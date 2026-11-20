import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.HomScheme.SplitTorusGroupExtension

/-! # Adic detection of homomorphisms from a diagonalizable group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

namespace Langlands.GroupScheme.HomScheme.Adic

open Diagonalizable TorsionDensity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Diagonalizable homomorphisms into a separated group are detected by their
reductions over any adically separated base ring. -/
def DiagonalizableAdicInjectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) [IsHausdorff I A]
    (M : Type u) [AddCommGroup M] (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsSeparated G.X.hom],
    Function.Injective (System.restrict I (groupScheme (CommRingCat.of A) M).toGrp G)

theorem diagonalizableAdicInjectivity : DiagonalizableAdicInjectivityStatement.{u} := by
  intro A _ I _ M _ G _ f g h
  let C := CommRingCat.of (AddMonoidAlgebra A M)
  let j := equalizer.ι f.hom.hom g.hom.hom
  let jLeft : (equalizer f.hom.hom g.hom.hom).left ⟶ Spec C := j.left
  have : IsClosedImmersion jLeft := inferInstanceAs (IsClosedImmersion j.left)
  have hz (a : Γ(Spec C, ⊤)) (ha : jLeft.appTop a = 0) :
      ∀ n, AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (I ^ (n + 1)))
        ((Scheme.ΓSpecIso C).hom a) = 0 := by
    intro n
    let φ := Ideal.Quotient.mk (I ^ (n + 1))
    let q := Spec.map (CommRingCat.ofHom φ)
    let c := coefficientProjectionOver M φ
    have hn : (baseChange q).map f = (baseChange q).map g :=
      congrArg (fun s => s.hom n) h
    have he : c ≫ f.hom.hom = c ≫ g.hom.hom := by
      apply Over.OverMorphism.ext
      change coefficientProjection M φ ≫ f.hom.hom.left =
        coefficientProjection M φ ≫ g.hom.hom.left
      rw [← baseChangeMap_project φ f, ← baseChangeMap_project φ g, hn]
    let liftLeft : Spec (CommRingCat.of (AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)) ⟶
        (equalizer f.hom.hom g.hom.hom).left := (equalizer.lift c he).left
    have hfac : liftLeft ≫ jLeft = coefficientProjection M φ :=
      congrArg (fun h => h.left) (equalizer.lift_ι c he)
    have hk : (coefficientProjection M φ).appTop a = 0 := by
      rw [← hfac, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simpa only [map_zero] using congrArg (fun x => liftLeft.appTop x) ha
    let D := CommRingCat.of (AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)
    let m : C ⟶ D := CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom M φ)
    have hi := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality m) a
    change (Scheme.ΓSpecIso D).hom ((coefficientProjection M φ).appTop a) =
      AddMonoidAlgebra.mapRingHom M φ ((Scheme.ΓSpecIso C).hom a) at hi
    rw [hk, map_zero] at hi
    exact hi.symm
  have hj : Function.Injective jLeft.appTop := by
    apply (RingHom.injective_iff_ker_eq_bot jLeft.appTop.hom).mpr
    apply eq_bot_iff.mpr
    intro a ha
    apply Ideal.mem_bot.mpr
    apply (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso C).hom a = (Scheme.ΓSpecIso C).hom 0
    rw [map_zero]
    let z : AddMonoidAlgebra A M := (Scheme.ΓSpecIso C).hom a
    change z = 0
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    apply congrFun (IsHausdorff.StrictMono.funext' I strictMono_add_one
      (f := fun _ : Unit => z.coeff m)
      (g := fun _ : Unit => (0 : A)) ?_) ()
    intro n _
    have hc := congrArg (fun x : AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M => x.coeff m)
      (hz a (RingHom.mem_ker.mp ha) n)
    simpa only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, map_zero, z] using hc
  have : IsIso jLeft := IsClosedImmersion.isIso_of_injective_of_isAffine hj
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi jLeft).mp
  exact congrArg (fun h => h.left) (equalizer.condition f.hom.hom g.hom.hom)

/-- The detection result also applies to any isomorphic source. -/
theorem diagonalizableAdicInjectivity_of_iso
    {A : Type u} [CommRing A] (I : Ideal A) [IsHausdorff I A]
    {M : Type u} [AddCommGroup M] {H G : GroupScheme (Spec (CommRingCat.of A))}
    [IsSeparated G.X.hom] (e : (groupScheme (CommRingCat.of A) M).toGrp ≅ H) :
    Function.Injective (System.restrict I H G) := by
  apply (System.restrict_injective_iff I H G).mpr
  intro f g h
  apply (cancel_epi e.hom).mp
  apply (System.restrict_injective_iff I _ G).mp
    (diagonalizableAdicInjectivity A I M G)
  intro n
  simp only [Functor.map_comp, h n]

end Langlands.GroupScheme.HomScheme.Adic
