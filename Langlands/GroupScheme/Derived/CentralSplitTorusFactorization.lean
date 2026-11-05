import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Factorization through the supplied derived maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section DerivedFactor

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {S S_D : CommGroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {i : S.toGrp ⟶ G} {j : S_D.toGrp ⟶ D} {e : S_D ⟶ S}

/-- Every derived-valued endomorphism of the ambient split torus factors through
the supplied compatible derived maximal split torus. -/
theorem IsDerivedSubgroup.exists_factor_splitTorusEnd
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (q : S ⟶ S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U) :
    ∃ f : S ⟶ S_D, f ≫ e = q := by
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  have hqr : SubgroupFunctor.range (CommGroupScheme.groupHom q ≫ i) ≤
      derivedSubgroup G := by
    rintro U _ ⟨x, rfl⟩
    exact hq U x
  let b : S.toGrp ⟶ D := hd.isRepresentedBy.factorHom
    (CommGroupScheme.groupHom q ≫ i) hqr
  have hb : b ≫ d = CommGroupScheme.groupHom q ≫ i :=
    hd.isRepresentedBy.factorHom_comp _ _
  have hbj : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X)
      (y : U ⟶ S_D.X), Commute (x ≫ b.hom.hom) (y ≫ j.hom.hom) := by
    intro U x y
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono d.hom.hom).mp
    have hbx : (x ≫ b.hom.hom) ≫ d.hom.hom =
        (x ≫ (CommGroupScheme.groupHom q).hom.hom) ≫ i.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => x ≫ z.hom.hom) hb
    have hjy : (y ≫ j.hom.hom) ≫ d.hom.hom =
        (y ≫ (CommGroupScheme.groupHom e).hom.hom) ≫ i.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => y ≫ z.hom.hom) he
    rw [MonObj.mul_comp, MonObj.mul_comp, hbx, hjy,
      ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  obtain ⟨f, hf⟩ := hj.exists_factor_of_commute hi.1 b hbj
  refine ⟨Additive.ofMul f, ?_⟩
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  have hcomp : (f ≫ CommGroupScheme.groupHom e) ≫ i =
      CommGroupScheme.groupHom q ≫ i := by
    rw [Category.assoc, ← he, ← Category.assoc, hf, hb]
  exact congrArg (fun z => z.hom.hom) hcomp

/-- A chosen factor of a derived-valued split-torus endomorphism through the
supplied compatible derived maximal split torus. -/
def IsDerivedSubgroup.splitTorusEndFactor
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (q : S ⟶ S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U) :
    S ⟶ S_D :=
  Classical.choose (hd.exists_factor_splitTorusEnd hi hj he q hq)

/-- The chosen factor recovers the original endomorphism after inclusion. -/
theorem IsDerivedSubgroup.splitTorusEndFactor_comp
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (q : S ⟶ S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U) :
    hd.splitTorusEndFactor hi hj he q hq ≫ e = q :=
  Classical.choose_spec (hd.exists_factor_splitTorusEnd hi hj he q hq)

end DerivedFactor

end Langlands.GroupScheme
