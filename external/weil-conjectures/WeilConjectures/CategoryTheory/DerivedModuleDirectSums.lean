/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Direct sums of module complexes in the derived category

Source: Stacks Project, Injectives, Lemma 07D9 (clauses (1)-(2)) (blueprint:
lem-pc-derived-module-direct-sums).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private lemma coproduct_homotopy
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C]
    (K : I → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f g : ∐ K ⟶ L) (h : ∀ i, Homotopy (Sigma.ι K i ≫ f) (Sigma.ι K i ≫ g)) :
    Nonempty (Homotopy f g) := by
  let hc (n : ℤ) := isColimitOfPreserves
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n) (coproductIsCoproduct K)
  let t (n m : ℤ) : Cocone
      (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) :=
    { pt := L.X m
      ι := { app := fun i ↦ (h i.as).hom n m
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := Discrete.eq_of_hom f
               simp } }
  let a (n m : ℤ) : (∐ K).X n ⟶ L.X m :=
    (hc n).desc (t n m)
  have ha (i : I) (n m : ℤ) : (Sigma.ι K i).f n ≫ a n m = (h i).hom n m := by
    exact (hc n).fac (t n m) ⟨i⟩
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    rintro ⟨i⟩
    simpa only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      ha, comp_zero] using (h i).zero n m hnm
  · intro n
    apply (hc n).hom_ext
    rintro ⟨i⟩
    change (Sigma.ι K i).f n ≫ f.f n = _
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      Preadditive.comp_add, dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι K i).comm_assoc, ha, ← Category.assoc, ha]
    exact (h i).comm n

private lemma derived_map_surjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).surjective
    (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_mono (e.inv.app L)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, hg]
  simp [e]

private lemma derived_map_homotopy
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} [L.IsKInjective] (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

/-- (blueprint: lem-pc-derived-module-direct-sums) Let `R` be a ring and let
`D(R)` be the derived category of `R`-modules. For a family of cochain complexes
`K` indexed by `I`, the image under `DerivedCategory.Q` of the termwise
coproduct complex, together with the images of its coprojections, is a
coproduct of the `Q.obj (K i)` in `D(R)`. Following Stacks Project,
Injectives, Lemma 07D9: first form the complex degreewise by direct sums,
with differentials and inclusions induced from the summands. Next use the
Grothendieck abelian property of modules and exactness of filtered colimits
to show direct sums are exact; hence cohomology and quasi-isomorphisms
commute with these sums. Finally resolve an arbitrary target by a
K-injective complex, identify derived morphisms into it with homotopy
morphisms, and apply the degreewise coproduct property for chain maps and
homotopies to obtain the universal property in the derived category. -/
theorem derivedModuleDirectSums (R : Type u) [Ring R]
    [HasDerivedCategory (ModuleCat.{max u v} R)] (I : Type v)
    (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i => DerivedCategory.Q.map (Sigma.ι K i)))) := by
  classical
  let : IsGrothendieckAbelian.{max u v} (ModuleCat.{max u v} R) :=
    IsGrothendieckAbelian.of_equivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} R ≃+* R)).symm
  let : Abelian.HasKInjectiveResolutions (ModuleCat.{max u v} R) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max u v}
  have hu (X : DerivedCategory (ModuleCat.{max u v} R))
      (a : ∀ i, DerivedCategory.Q.obj (K i) ⟶ X) :
      ∃! d : DerivedCategory.Q.obj (∐ K) ⟶ X,
        ∀ i, DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨L, _, r, _, _⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective
        (DerivedCategory.Q.objPreimage X)
    let e : X ≅ DerivedCategory.Q.obj L :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map r)
    choose f hf using fun i ↦ derived_map_surjective (K i) L (a i ≫ e.hom)
    let d := DerivedCategory.Q.map (Sigma.desc f) ≫ e.inv
    have hd (i : I) : DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
      dsimp [d]
      rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_comp_desc, hf]
      simp
    refine ⟨d, hd, ?_⟩
    intro m hm
    apply (cancel_mono e.hom).1
    obtain ⟨g, hg⟩ := derived_map_surjective (∐ K) L (m ≫ e.hom)
    have he (i : I) :
        DerivedCategory.Q.map (Sigma.ι K i ≫ g) = DerivedCategory.Q.map (f i) := by
      rw [Functor.map_comp, hg, ← Category.assoc, hm, hf]
    have hhom := coproduct_homotopy K g (Sigma.desc f) (fun i ↦
      (derived_map_homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f)
        (by simpa only [Sigma.ι_comp_desc] using he i)).some)
    rw [← hg, DerivedCategory.Q_map_eq_of_homotopy _ hhom.some]
    simp [d]
  refine ⟨Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose) ?_ ?_⟩
  · intro t i
    exact (hu t.pt t.inj).choose_spec.1 i
  · intro t m hm
    exact (hu t.pt t.inj).choose_spec.2 m hm

end CategoryTheory
