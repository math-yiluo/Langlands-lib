/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.CategoryTheory.SequentialTelescopeMono
import WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing

/-!
# Localization internal Hom and the multiplication tower

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Internal RHom from the coefficient localization vanishes exactly when a derived limit
of the multiplication tower vanishes, on the slice site.

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (auxiliary; not a blueprint node).

Proof:
1. The coefficient localization is the sequential colimit of repeated multiplication
   on the unit sheaf. The countable free telescope map is monic by the sequential
   telescope theorem in a Grothendieck abelian category. The colimit universal
   property identifies its cokernel with the coefficient localization.
2. Embed this short exact sequence in degree zero and apply the distinguished-triangle
   construction. Contravariant derived internal Hom gives a distinguished triangle
   whose first object is the internal Hom in the statement.
3. The free coefficient telescope duality calculation identifies the middle map with
   the Roos endomorphism on the product of restricted copies of K, including the
   specified derived local-section multiplication.
4. In a distinguished triangle the first object vanishes exactly when the middle
   map is invertible. Apply this both to the Hom triangle and to the triangle in the
   supplied derived-limit witness. Conjugation by the product isomorphism preserves
   invertibility. No choice or uniqueness theorem for derived limits is needed. -/
theorem localHom_zero_iff_multiplicationTower_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)]
    (T : DerivedCategory (ringedSiteModules.{u} ((localCoefficientRings R).over U)))
    (_hT : IsDerivedLimit
      (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
      (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) T) :
    IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization R U f)),
        (localCoefficientDerivedRestriction R U).obj K)) ↔ IsZero T := by
  classical
  let A := ringedSiteModules.{u} ((localCoefficientRings R).over U)
  -- Keep the opposite structures local to this proof, for both slice presentations.
  let : HasShift (DerivedCategory A)ᵒᵖ ℤ :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory A)ᵒᵖ n).Additive :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let : Pretriangulated (DerivedCategory A)ᵒᵖ :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let A' := SheafOfModules.{u}
    ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))
  let : HasShift (DerivedCategory A')ᵒᵖ ℤ :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory A')ᵒᵖ n).Additive :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let : Pretriangulated (DerivedCategory A')ᵒᵖ :=
    open scoped CategoryTheory.Pretriangulated.Opposite in inferInstance
  let E := Functor.ofSequence
    (X := fun _ : ℕ ↦ SheafOfModules.unit ((localCoefficientRings R).over U))
    (fun _ ↦ localSectionMultiplication R U f _)
  let B : Cofan E.obj := Cofan.mk (localCoefficientFree R U) (fun n ↦ Sigma.ι _ n)
  have hB : IsColimit B := coproductIsCoproduct _
  let d := localCoefficientTelescopeMap R U f
  have hd (n : ℕ) : B.inj n ≫ d =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1) := by
    change Sigma.ι _ n ≫ d = Sigma.ι _ n -
      E.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι _ (n + 1)
    rw [show E.map (homOfLE (Nat.le_succ n)) = localSectionMultiplication R U f _ from
      Functor.ofSequence_map_homOfLE_succ _ n]
    exact Sigma.ι_comp_desc _ n
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink _
  have : Mono d := sequentialTelescope_mono E B hB d hd
  obtain ⟨q, hz, hs⟩ := telescope_shortExact E B hB d hd
  let F := HomologicalComplex.single A (.up ℤ) 0
  have hS := hs.map_of_exact F
  let D := DerivedCategory.triangleOfSES hS
  have hD := DerivedCategory.triangleOfSES_distinguished hS
  let L := (localCoefficientDerivedRestriction R U).obj K
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj L
  obtain ⟨hshift, htri⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 L
  let := hshift
  let := htri
  let Dop := (Pretriangulated.triangleOpEquivalence _).functor.obj (op D)
  have hDop : Dop ∈ distTriang _ := by
    apply (Pretriangulated.Opposite.mem_distinguishedTriangles_iff' _).mpr
    exact ⟨D, hD, ⟨Iso.refl _⟩⟩
  have hleft := Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (H.mapTriangle.obj Dop) (H.map_distinguished Dop hDop)
  obtain ⟨e, he⟩ := localCoefficientTelescope_rhom_product J R U f K
  have hmiddle : IsIso (H.map ((DerivedCategory.singleFunctor A 0).map d).op) ↔
      IsIso (towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ L) (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) := by
    constructor
    · intro hi
      let := hi
      have : IsIso (H.map ((DerivedCategory.singleFunctor A 0).map d).op ≫ e.hom) :=
        inferInstance
      rw [he] at this
      exact (isIso_comp_left_iff e.hom _).mp this
    · intro hi
      let := hi
      have : IsIso (e.hom ≫ towerTransitionEndomorphism
          (K := fun _ : ℕ ↦ L) (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) :=
        inferInstance
      rw [← he] at this
      exact (isIso_comp_right_iff _ e.hom).mp this
  obtain ⟨p, δ, hT⟩ := _hT
  have hright := Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (Pretriangulated.Triangle.mk p
      (towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ L) (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) δ) hT
  exact hleft.trans (hmiddle.trans hright.symm)

end CategoryTheory
