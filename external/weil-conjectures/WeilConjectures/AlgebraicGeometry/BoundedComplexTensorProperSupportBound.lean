/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Data.Int.Interval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # A proper support bound for tensor with a bounded complex

Source: Stacks Project, Tag 0DJQ, verification of the support hypothesis of 08EV;
Tags 01AT (support), 09MQ (4) and 03GN (descent along a proper surjection).
(blueprint: lem-pc-bounded-complex-tensor-proper-support-bound).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem stalk_subsingleton_of_isZero {X : Scheme.{u}}
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : IsZero F) (x : X) : Subsingleton (Modules.presheaf F |>.stalk x) := by
  have h₁ := (SheafOfModules.forget (moduleRings X.toRingedSpace)).map_isZero hF
  have h₂ := (PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj).map_isZero h₁
  exact AddCommGrpCat.subsingleton_of_isZero
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_isZero h₂)

private theorem module_restriction_zero
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hM : {x : X | ¬ Subsingleton ((Modules.presheaf M).stalk x)} ⊆ (Z : Set X)) :
    IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      Z.compl).obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext V z
  change z = 0
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M)
  intro x hx
  have hxZ : x ∉ Z := leOfHom V.unop.hom hx
  have hs : Subsingleton ((Modules.presheaf M).stalk x) := by
    by_contra hn
    exact hxZ (hM hn)
  exact hs.elim _ _

private theorem derived_tensor_isZero_of_right (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E F : schemeDerivedCategory X) (hF : IsZero F) : IsZero (E ⊗ F) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have := schemeModule_hasFunctorialFlatResolution X
  exact (tensorLeft E).map_isZero hF

set_option synthInstance.maxSize 2048 in
private theorem tensor_support_subset (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (Z : TopologicalSpace.Closeds X)
    (hG : ∀ n : ℤ,
      {x : X | ¬ Subsingleton ((Modules.presheaf (G.X n)).stalk x)} ⊆ (Z : Set X)) :
    ∀ i : ℤ,
      {x : X | ¬ Subsingleton ((Modules.presheaf
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            (E ⊗ DerivedCategory.Q.obj G))).stalk x)} ⊆ (Z : Set X) := by
  let U : X.Opens := Z.compl
  let : HasDerivedCategory (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) := HasDerivedCategory.standard _
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
  have : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  let RG := (R.mapHomologicalComplex (.up ℤ)).obj G
  have hRG (n : ℤ) : IsZero (RG.X n) := by
    exact (Modules.overEquiv U).functor.map_isZero (module_restriction_zero X Z
      (G.X n) (hG n))
  have hRGzero : IsZero RG := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.Hom.ext
    funext n
    exact (hRG n).eq_of_src _ _
  have hQG : IsZero (R.mapDerivedCategory.obj (DerivedCategory.Q.obj G)) :=
    (DerivedCategory.Q.map_isZero hRGzero).of_iso (R.mapDerivedCategoryFactors.app G)
  obtain ⟨e⟩ := derivedTensor_openRestriction_iso_universes X U E (DerivedCategory.Q.obj G)
  have hRT : IsZero (R.mapDerivedCategory.obj (E ⊗ DerivedCategory.Q.obj G)) :=
    (derived_tensor_isZero_of_right U.toScheme _ _ hQG).of_iso e
  intro i x hx
  by_contra hxZ
  let y : U.toScheme := ⟨x, hxZ⟩
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
      (E ⊗ DerivedCategory.Q.obj G)
  have hRH : IsZero (R.obj H) :=
    ((DerivedCategory.homologyFunctor _ i).map_isZero hRT).of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso i).app _)
  have hs : Subsingleton ((Modules.presheaf (R.obj H)).stalk y) :=
    stalk_subsingleton_of_isZero _ hRH y
  let eH : R.obj H ≅ (Modules.restrictFunctor U.ι).obj H :=
    (Modules.overFunctorEquiv U).app H
  let T := Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let eS := T.mapIso eH ≪≫ (Modules.restrictStalkNatIso U.ι y).app H
  exact hx ((Equiv.subsingleton_congr
    (Equiv.ofBijective eS.hom (ConcreteCategory.bijective_of_isIso eS.hom))).mp hs)

/-- Tensoring any derived object with a bounded complex with proper termwise supports
puts all cohomology supports inside one closed subset proper over the base. No perfection,
coherence, relative flatness, Noetherian assumption or cohomology boundedness is needed.
This asserts containment; the cohomology supports need not themselves be closed.
Source: Stacks Project, Tag 0DJQ, support verification for 08EV; Tags 01AT, 0CYR, 08DX.

Proof:
1. If [c,d] bounds G, let Z be the union of the supports of G^n for c <= n <= d.
   Terms outside the interval are zero, with empty support. This is a finite union of
   closed subsets. If c > d the entire complex is zero and the union is empty.
2. Apply isClosedSubsetProperOver_union_preimage (Stacks 0CYR) to this finite family.
   This packages the proper-surjection descent argument for the reduced union.
3. On the open complement of Z every term of G has zero stalks, hence is the zero sheaf.
   Therefore the restricted complex G is zero. Restriction to an open commutes with
   the K-flat derived tensor, and tensor with zero is zero, so E tensor^L G restricts
   to zero there, for arbitrary E. Exactness of open restriction shows every cohomology
   sheaf is zero on this complement. Its nonzero-stalk locus is consequently contained
   in Z, as asserted. For an empty Z the same proof gives zero cohomology everywhere.
(blueprint: lem-pc-bounded-complex-tensor-proper-support-bound). -/
theorem boundedComplex_tensor_proper_support_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGproper : ∀ n : ℤ, Modules.HasSupportProperOver f (G.X n)) :
    ∃ Z : TopologicalSpace.Closeds X, IsClosedSubsetProperOver f Z ∧
      ∀ i : ℤ,
        {x : X | ¬ Subsingleton
          ((Modules.presheaf (X := X)
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
                (E ⊗ DerivedCategory.Q.obj G))).stalk x)} ⊆ (Z : Set X) := by
  classical
  obtain ⟨a, b, hab⟩ := hGb
  choose Z hZ hproper using hGproper
  let I := {n : ℤ // n ∈ Finset.Icc a b}
  let e := Fintype.equivFin I
  let W : Fin (Fintype.card I) → TopologicalSpace.Closeds X :=
    fun i ↦ Z (e.symm i).val
  let T : TopologicalSpace.Closeds X := ⨆ i, W i
  have hT : IsClosedSubsetProperOver f T :=
    (isClosedSubsetProperOver_union_preimage f).1 _ W
      (fun i ↦ hproper (e.symm i).val)
  have hsupport (n : ℤ) :
      {x : X | ¬ Subsingleton ((Modules.presheaf (G.X n)).stalk x)} ⊆ (T : Set X) := by
    intro x hx
    by_cases hn : n ∈ Finset.Icc a b
    · have hle : Z n ≤ T := by
        have hi : W (e ⟨n, hn⟩) ≤ T := le_iSup W (e ⟨n, hn⟩)
        simpa only [W, Equiv.symm_apply_apply] using hi
      exact hle (by
        change x ∈ (Z n : Set X)
        rwa [hZ n])
    · have hz : IsZero (G.X n) := hab n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn)
      exact (hx (stalk_subsingleton_of_isZero (G.X n) hz x)).elim
  exact ⟨T, hT, tensor_support_subset X E G T hsupport⟩

end AlgebraicGeometry.Scheme
