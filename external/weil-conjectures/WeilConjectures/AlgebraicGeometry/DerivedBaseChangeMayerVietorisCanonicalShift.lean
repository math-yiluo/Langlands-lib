/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PinnedBaseChangeMateShifts
import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! Canonical compatibility for relative Mayer--Vietoris.
Source: Stacks Project, Tags 08BV, 08HY and 0DJ9. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The pinned base-change comparison is natural and shift-compatible, with the
right-derived direct-image shifts and their unique adjoint pullback shifts.
This assertion has no cover, SES or connecting morphism.
Source: Stacks Tag 08HY, counit construction; Mathlib Shift.Adjunction.
(blueprint: lem-pc-rf-mv-canonical-base-change-shift).

Proof: derive the termwise tensor-pullback composition comparison using K-flat
resolutions. On such resolutions it is the associative tensor comparison, which
commutes with translation, including the differential sign. The left-derived
universal property extends this identity to all objects. Its right-adjoint mate
is compatible with the existing right-derived direct-image shift: use the
right-derived unit computation on K-injectives and uniqueness of the shift mate.
In the definition of schemeDerivedBaseChangeMap the composition comparisons and
pinned counits are exactly these comparisons and counits. Their naturality
identifies the comparison at a morphism a with the shifted comparison at K.
The units and counits commute with shifts by mvCanonicalPullbackShift_compatible;
transposition commutes with shifts by mvCanonicalHomEquiv_shift. Compose these
identities to obtain the boundary-shaped naturality equation with a, and finally
postcompose by Rf'(ψ)[n]. Naturality of the right-derived shift moves this last
factor across its commutation isomorphism, giving the stated formula.
The proof does not use cartesianness, quasi-coherence or a cover. -/
theorem mvCanonicalBaseChange_shift
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (A K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K') (n : ℤ) (a : A ⟶ K⟦n⟧) :
    letI := mvCanonicalPullbackShift g'
    let csF := mvCanonicalSourceShift f g
    let csG := mvCanonicalTargetShift f'
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map a ≫
        (letI := csF;
          (schemeDerivedDirectImage f ⋙ derivedPullback g).commShiftIso n).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' h K ≫
          (schemeDerivedDirectImage f').map ψ)⟦n⟧' =
      schemeDerivedBaseChangeMap f f' g g' h A ≫
        (schemeDerivedDirectImage f').map
          ((derivedPullback g').map a ≫
            ((derivedPullback g').commShiftIso n).hom.app K ≫ ψ⟦n⟧') ≫
        (letI := csG; (schemeDerivedDirectImage f').commShiftIso n).hom.app K' := by
  classical
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive :=
    fun k ↦ (Classical.choose exists_derivedPullbackComposition.{u, w}) k
  obtain ⟨s, hs⟩ := exists_pinned_pullback_counit_shifts.{u, w}
  have heq {Y Z : Scheme.{u}} (k : Y ⟶ Z) : s k = mvCanonicalPullbackShift k := by
    let adj := mvDerivedPullbackAdjunction k
    have h₁ : letI := s k; adj.CommShift ℤ := pinnedDerivedAdjunction_commShift s hs k
    have h₂ : letI := mvCanonicalPullbackShift k; adj.CommShift ℤ :=
      mvCanonicalPullbackShift_compatible k
    have hiso (m : ℤ) : (s k).commShiftIso m = (mvCanonicalPullbackShift k).commShiftIso m := by
      apply Adjunction.CommShift.compatibilityUnit_unique_left adj _ _
        ((schemeDerivedDirectImage k).commShiftIso m)
      · let := s k
        let := h₁
        exact fun E ↦ adj.shift_unit_app m E
      · let := mvCanonicalPullbackShift k
        let := h₂
        exact fun E ↦ adj.shift_unit_app m E
    generalize s k = v at hiso ⊢
    generalize mvCanonicalPullbackShift k = v' at hiso ⊢
    cases v
    cases v'
    congr 1
    funext m
    exact hiso m
  obtain ⟨τ, hτ, hτs⟩ := exists_pinned_base_change_mate_shifts s hs f g g' f' h
  rw [heq g, heq g'] at hτs
  let := mvCanonicalPullbackShift g
  let := mvCanonicalPullbackShift g'
  have := hτs
  have hn := τ.naturality a
  have ht := NatTrans.shift_app_comm τ n K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at ht
  simp only [Functor.comp_map] at hn
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  rw [← hτ K, ← hτ A]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc]
  rw [reassoc_of% ht, reassoc_of% hn, ← Functor.commShiftIso_hom_naturality]


end AlgebraicGeometry
