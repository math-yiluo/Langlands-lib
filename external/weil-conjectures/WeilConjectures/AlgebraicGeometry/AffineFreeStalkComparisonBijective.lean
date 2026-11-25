/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.AffineRegularStalkComparisonBijective

/-! # Bijectivity of the explicit finite free stalk comparison

Source: Stacks Project, Tags 01HV, 01IB, 01C6 and 0098.
(blueprint: lem-sc-affine-free-stalk-comparison-bijective).
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem coordinate_reconstruction (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    (∑ p, affineCoordinateProjection X U n p ≫ affineCoordinateInclusion X U n p) =
      𝟙 (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U)))) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (∑ p, affineCoordinateProjection X U n p ≫
    affineCoordinateInclusion X U n p).hom v = v
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply (ULift.moduleEquiv (R := Γ(X, U)) (M := Fin n → Γ(X, U))).injective
  rw [map_sum]
  change (∑ p, Pi.single p (v.down p)) = v.down
  exact LinearMap.sum_single_apply (fun _ : Fin n ↦ Γ(X, U)) v.down

private theorem stalk_projection_ext (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hU : IsAffineOpen U) (n : ℕ)
    (v w : (affineFreeStalkFunctor X x U hU).obj
      (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U)))))
    (h : ∀ p, (affineFreeStalkFunctor X x U hU).map
      (affineCoordinateProjection X U n p) v =
        (affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p) w) :
    v = w := by
  let H := affineFreeStalkFunctor X x U hU
  have he (z : H.obj (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))))) :
      z = ∑ p, H.map (affineCoordinateInclusion X U n p)
        (H.map (affineCoordinateProjection X U n p) z) := by
    have hh := congrArg (fun f ↦ (H.map f).hom z) (coordinate_reconstruction X U n)
    simpa only [H.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, H.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, H.map_id, ModuleCat.hom_id,
      LinearMap.id_apply] using hh.symm
  rw [he v, he w]
  apply Finset.sum_congr rfl
  intro p _
  rw [h p]

private theorem stalk_projection_basis (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) (n : ℕ) (p q : Fin n) :
    (affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p)
      (affineFreeBasisGerm X x U hxU hU n q) =
        if p = q then affineRegularStalkGerm X x U hxU hU else 0 := by
  let H := affineFreeStalkFunctor X x U hU
  have hc : affineCoordinateInclusion X U n q ≫ affineCoordinateProjection X U n p =
      if p = q then 𝟙 _ else 0 := by
    split_ifs with h
    · subst p
      ext
      simp [affineCoordinateInclusion, affineCoordinateProjection]
    · ext
      simp [affineCoordinateInclusion, affineCoordinateProjection, h]
  change H.map (affineCoordinateProjection X U n p)
    (H.map (affineCoordinateInclusion X U n q) _) = _
  rw [← ModuleCat.comp_apply, ← H.map_comp, hc]
  split_ifs <;> simp

private theorem stalk_projection_comparison (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) (n : ℕ) (p : Fin n)
    (v : ULift.{0} (Fin n → X.presheaf.stalk x)) :
    (affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p)
      (affineFreeStalkComparison X x U hxU hU n v) =
        affineRegularStalkComparison X x U hxU hU (v.down p) := by
  classical
  change ((affineFreeStalkFunctor X x U hU).map
    (affineCoordinateProjection X U n p)).hom
      (∑ q, v.down q • affineFreeBasisGerm X x U hxU hU n q) = _
  rw [map_sum]
  simp only [map_smul, stalk_projection_basis]
  change (∑ q, v.down q • (if p = q then _ else 0)) =
    v.down p • affineRegularStalkGerm X x U hxU hU
  simp

/-- The linear combination map of actual standard basis germs is bijective.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (7), and Tags 01IB, 01C6, 0098.
(blueprint: lem-sc-affine-free-stalk-comparison-bijective).

Proof: On Spec Gamma(X,U), the tilde stalk localization sends each standard basis
vector to its germ. Localization of the finite coordinate module is the finite
coordinate module over the localized ring: fractions are taken coordinatewise,
and finitely many denominators admit a common product. Transport this identification
along the affine chart and the inverse slice-site equivalence. The regular-module
identification used in affineRegularSheafIso takes 1 to the unit section, so the
transported basis vectors are precisely affineFreeBasisGerm. Neighbourhoods contained
in U are cofinal among neighbourhoods of x. Ordinary open direct image consequently
has the same stalk and scalar action. The resulting coordinate map is exactly
sum_p v_p times the p-th basis germ, namely affineFreeStalkComparison. Projection
germs provide its inverse, proving both injectivity and surjectivity. For n = 0,
the source and target are zero modules and the empty sum is their unique map. -/
theorem affineFreeStalkComparison_bijective
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (n : ℕ) : Function.Bijective (affineFreeStalkComparison X x U hxU hU n)  := by
  classical
  have hregular := affineRegularStalkComparison_bijective X x U hxU hU
  constructor
  · intro v w h
    apply (ULift.moduleEquiv (R := X.presheaf.stalk x)
      (M := Fin n → X.presheaf.stalk x)).injective
    ext p
    apply hregular.1
    have hh := congrArg (fun z ↦ (affineFreeStalkFunctor X x U hU).map
      (affineCoordinateProjection X U n p) z) h
    change (affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p)
      (affineFreeStalkComparison X x U hxU hU n v) =
        (affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p)
          (affineFreeStalkComparison X x U hxU hU n w) at hh
    rw [stalk_projection_comparison, stalk_projection_comparison] at hh
    exact hh
  · intro z
    have hz (p : Fin n) := hregular.2
      ((affineFreeStalkFunctor X x U hU).map (affineCoordinateProjection X U n p) z)
    choose v hv using hz
    refine ⟨ULift.up v, ?_⟩
    apply stalk_projection_ext X x U hU n
    intro p
    rw [stalk_projection_comparison]
    exact hv p

end AlgebraicGeometry.Scheme
