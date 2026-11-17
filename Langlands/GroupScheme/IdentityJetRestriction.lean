import Langlands.GroupScheme.IdentityCotangentNaturality
import Langlands.RingTheory.Smooth.SectionJetHomogeneousLayers

/-! # Affine restriction of actual identity-jet quotients and layers -/

noncomputable section

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]

attribute [local instance] sectionAlgebra

/-- The semilinear augmentation-quotient restriction transported from the actual
identity-jet module sheaf. -/
def restriction (n : ℕ) {U V : S.affineOpens} (h : V.1 ≤ U.1) :
    Algebra.SectionJet.Quotient (augmentation G U) n →ₛₗ[(S.presheaf.map (homOfLE h).op).hom]
      Algebra.SectionJet.Quotient (augmentation G V) n where
  toFun x := sectionsEquiv G n V
    ((module G n).presheaf.map (homOfLE h).op ((sectionsEquiv G n U).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by simp only [map_smul, AlgebraicGeometry.Scheme.Modules.map_smul]

theorem sectionsEquiv_restrict (n : ℕ) {U V : S.affineOpens}
    (h : V.1 ≤ U.1) (x : Γ(module G n, U)) :
    restriction G n h (sectionsEquiv G n U x) =
      sectionsEquiv G n V ((module G n).presheaf.map (homOfLE h).op x) := by
  change sectionsEquiv G n V
    ((module G n).presheaf.map (homOfLE h).op
      ((sectionsEquiv G n U).symm (sectionsEquiv G n U x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Actual jet restriction sends a residue class to the class of the restricted
actual group function. -/
theorem restriction_mk (n : ℕ) {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    restriction G n h (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (IdentityCotangent.functionRestriction G h a) := by
  have hq :
      (sectionsEquiv G n U).symm (Ideal.Quotient.mk _ a) = (quotientMap G n).app U a :=
    (sectionsEquiv G n U).symm_apply_eq.mpr (sectionsEquiv_quotientMap G n U a).symm
  change sectionsEquiv G n V
    ((module G n).presheaf.map (homOfLE h).op
      ((sectionsEquiv G n U).symm (Ideal.Quotient.mk _ a))) = _
  rw [hq]
  have hnat := PresheafOfModules.naturality_apply (quotientMap G n).val (homOfLE h).op a
  exact (congrArg (sectionsEquiv G n V) hnat.symm).trans
    (sectionsEquiv_quotientMap G n V (IdentityCotangent.functionRestriction G h a))

/-- Restriction commutes with the actual successive augmentation quotient maps. -/
theorem restriction_truncate (n : ℕ) {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (x : Algebra.SectionJet.Quotient (augmentation G U) (n + 1)) :
    Algebra.SectionJet.truncate (augmentation G V) n (restriction G (n + 1) h x) =
      restriction G n h (Algebra.SectionJet.truncate (augmentation G U) n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [restriction_mk, Algebra.SectionJet.truncate_mk]

/-- Restricted functions that vanish at the actual identity still vanish there. -/
theorem augmentation_functionRestriction_eq_zero {U V : S.affineOpens} (h : V.1 ≤ U.1)
    {a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)} (ha : augmentation G U a = 0) :
    augmentation G V (IdentityCotangent.functionRestriction G h a) = 0 := by
  have hm : Ideal.Quotient.mk (RingHom.ker (augmentation G U) ^ (0 + 1)) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (by simpa only [Nat.zero_add, pow_one, RingHom.mem_ker] using ha)
  have hv := congrArg (restriction G 0 h) hm
  rw [restriction_mk, map_zero] at hv
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
  simpa only [Nat.zero_add, pow_one, RingHom.mem_ker] using hmem

/-- The induced semilinear restriction on the actual kernels of jet truncation. -/
def layerRestriction (n : ℕ) {U V : S.affineOpens} (h : V.1 ≤ U.1) :
    Algebra.SectionJet.Layer (augmentation G U) n →ₛₗ[(S.presheaf.map (homOfLE h).op).hom]
      Algebra.SectionJet.Layer (augmentation G V) n :=
  ((restriction G (n + 1) h).comp (Algebra.SectionJet.Layer (augmentation G U) n).subtype).codRestrict _
    (fun x => by
      change Algebra.SectionJet.truncate (augmentation G V) n
        (restriction G (n + 1) h x.val) = 0
      rw [restriction_truncate, show Algebra.SectionJet.truncate (augmentation G U) n x.val = 0
        from x.property, map_zero])

@[simp]
theorem layerRestriction_val (n : ℕ) {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (x : Algebra.SectionJet.Layer (augmentation G U) n) :
    (layerRestriction G n h x).val = restriction G (n + 1) h x.val := rfl

/-- On homogeneous coordinate values, actual layer restriction is residue-class
restriction of the evaluated actual group function. -/
theorem layerRestriction_homogeneousToLayer_val {σ : Type w} {U V : S.affineOpens}
    (h : V.1 ≤ U.1) (z : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (hz : ∀ i, augmentation G U (z i) = 0) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ Γ(S, U) (n + 1)) :
    (layerRestriction G n h (Algebra.SectionJet.Coordinates.homogeneousToLayer z hz n p)).val =
      Ideal.Quotient.mk _ (IdentityCotangent.functionRestriction G h (MvPolynomial.aeval z p.val)) := by
  rw [layerRestriction_val, Algebra.SectionJet.Coordinates.homogeneousToLayer_val, restriction_mk]

end Langlands.GroupScheme.IdentityJet
