import Langlands.Representation.Plancherel.RationalCharacterHaar

/-! # Actual unitary unramified characters and kernel-scaled Haar measures under scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]

local instance rationalUnitaryCharacterIso_sourceTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance rationalUnitaryCharacterIso_targetTopology :
    TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X

/-- Actual unitary unramified character transport through a group-scheme
isomorphism. The norm families on both sides remain the actual rational ones. -/
def rationalUnitaryCharacterIso (e : G ≅ H) :
    unitaryUnramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul) ≃ₜ*
      unitaryUnramifiedCharacters (fun χ => (rationalNormCharacters H χ).toMul) where
  toFun := rationalUnitaryUnramifiedCharacterRestrict e.inv
  invFun := rationalUnitaryUnramifiedCharacterRestrict e.hom
  left_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    change χ.val ((g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = χ.val g
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro h
    change χ.val ((h ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) = χ.val h
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  map_mul' χ ψ := map_mul (rationalUnitaryUnramifiedCharacterRestrict e.inv) χ ψ
  continuous_toFun := (rationalUnitaryUnramifiedCharacterRestrict e.inv).continuous
  continuous_invFun := (rationalUnitaryUnramifiedCharacterRestrict e.hom).continuous

@[simp]
theorem rationalUnitaryCharacterIso_apply (e : G ≅ H)
    (χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (h : rationalPoints H) :
    (rationalUnitaryCharacterIso e χ).val h = χ.val (rationalPoints.map e.inv h) := rfl

section Restriction

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (e : G ≅ H)

local instance rationalUnitaryCharacterIso_restrictionTopology :
    TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology F T.X

/-- Transport commutes with restriction to the same affine commutative source. -/
theorem rationalUnitaryCharacterIso_restrict
    (χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalUnitaryUnramifiedCharacterRestrict (s ≫ e.hom) (rationalUnitaryCharacterIso e χ) =
      rationalUnitaryUnramifiedCharacterRestrict s χ := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro t
  change χ.val ((t ≫ (s ≫ e.hom).hom.hom) ≫ e.inv.hom.hom) = χ.val (t ≫ s.hom.hom)
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Category.comp_id]

/-- The restriction kernels correspond, giving equality of their orders whenever they
are finite. -/
theorem rationalUnitaryCharacterIso_map_restriction_ker :
    (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker.map
        (rationalUnitaryCharacterIso e).toMonoidHom =
      (rationalUnitaryUnramifiedCharacterRestrict (s ≫ e.hom)).toMonoidHom.ker := by
  ext χ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    change rationalUnitaryUnramifiedCharacterRestrict (s ≫ e.hom)
      (rationalUnitaryCharacterIso e ψ) = 1
    rw [rationalUnitaryCharacterIso_restrict]
    exact hψ
  · intro hχ
    refine ⟨(rationalUnitaryCharacterIso e).symm χ, ?_,
      (rationalUnitaryCharacterIso e).apply_symm_apply χ⟩
    change rationalUnitaryUnramifiedCharacterRestrict s
      ((rationalUnitaryCharacterIso e).symm χ) = 1
    rw [← rationalUnitaryCharacterIso_restrict s e,
      (rationalUnitaryCharacterIso e).apply_symm_apply]
    exact hχ

theorem rationalUnitaryCharacterIso_restriction_ker_card :
    Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker =
      Nat.card (rationalUnitaryUnramifiedCharacterRestrict (s ≫ e.hom)).toMonoidHom.ker := by
  let E := ((rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker.equivMapOfInjective
    (rationalUnitaryCharacterIso e).toMonoidHom (rationalUnitaryCharacterIso e).injective).trans
      (MulEquiv.subgroupCongr (rationalUnitaryCharacterIso_map_restriction_ker s e))
  exact Nat.card_congr E.toEquiv

end Restriction

section Measure

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]

local instance rationalUnitaryCharacterIso_sourceCompact : CompactSpace
    (unitaryUnramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters G
local instance rationalUnitaryCharacterIso_targetCompact : CompactSpace
    (unitaryUnramifiedCharacters (fun χ => (rationalNormCharacters H χ).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters H

/-- Haar probability is transported by the actual character isomorphism. -/
theorem map_rationalUnitaryUnramifiedProbabilityHaar (e : G ≅ H) :
    Measure.map (rationalUnitaryCharacterIso e) (rationalUnitaryUnramifiedProbabilityHaar G) =
      rationalUnitaryUnramifiedProbabilityHaar H := by
  exact ((rationalUnitaryCharacterIso e).toMonoidHom.measurePreserving
    (rationalUnitaryCharacterIso e).continuous (rationalUnitaryCharacterIso e).surjective
      (by simp [rationalUnitaryUnramifiedProbabilityHaar])).map_eq

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (e : G ≅ H)
  (hs : IsCentral s) (hsH : IsCentral (s ≫ e.hom))
  (hindexG : (RenardCartan.splitValuationImage s).FiniteIndex)
  (hindexH : (RenardCartan.splitValuationImage (s ≫ e.hom)).FiniteIndex)

/-- The kernel-scaled character Haar measure attached to the displayed central
morphism is transported with its finite restriction-kernel cardinality. In the
split-component specialization this is the character measure of Waldspurger I.1. -/
theorem map_rationalUnitaryUnramifiedCharacterHaar_of_iso :
    Measure.map (rationalUnitaryCharacterIso e)
        (rationalUnitaryUnramifiedCharacterHaar s hs hindexG) =
      rationalUnitaryUnramifiedCharacterHaar (s ≫ e.hom) hsH hindexH := by
  rw [rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability,
    Measure.map_smul (f := fun χ => rationalUnitaryCharacterIso e χ) _
      (rationalUnitaryCharacterIso e).continuous.measurable.aemeasurable,
    map_rationalUnitaryUnramifiedProbabilityHaar,
    rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability,
    rationalUnitaryCharacterIso_restriction_ker_card s e]

end Measure

end Langlands.Plancherel
