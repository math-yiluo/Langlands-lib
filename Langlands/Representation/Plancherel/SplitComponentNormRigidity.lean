import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.CorepresentedComultiplication

/-! # Rational-character norms detect the action on a split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- Equal normalized norms of field units give equal integer orders. -/
theorem fieldOrderUnits_eq_of_fieldNormUnits_eq {a b : kˣ}
    (h : fieldNormUnits k a = fieldNormUnits k b) :
    fieldOrderUnits k a = fieldOrderUnits k b := by
  have hn : fieldNormUnits k (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hv := (fieldNormUnits_eq_one_iff k (a * b⁻¹)).mp hn
  rw [map_mul, map_inv, mul_inv_eq_one] at hv
  exact hv

end Langlands.Plancherel

namespace Langlands.GroupScheme

open CocharacterUniformizer

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}

section NormDetection

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- On a split torus, equality of all normalized norms detects the character itself. -/
theorem IsSplitTorus.character_eq_of_rationalNormCharacters_eq
    (hA : IsSplitTorus A.toGrp) {χ ψ : rationalCharacters A.toGrp}
    (h : ∀ x : rationalPoints A.toGrp,
      (Plancherel.rationalNormCharacters A.toGrp χ).toMul x =
        (Plancherel.rationalNormCharacters A.toGrp ψ).toMul x) :
    χ = ψ := by
  let := latticePairing_isPerfPair k A hA
  apply (rationalCharacters.equivCharacterLattice A).injective
  apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
  apply LinearMap.ext
  intro c
  rw [← rationalCharacterValuation_latticeSection k A
    (rationalCharacters.equivCharacterLattice A χ) c,
    ← rationalCharacterValuation_latticeSection k A
      (rationalCharacters.equivCharacterLattice A ψ) c]
  simp only [AddEquiv.symm_apply_apply, Plancherel.rationalCharacterValuation_apply]
  exact congrArg Multiplicative.toAdd
    (Plancherel.fieldOrderUnits_eq_of_fieldNormUnits_eq (h _))

end NormDetection

section Restriction

variable {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom M.X.hom]
  {a : A.toGrp ⟶ M}

/-- The endomorphism of a split component induced by an ambient automorphism.
Its defining factorization is independent of character norms. -/
def IsSplitComponent.automorphismRestriction (ha : IsSplitComponent a) (φ : M ≅ M) :
    A.toGrp ⟶ A.toGrp :=
  (ha.exists_factor ha.1.1.1 (ha.1.2.comp_iso φ)).choose

/-- The restriction factors the original automorphism on the actual split component. -/
theorem IsSplitComponent.automorphismRestriction_comp
    (ha : IsSplitComponent a) (φ : M ≅ M) :
    ha.automorphismRestriction φ ≫ a = a ≫ φ.hom :=
  (ha.exists_factor ha.1.1.1 (ha.1.2.comp_iso φ)).choose_spec

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- An automorphism preserving all rational-character norms on central rational
points induces the identity on every split component of a connected reductive group. -/
theorem IsSplitComponent.automorphismRestriction_eq_id_of_norm
    (hM : IsConnectedReductive M) (ha : IsSplitComponent a) (φ : M ≅ M)
    (hnorm : ∀ x ∈ Subgroup.center (rationalPoints M), ∀ χ : rationalCharacters M,
      (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom x) =
        (Plancherel.rationalNormCharacters M χ).toMul x) :
    ha.automorphismRestriction φ = 𝟙 A.toGrp := by
  let f := ha.automorphismRestriction φ
  have hf : f ≫ a = a ≫ φ.hom := ha.automorphismRestriction_comp φ
  have hres (χ : rationalCharacters M) :
      characterRestrict f (characterRestrict a χ) = characterRestrict a χ := by
    apply ha.1.1.1.character_eq_of_rationalNormCharacters_eq
    intro x
    rw [Plancherel.rationalNormCharacters_characterRestrict,
      Plancherel.rationalNormCharacters_characterRestrict,
      Plancherel.rationalNormCharacters_characterRestrict]
    have hx : rationalPoints.map a x ∈ Subgroup.center (rationalPoints M) :=
      ha.1.range_le_center ⟨x, rfl⟩
    have he : rationalPoints.map a (rationalPoints.map f x) =
        rationalPoints.map φ.hom (rationalPoints.map a x) := by
      change x ≫ f.hom.hom ≫ a.hom.hom = x ≫ a.hom.hom ≫ φ.hom.hom.hom
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun q => x ≫ q.hom.hom) hf
    rw [he]
    exact hnorm _ hx χ
  let S := (characterRestrict a).range
  let : S.FiniteIndex := ha.finiteIndex_range_characterRestrict hM
  have hfix (ψ : rationalCharacters A.toGrp) : characterRestrict f ψ = ψ := by
    obtain ⟨χ, hχ⟩ := S.nsmul_index_mem ψ
    have he : S.index • characterRestrict f ψ = S.index • ψ := by
      rw [← map_nsmul, ← hχ]
      exact hres χ
    let := latticePairing_isPerfPair k A ha.1.1.1
    apply (rationalCharacters.equivCharacterLattice A).injective
    apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
    apply LinearMap.ext
    intro c
    have hp := congrArg (fun ξ : rationalCharacters A.toGrp =>
      latticePairing A (rationalCharacters.equivCharacterLattice A ξ) c) he
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hp
    exact mul_left_cancel₀
      (Int.natCast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := S))) hp
  have hfc : Additive.ofMul f = (𝟙 A : A ⟶ A) := by
    apply ha.1.1.1.hom_ext_characters
    intro χ
    have hc : (Additive.ofMul f : A ⟶ A) ≫ χ = χ :=
      congrArg (rationalCharacters.equivCharacterLattice A)
        (hfix ((rationalCharacters.equivCharacterLattice A).symm χ))
    rw [Category.id_comp]
    exact hc
  exact congrArg CommGroupScheme.groupHom hfc

/-- Norm preservation fixes the inclusion of the split component as a scheme morphism. -/
theorem IsSplitComponent.comp_automorphism_eq_of_norm
    (hM : IsConnectedReductive M) (ha : IsSplitComponent a) (φ : M ≅ M)
    (hnorm : ∀ x ∈ Subgroup.center (rationalPoints M), ∀ χ : rationalCharacters M,
      (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom x) =
        (Plancherel.rationalNormCharacters M χ).toMul x) :
    a ≫ φ.hom = a := by
  rw [← ha.automorphismRestriction_comp φ,
    ha.automorphismRestriction_eq_id_of_norm hM φ hnorm, Category.id_comp]

end Restriction

end Langlands.GroupScheme
