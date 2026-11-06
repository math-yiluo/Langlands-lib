import Langlands.ClassFieldTheory.Local.FiniteArtinReconstruction
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement

/-! # Finite-family equivalence and geometric normalization under reconstruction -/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace ProfiniteReciprocityReconstruction

open FiniteArtinReconstruction

variable (K : Type u) [Field K] [TopologicalSpace K]

/-- Every continuous homomorphism has compatible actual finite restrictions. -/
theorem finiteFamilyOfHom_compatible
    (r : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K) :
    FiniteArtinRestrictionRelation (finiteFamilyOfHom r) := by
  intro L M h
  apply ContinuousMonoidHom.ext
  intro x
  exact DFunLike.congr_fun (restrictionOfLE_comp K L M h) (r x)

variable [PerfectField K]

/-- Continuous maps to the actual Galois abelianization are exactly coherent finite families. -/
def finiteFamilyEquiv :
    (Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K) ≃
      {a : FiniteArtinFamily K // FiniteArtinRestrictionRelation a} where
  toFun r := ⟨finiteFamilyOfHom r, finiteFamilyOfHom_compatible K r⟩
  invFun a := reconstruct K a.val a.property
  left_inv _ := finiteFamilyOfHom_injective K
    (finiteFamilyOfHom_reconstruct K _ _)
  right_inv a := Subtype.ext (finiteFamilyOfHom_reconstruct K a.val a.property)

/-- The supplied finite residue normalization passes to the reconstructed homomorphism. -/
theorem reconstruct_geometric
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
    ∀ (a : FiniteArtinFamily F.Carrier) (ha : FiniteArtinSystemRelation a),
      (∀ (L : LocalFiniteAbelianExtension F)
        (S : (L.asPadicField (p := p)).TopologicalData)
        (b : F.Carrierˣ), T.ord (b : F.Carrier) = 1 →
        ∀ x : L.field, S.discreteValuation x ≤ 1 →
          S.discreteValuation ((a L b).symm x - x ^ T.residueCardinality) < 1) →
      GeometricProfiniteReciprocityRelation F T (reconstruct F.Carrier a ha.2) := by
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro a ha hnorm
  refine ⟨reconstruct_normResidue F.Carrier a ha, ?_⟩
  intro L S b hb x hx
  rw [finiteFamilyOfHom_reconstruct F.Carrier a ha.2]
  exact hnorm L S b hb x hx

end ProfiniteReciprocityReconstruction

end Langlands.LocalClassField
