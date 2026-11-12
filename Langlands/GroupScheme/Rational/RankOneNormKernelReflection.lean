import Langlands.GroupScheme.Rational.RankOneCharacterComparison
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints

/-! # Actual normalizers reversing rank-one norm-kernel cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- An actual rational normalizer reverses the specified integral cocharacter. -/
def HasReversingNormalizer (ζ : cocharacterLattice T) : Prop :=
  ∃ n : normalizerPoints i, cocharacterAut (normalizingAut i n) ζ = -ζ

/-- Root relations and ambient-character annihilation promote root reflection
to reversal of an entire integral cocharacter. -/
theorem relativeWeylCocharacterAction_eq_neg_of_root_relations
    (hT : IsSplitTorus T.toGrp) (α : characterLattice T)
    (hrel : ∀ χ : characterLattice T, HasIntegralRootCharacterRelation i α χ)
    (ζ : cocharacterLattice T)
    (hambient : ∀ ψ : rationalCharacters G,
      latticePairing T (torusCharacterRestrict i ψ) ζ = 0)
    (w : relativeWeylGroup i)
    (hw : relativeWeylCharacterAction i w α = -α) :
    relativeWeylCocharacterAction i w ζ = -ζ := by
  apply sub_eq_zero.mp
  apply hT.cocharacter_eq_zero
  intro χ
  obtain ⟨d, hd, ψ, z, hχ⟩ := hrel χ
  have hψ : latticePairing T (torusCharacterRestrict i ψ)
      (relativeWeylCocharacterAction i w ζ) = 0 := by
    rw [latticePairing_relativeWeyl_right,
      relativeWeylCharacterAction_eq_latticeAction,
      relativeWeylLatticeAction_torusCharacterRestrict, hambient]
  have hα : latticePairing T α (relativeWeylCocharacterAction i w ζ) =
      -latticePairing T α ζ := by
    have h := latticePairing_relativeWeyl i w α ζ
    rw [hw, map_neg, LinearMap.neg_apply] at h
    omega
  have h₁ := congrArg ((latticePairing T).flip ζ) hχ
  have h₂ := congrArg ((latticePairing T).flip
    (relativeWeylCocharacterAction i w ζ)) hχ
  simp only [map_nsmul, map_add, map_zsmul, LinearMap.flip_apply,
    hambient ψ, hψ, hα, zero_add, nsmul_eq_mul, zsmul_eq_mul] at h₁ h₂
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hpair : latticePairing T χ (relativeWeylCocharacterAction i w ζ) =
      -latticePairing T χ ζ := by
    apply mul_left_cancel₀ hd0
    simpa only [mul_neg, h₁] using h₂
  rw [map_sub, map_neg, hpair, sub_self]

variable [IsAffineHom G.X.hom]

/-- A singleton actual simple-root set supplies an actual rational normalizer
reversing every cocharacter annihilating ambient rational characters. -/
theorem hasReversingNormalizer_of_simpleRelativeRoots_singleton
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (ζ : cocharacterLattice T)
    (hambient : ∀ ψ : rationalCharacters G,
      latticePairing T (torusCharacterRestrict i ψ) ζ = 0) :
    HasReversingNormalizer i ζ := by
  have hαsimple : α ∈ simpleRelativeRoots i ν := by rw [hα]; rfl
  obtain ⟨w, hw⟩ :=
    (relativeRootSystem k G hG T i hi).exists_isRelativeReflection hαsimple.1.1
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨n, ?_⟩
  exact relativeWeylCocharacterAction_eq_neg_of_root_relations i hi.1.1 α
    (exists_pos_nsmul_eq_restrict_add_zsmul_of_simpleRelativeRoots_singleton
      i hG hi ν hν α hα) ζ hambient _
    (hw.relativeWeylCharacterAction_apply_self i hi.1.1)

/-- In actual relative rank one, the integral Weyl correction has a rational
normalizer reversing it; no splitting of the ambient group is required. -/
theorem hasReversingNormalizer_normKernelCocharacter
    [Fintype (relativeWeylGroup i)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α}) :
    HasReversingNormalizer i (normKernelCocharacter i ν) :=
  hasReversingNormalizer_of_simpleRelativeRoots_singleton i hG hi ν hν α hα _
    (latticePairing_normKernelCocharacter_restrict i ν)

end Langlands.GroupScheme
