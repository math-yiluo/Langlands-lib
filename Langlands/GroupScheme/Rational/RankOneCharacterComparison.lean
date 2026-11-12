import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.NormKernelStandardCocharacter

/-! # Integral rank-one characters modulo ambient characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra.RationalSpan

/-- Every rationalized element has a positive integral multiple in the original image. -/
theorem exists_pos_nsmul_eq_toRat {M : Type*} [AddCommGroup M]
    (x : ℚ ⊗[ℤ] M) :
    ∃ d : ℕ, 0 < d ∧ ∃ m : M, d • x = toRat m := by
  induction x using TensorProduct.inductionOn with
  | tmul q m =>
    refine ⟨q.den, q.pos, q.num • m, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    change (q.den : ℚ) • (q ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (q.num • m)
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul,
      zsmul_eq_mul, mul_one, mul_comm, Rat.mul_den_eq_num]
  | add x y hx hy =>
    obtain ⟨d, hd, m, hm⟩ := hx
    obtain ⟨e, he, n, hn⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, e • m + d • n, ?_⟩
    rw [smul_add, mul_comm d e, mul_smul, hm, mul_comm e d, mul_smul, hn,
      map_add, map_nsmul, map_nsmul]

end Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

/-- A singleton actual simple-root set generates the full relative-root span. -/
theorem relativeRootSpan_eq_span_singleton_of_simpleRelativeRoots
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α}) :
    relativeRootSpan i = Submodule.span ℚ {toRat α} := by
  let := hi.isSplitSubtorus.mono
  have hroots := relativeRootSystem k G hG T i hi
  rw [← ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
    (fun _ hβ => hroots.neg_mem_relativeRoots i hi.1.1 hβ), hα, ratSpan,
    Set.image_singleton]

/-- In relative rank one, every actual torus character is rationally a root
multiple plus a restriction of an actual ambient rational character. -/
theorem exists_rat_root_add_restrict_of_simpleRelativeRoots_singleton
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (χ : characterLattice T) :
    ∃ (q : ℚ) (η : ℚ ⊗[ℤ] rationalCharacters G),
      toRat χ = q • toRat α + rationalCharacterRestrictRat i η := by
  have hχ : toRat χ ∈ relativeRootSpan i ⊔
      (rationalCharacterRestrictRat i).range := by
    rw [hG.relativeRootSpan_sup_restrictionRange_eq_top i hi]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, ⟨η, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hχ
  rw [relativeRootSpan_eq_span_singleton_of_simpleRelativeRoots
    i hG hi ν hν α hα] at hx
  obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨q, η, hsum.symm⟩

omit [IsAffineHom G.X.hom] in
/-- An exact integral root relation modulo an actual ambient character; the
denominator is positive and the root coefficient is signed. -/
def HasIntegralRootCharacterRelation (α χ : characterLattice T) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ (η : rationalCharacters G) (z : ℤ),
    d • χ = torusCharacterRestrict i η + z • α

/-- Clearing both denominators gives an exact integral relation, with a signed
root coefficient and an actual ambient rational character. -/
theorem exists_pos_nsmul_eq_restrict_add_zsmul_of_simpleRelativeRoots_singleton
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (χ : characterLattice T) :
    HasIntegralRootCharacterRelation i α χ := by
  obtain ⟨q, y, hy⟩ :=
    exists_rat_root_add_restrict_of_simpleRelativeRoots_singleton
      i hG hi ν hν α hα χ
  obtain ⟨d, hd, η, hη⟩ := exists_pos_nsmul_eq_toRat y
  refine ⟨d * q.den, Nat.mul_pos hd q.pos, q.den • η, (d : ℤ) * q.num, ?_⟩
  apply hi.1.1.character_toRat_injective
  have hηi : d • rationalCharacterRestrictRat i y =
      toRat (torusCharacterRestrict i η) := by
    rw [← map_nsmul, hη]
    rfl
  have hq : q.den • (d • (q • toRat α)) =
      ((d : ℤ) * q.num) • toRat α := by
    rw [smul_comm q.den d, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
      smul_smul, smul_smul]
    congr 1
    push_cast
    rw [mul_assoc, mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]
  calc
    toRat ((d * q.den) • χ) = q.den • (d • toRat χ) := by
      rw [map_nsmul, ← mul_smul, mul_comm d q.den]
    _ = q.den • (d • (q • toRat α + rationalCharacterRestrictRat i y)) := by
      rw [hy]
    _ = ((d : ℤ) * q.num) • toRat α +
        q.den • toRat (torusCharacterRestrict i η) := by
      rw [smul_add, smul_add, hq, hηi]
    _ = toRat (torusCharacterRestrict i (q.den • η) +
        ((d : ℤ) * q.num) • α) := by
      rw [map_add, map_nsmul, map_nsmul, map_zsmul, add_comm]

omit [IsAffineHom G.X.hom] in
/-- An ambient-character-annihilating cocharacter detects positivity of the
signed root coefficient in an exact character relation. -/
theorem root_coefficient_pos_of_pairing
    {α χ : characterLattice T} {d : ℕ} (hd : 0 < d)
    {η : rationalCharacters G} {z : ℤ}
    (hrel : d • χ = torusCharacterRestrict i η + z • α)
    (ζ : cocharacterLattice T)
    (hambient : ∀ ψ : rationalCharacters G,
      latticePairing T (torusCharacterRestrict i ψ) ζ = 0)
    (hαζ : 0 < latticePairing T α ζ)
    (hχζ : 0 < latticePairing T χ ζ) :
    0 < z := by
  have he := congrArg ((latticePairing T).flip ζ) hrel
  simp only [map_nsmul, map_add, map_zsmul, LinearMap.flip_apply,
    hambient η, zero_add, nsmul_eq_mul, zsmul_eq_mul] at he
  have hprod : 0 < z * latticePairing T α ζ :=
    he ▸ mul_pos (by exact_mod_cast hd) hχζ
  exact (mul_pos_iff_of_pos_right hαζ).mp hprod

/-- A positive pairing on a direction annihilating all ambient characters
upgrades the signed relation to positive natural coefficients. -/
theorem exists_pos_nsmul_eq_restrict_add_pos_nsmul_of_pairing
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (χ : characterLattice T) (ζ : cocharacterLattice T)
    (hambient : ∀ ψ : rationalCharacters G,
      latticePairing T (torusCharacterRestrict i ψ) ζ = 0)
    (hαζ : 0 < latticePairing T α ζ)
    (hχζ : 0 < latticePairing T χ ζ) :
    ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ ∃ η : rationalCharacters G,
      d • χ = torusCharacterRestrict i η + b • α := by
  obtain ⟨d, hd, η, z, hrel⟩ :=
    exists_pos_nsmul_eq_restrict_add_zsmul_of_simpleRelativeRoots_singleton
      i hG hi ν hν α hα χ
  have hz := root_coefficient_pos_of_pairing i hd hrel ζ hambient hαζ hχζ
  have hzNat : 0 < z.toNat := by omega
  have hzcast : (z.toNat : ℤ) = z := by omega
  refine ⟨d, z.toNat, hd, hzNat, η, ?_⟩
  rw [← hzcast] at hrel
  simpa only [natCast_zsmul] using hrel

section NormKernel

variable [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- For the actual Weyl correction of the generic cocharacter, the ambient
term vanishes and root positivity is automatic. Positivity of the given
character on that corrected direction remains an explicit premise. -/
theorem exists_pos_nsmul_eq_restrict_add_pos_nsmul_of_normKernel_pairing
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (χ : characterLattice T)
    (hχ : 0 < latticePairing T χ (normKernelCocharacter i ν)) :
    ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ ∃ η : rationalCharacters G,
      d • χ = torusCharacterRestrict i η + b • α := by
  apply exists_pos_nsmul_eq_restrict_add_pos_nsmul_of_pairing
    i hG hi ν hν α hα χ (normKernelCocharacter i ν)
    (latticePairing_normKernelCocharacter_restrict i ν) _ hχ
  have hαsimple : α ∈ simpleRelativeRoots i ν := by rw [hα]; rfl
  rw [latticePairing_normKernelCocharacter_root_of_relativeRootSystem
    i hi.1.1 (relativeRootSystem k G hG T i hi) ν α hαsimple.1.1, nsmul_eq_mul]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) hαsimple.1.2

end NormKernel

end Langlands.GroupScheme
