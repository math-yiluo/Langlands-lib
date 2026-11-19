import Langlands.Representation.Finite.MackeyPairing
import Langlands.Representation.FiniteGeneralLinear.CuspidalWhittaker
import Langlands.Representation.FiniteGeneralLinear.FiniteProductCharacters
import Langlands.Representation.FiniteGeneralLinear.ParabolicDoubleCosets

/-! Whittaker heredity for finite Harish–Chandra induction. -/

noncomputable section

open scoped BigOperators
open Module Representation

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear Geometric Whittaker

variable {k : Type*} [Field k] [Finite k] {n : ℕ}

/-- Inflate a Levi representation and induce from its standard parabolic. -/
def harishChandraInduce (B : BlockShape n) (V : FDRep ℂ (B.Levi k)) :
    FDRep ℂ (GeneralLinear n k) :=
  induceRep (B.parabolic k) (pullbackRep (B.leviProjection k) V)

/-- The finite Gelfand–Graev representation induced from the entrywise character. -/
def gelfandGraevRep (ψ : AddChar k ℂ) (n : ℕ) : FDRep ℂ (GeneralLinear n k) :=
  induceRep (upperUnipotent n k) (oneDimensional (entrywiseCharacter ψ n))

/-- Character vectors give the multiplicity of maps from the Gelfand–Graev representation. -/
theorem finrank_intertwiningMap_gelfandGraevRep (ψ : AddChar k ℂ)
    (W : FDRep ℂ (GeneralLinear n k)) :
    finrank ℂ (IntertwiningMap (gelfandGraevRep ψ n).ρ W.ρ) =
      finrank ℂ (whittakerVectors W.ρ ψ) := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let U := upperUnipotent n k
  let θ := entrywiseCharacter ψ n
  change finrank ℂ (IntertwiningMap (induceRep U (oneDimensional θ)).ρ W.ρ) = _
  rw [finrank_intertwiningMap_induceRep_left]
  exact (oneDimensionalIntertwiningMapEquiv (pullbackRep U.subtype W) θ).finrank_eq

omit [Finite k] in
private theorem mackeyTerm_nonOpen (B : BlockShape (n + 1)) (V : FDRep ℂ (B.Levi k))
    {ψ : AddChar k ℂ} (hψ : ψ ≠ 0)
    (v : MinimalRepresentatives B (BlockShape.singletons (n + 1)))
    (hv : v.val ≠ B.reversePermutation.symm) :
    mackeyTerm (B.parabolic k) (upperUnipotent (n + 1) k)
      (oneDimensional (entrywiseCharacter ψ (n + 1))) (pullbackRep (B.leviProjection k) V)
      (unipotentParabolicRepresentative (k := k) B v) = 0 := by
  let P := B.parabolic k
  let U := upperUnipotent (n + 1) k
  let w := unipotentParabolicRepresentative (k := k) B v
  let S := orbitStabilizer P U w
  let f := (B.leviProjection k).comp (stabilizerToInducing P U w)
  let χ := (entrywiseCharacter ψ (n + 1)).comp S.subtype
  let W := pullbackRep f V
  obtain ⟨q, hq, hqψ⟩ := nonOpenCharacterWitness k n B ψ (by simpa [AddChar.one_eq_zero] using hψ) v hv
  change finrank ℂ (IntertwiningMap (oneDimensional χ).ρ W.ρ) = 0
  rw [(oneDimensionalIntertwiningMapEquiv W χ).finrank_eq, Submodule.finrank_eq_zero]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have he : W.ρ q x = x := by
    change V.ρ (f q) x = x
    change f q = 1 at hq
    rw [hq, map_one]
    rfl
  have hx' : W.ρ q x = (χ q : ℂ) • x := hx q
  have hne : (χ q : ℂ) ≠ 1 := by
    intro h
    apply hqψ
    apply Units.ext
    exact h
  have hzero : ((χ q : ℂ) - 1) • x = 0 := by rw [sub_smul, one_smul, ← hx', he, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

private theorem mackeyTerm_open (B : BlockShape n) (ψ : AddChar k ℂ)
    (V : ∀ i : Fin B.length, FDRep ℂ (GeneralLinear (B.size i) k)) :
    mackeyTerm (B.parabolic k) (upperUnipotent n k)
      (oneDimensional (entrywiseCharacter ψ n))
      (pullbackRep (B.leviProjection k) (externalRep V)) (B.reverseMatrix k)⁻¹ =
      ∏ i, finrank ℂ (whittakerVectors (V i).ρ ψ) := by
  classical
  let U := upperUnipotent n k
  let P := B.parabolic k
  let S := openStabilizer B k
  let U₀ (i : Fin B.length) := upperUnipotent (B.size i) k
  let e := openStabilizerEquiv B k
  let θ := entrywiseCharacter ψ n
  let A (i : Fin B.length) : FDRep ℂ (U₀ i) :=
    oneDimensional (entrywiseCharacter ψ (B.size i))
  let D (i : Fin B.length) : FDRep ℂ (U₀ i) := pullbackRep (U₀ i).subtype (V i)
  let : Fintype S := Fintype.ofFinite S
  let : ∀ i, Fintype (U₀ i) := fun i => Fintype.ofFinite (U₀ i)
  have hOpen : mackeyTerm P U (oneDimensional θ)
      (pullbackRep (B.leviProjection k) (externalRep V)) (B.reverseMatrix k)⁻¹ =
      finrank ℂ (IntertwiningMap (pullbackRep e.toMonoidHom (externalRep A)).ρ
        (pullbackRep e.toMonoidHom (externalRep D)).ρ) := by
    let χ := θ.comp S.subtype
    let f := (B.leviProjection k).comp (stabilizerToInducing P U (B.reverseMatrix k)⁻¹)
    let W := pullbackRep f (externalRep V)
    change finrank ℂ (IntertwiningMap (oneDimensional χ).ρ W.ρ) = _
    apply Nat.cast_injective (R := ℂ)
    rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    change (oneDimensional χ).character q⁻¹ * W.character q =
      (pullbackRep e.toMonoidHom (externalRep A)).character q⁻¹ *
        (pullbackRep e.toMonoidHom (externalRep D)).character q
    rw [character_oneDimensional, character_pullbackRep, character_pullbackRep, character_pullbackRep,
      character_externalRep, character_externalRep, character_externalRep]
    have hχ : χ q⁻¹ = ∏ i, entrywiseCharacter ψ (B.size i) (e q⁻¹ i) :=
      openStabilizerEquiv_character B k ψ q⁻¹
    have hW (i : Fin B.length) : f q i = (e q i).val := by
      exact congrFun (openStabilizerEquiv_leviProjection B k q) i
    simp only [A, D, character_oneDimensional, character_pullbackRep, hχ, hW, Units.coe_prod,
      MulEquiv.coe_toMonoidHom]
    rfl
  rw [hOpen, finrank_intertwiningMap_pullbackRep, finrank_intertwiningMap_externalRep]
  apply Finset.prod_congr rfl
  intro i _
  exact (oneDimensionalIntertwiningMapEquiv (D i) (entrywiseCharacter ψ (B.size i))).finrank_eq

/-- The dimension of Whittaker vectors in parabolic induction of an external Levi tensor
is the product of the individual Whittaker dimensions. -/
theorem finrank_whittakerVectors_harishChandraInduce (B : BlockShape (n + 1))
    (V : ∀ i : Fin B.length, FDRep ℂ (GeneralLinear (B.size i) k))
    {ψ : AddChar k ℂ} (hψ : ψ ≠ 0) :
    finrank ℂ (whittakerVectors (harishChandraInduce B (externalRep V)).ρ ψ) =
      ∏ i, finrank ℂ (whittakerVectors (V i).ρ ψ) := by
  classical
  let I := MinimalRepresentatives B (BlockShape.singletons (n + 1))
  let : Fintype I := Fintype.ofFinite I
  let := Fintype.ofFinite (GeneralLinear (n + 1) k)
  let v₀ : I := ⟨B.reversePermutation.symm, reversePermutation_isMinimalRepresentative B⟩
  rw [← finrank_intertwiningMap_gelfandGraevRep]
  change finrank ℂ (IntertwiningMap
    (induceRep (upperUnipotent (n + 1) k) (oneDimensional (entrywiseCharacter ψ (n + 1)))).ρ
    (induceRep (B.parabolic k) (pullbackRep (B.leviProjection k) (externalRep V))).ρ) = _
  rw [finrank_intertwiningMap_induceRep _ _ _ _ (unipotentParabolicRepresentative (k := k) B)
    (unipotentParabolicDoubleCoset_bijective B), Fintype.sum_eq_single v₀]
  · have he : unipotentParabolicRepresentative (k := k) B v₀ = (B.reverseMatrix k)⁻¹ := by
      change permutation (n + 1) k B.reversePermutation⁻¹ = (permutation (n + 1) k B.reversePermutation)⁻¹
      exact map_inv _ _
    rw [he]
    exact mackeyTerm_open B ψ V
  · intro v hv
    exact mackeyTerm_nonOpen B (externalRep V) hψ v (fun h => hv (Subtype.ext h))

end Langlands.FiniteGeneralLinear
