import Langlands.Representation.Exponents.WeakCriticalStatement
import Langlands.Group.GL.ConjugatePairRefinementRankProof
import Langlands.Representation.Exponents.DualJacquetInnerConjugationProof
import Langlands.Representation.Induction.SingleBlock
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Nat.Find

/-! Existence of a weakly minimal standard opposite-dual Jacquet pair. -/

noncomputable section

namespace Langlands

universe uF uV

namespace GeneralLinear.BlockShape

private theorem oneBlock_scalar {R : Type uF} [CommRing R] {n : ℕ}
    (B : BlockShape n) (hB : B.length = 1) (a : Fin B.length → Rˣ) :
    B.blockScalar R a = GeneralLinear.scalar (a (B.singleBlockIndex hB)) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  have hji : j = i := (B.eq_singleBlockIndex hB j).trans
    (B.eq_singleBlockIndex hB i).symm
  subst j
  change B.blockScalar R a (B.index i r) (B.index i s) =
    GeneralLinear.scalar (a (B.singleBlockIndex hB)) (B.index i r) (B.index i s)
  rw [B.blockScalar_apply_same]
  change (if r = s then (a i : R) else 0) =
    if B.index i r = B.index i s then (a (B.singleBlockIndex hB) : R) else 0
  simp only [(B.index i).injective.eq_iff]
  congr 2
  exact congrArg a (B.eq_singleBlockIndex hB i)

private theorem oneBlock_oppositeUnipotent_eq_one {R : Type uF} [CommRing R] {n : ℕ}
    (B : BlockShape n) (hB : B.length = 1) (g : B.oppositeUnipotentSubgroup R) :
    (g : GeneralLinear n R) = 1 := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  have hji : j = i := (B.eq_singleBlockIndex hB j).trans
    (B.eq_singleBlockIndex hB i).symm
  subst j
  have hg := (B.mem_oppositeUnipotentSubgroup_iff R g).mp g.property
  change (g : GeneralLinear n R) (B.index i r) (B.index i s) =
    (1 : GeneralLinear n R) (B.index i r) (B.index i s)
  rw [hg.2 i r s]
  change (if r = s then (1 : R) else 0) =
    if B.index i r = B.index i s then 1 else 0
  simp only [(B.index i).injective.eq_iff]

end GeneralLinear.BlockShape

namespace Exponents.ConjugateBlockPair

private theorem standard_pullbackRep {K : Type uF} [Field K] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (A : Rep.{uV} ℂ (GeneralLinear n K)) :
    (standard B).pullbackRep A = A := by
  change Rep.of (A.ρ.comp (MulAut.conj (1 : GeneralLinear n K)).toMonoidHom) = Rep.of A.ρ
  congr 1
  ext g v
  change A.ρ (1 * g * 1⁻¹) v = A.ρ g v
  simp

end Exponents.ConjugateBlockPair

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ}

/-- A nonzero representation with a smooth unitary scalar central character has
nonempty actual full-dual spectrum at every one-block shape. -/
theorem exists_unitaryDualJacquetExponent_oneBlock
    (B : GeneralLinear.BlockShape n) (hB : B.length = 1)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) [Nontrivial A]
    (c : letI := T.topology; UnitaryCentralCharacter A.ρ) :
    ∃ χ, T.IsUnitaryDualJacquetExponent B A χ := by
  let := T.topology
  let i := B.singleBlockIndex hB
  let z : (Fin B.length → F.Carrierˣ) →* Subgroup.center (GeneralLinear n F.Carrier) :=
    GeneralLinear.scalarToCenter.comp (Pi.evalMonoidHom _ i)
  let χ := c.character.comp z
  have hz : Continuous z :=
    ((GeneralLinear.scalarContinuous (R := F.Carrier) (n := n)).continuous.comp
      (continuous_apply i)).subtype_mk _
  have hχopen : IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) :=
    c.isOpen_ker.preimage hz
  obtain ⟨f, hf⟩ := exists_ne (0 : Module.Dual ℂ A)
  let fN : Jacquet.subgroupInvariantDual A.ρ (B.oppositeUnipotentSubgroup F.Carrier) :=
    ⟨f, by
      intro u v
      rw [B.oneBlock_oppositeUnipotent_eq_one hB u]
      simp⟩
  let e := T.splitCentreDualJacquetSourceEquiv B A
  let φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) := e.symm fN
  have hφ : φ ≠ 0 := by
    intro h
    have he : fN = 0 := e.symm.injective (h.trans (map_zero e.symm).symm)
    exact hf (congrArg Subtype.val he)
  have hmem : φ ∈ commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1 := by
    apply (T.mem_dualJacquet_eigenspace_iff B A χ φ).mpr
    intro a v
    have ha : B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) = (z a).val :=
      B.oneBlock_scalar hB a
    rw [ha, c.acts, map_smul, map_smul, T.singleBlock_leviHalfModulus B hB]
    simp only [Units.val_one, inv_one, one_mul, smul_eq_mul]
    rfl
  refine ⟨χ, ⟨hχopen, ?_⟩, fun a => c.norm_eq_one (z a)⟩
  intro hbot
  rw [hbot] at hmem
  change φ = 0 at hmem
  exact hφ hmem

/-- Analytic temperedness supplies the central-character datum used by the seed.
The all-Haar condition is instantiated at an existing Haar measure. -/
theorem IsTempered.exists_unitaryDualJacquetExponent_oneBlock
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} [Nontrivial A]
    (hA : T.IsTempered A.ρ)
    (B : GeneralLinear.BlockShape n) (hB : B.length = 1) :
    ∃ χ, T.IsUnitaryDualJacquetExponent B A χ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  obtain ⟨c, _⟩ := (hA μ).2
  exact T.exists_unitaryDualJacquetExponent_oneBlock B hB A c

/-- Irreducibility supplies nontriviality, so analytic temperedness supplies
an initial nonempty unitary dual spectrum at positive rank. -/
theorem IsTempered.exists_unitaryDualJacquetExponent
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : T.IsTempered A.ρ) (hI : Representation.IsIrreducible A.ρ) (hn : 0 < n) :
    ∃ B : GeneralLinear.BlockShape n, ∃ χ, T.IsUnitaryDualJacquetExponent B A χ := by
  let : Representation.IsIrreducible A.ρ := hI
  let : Nontrivial A :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule
  let B : GeneralLinear.BlockShape n :=
    { length := 1
      size := fun _ => n
      positive := fun _ => hn
      sum_eq := by simp }
  exact ⟨B, hA.exists_unitaryDualJacquetExponent_oneBlock T B rfl⟩

/-- A largest block length with nonempty spectrum excludes every strictly
finer concrete pair by rank growth and inner-conjugation transport. -/
private theorem exists_weaklyMinimal_of_unitarySpectrum
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hseed : ∃ B : GeneralLinear.BlockShape n, ∃ χ,
      T.IsUnitaryDualJacquetExponent B A χ) :
    ∃ B : GeneralLinear.BlockShape n,
      T.IsWeaklyMinimalDualJacquetPair (Exponents.ConjugateBlockPair.standard B) A := by
  classical
  let : Infinite F.Carrier := Infinite.of_injective
    (algebraMap (Padic p) F.Carrier) (algebraMap (Padic p) F.Carrier).injective
  have hstrict := (conjugatePairRefinementRank F.Carrier n).1
  have htransport := glDualJacquetInnerConjugation p F T n
  have hbound (B : GeneralLinear.BlockShape n) : B.length ≤ n := B.length_le
  let R : ℕ → Prop := fun k => ∃ B : GeneralLinear.BlockShape n,
    B.length = k ∧ ∃ χ, T.IsUnitaryDualJacquetExponent B A χ
  obtain ⟨B₀, hB₀⟩ := hseed
  have hR₀ : R B₀.length := ⟨B₀, rfl, hB₀⟩
  obtain ⟨B, hBk, hB⟩ := Nat.findGreatest_spec (P := R) (hbound B₀) hR₀
  refine ⟨B, ?_, ?_⟩
  · change ∃ χ, T.IsUnitaryDualJacquetExponent B
      ((Exponents.ConjugateBlockPair.standard B).pullbackRep A) χ
    rw [Exponents.ConjugateBlockPair.standard_pullbackRep]
    exact hB
  · intro Q hQ hψ
    obtain ⟨ψ, hψ⟩ := hψ
    have hψ' := (htransport Q A ψ).mp hψ
    have hlt : Nat.findGreatest R n < Q.shape.length := by
      rw [← hBk]
      exact hstrict (Exponents.ConjugateBlockPair.standard B) Q hQ
    exact Nat.findGreatest_is_greatest hlt (hbound Q.shape) ⟨Q.shape, rfl, ψ, hψ'⟩

end PadicField.TopologicalData

/-- Every irreducible analytically tempered source of positive rank has a
weakly minimal standard pair for its actual opposite-dual Jacquet spectrum. -/
theorem glWeaklyMinimalStandardPairExistence :
    GLWeaklyMinimalStandardPairExistenceStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn A hI hA
  exact T.exists_weaklyMinimal_of_unitarySpectrum A
    (hA.exists_unitaryDualJacquetExponent T hI hn)

end Langlands
