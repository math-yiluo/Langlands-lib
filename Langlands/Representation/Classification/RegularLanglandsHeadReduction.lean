import Langlands.Representation.Classification.RegularLanglandsStatement
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.HeadQuotientCriterionProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Twist.LeviRealPower
import Langlands.Group.GL.CompactOpen
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! Nonzero standard modules and a conditional construction of their canonical heads.
Finite length and exclusion of product quotients remain explicit hypotheses. -/

noncomputable section

namespace Langlands.RegularHeadExistence

universe uG uV

open Module CuspidalSupport.QuasicuspidalEmbedding

/-- A nonzero finite-length smooth representation has an actual smooth irreducible
quotient. This elementary helper does not assert uniqueness of its kernel. -/
theorem exists_irreducibleQuotient_of_finiteLength
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : A.HasFiniteLength) :
    ∃ B : SmoothRep.{0, uG, uV} ℂ G,
      Classification.IsIrreducibleQuotient A.representation B.representation := by
  have : IsNoetherian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  have hco : IsCoatomic (Subrepresentation A.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := A.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hbt : (⊥ : Subrepresentation A.representation) ≠ ⊤ := by
    intro h
    apply hv
    have hmem : v ∈ (⊥ : Subrepresentation A.representation) := by
      rw [h]
      exact Submodule.mem_top
    exact hmem
  obtain ⟨S, hS, -⟩ := (hco.eq_top_or_exists_le_coatom ⊥).resolve_left hbt
  let B := SmoothRep.quotient A S
  let q : A.representation.IntertwiningMap B.representation :=
    SmoothRep.hom (SmoothRep.mkQ A S)
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective A S
  have hqker : ∀ x, q x = 0 ↔ x ∈ S := fun x => Submodule.Quotient.mk_eq_zero _
  exact ⟨B, isIrreducible_of_isCoatom q hq S hS hqker, q, hq⟩

/-- Exclude actual quotients onto products of two irreducibles, including
two copies of the same irreducible. The target carriers use the source universe. -/
def NoIrreducibleProductQuotient
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∀ (W₁ W₂ : Type uV)
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (π₁ : Representation ℂ G W₁) (π₂ : Representation ℂ G W₂),
    Representation.IsIrreducible π₁ → Representation.IsIrreducible π₂ →
      ∀ q : ρ.IntertwiningMap (π₁.prod π₂), ¬ Function.Surjective q

/-- Finite length supplies existence; the product obstruction supplies equality
of the kernels of all irreducible quotient maps. -/
theorem hasIrreducibleHead_of_finiteLength_noProduct
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : A.HasFiniteLength)
    (hno : NoIrreducibleProductQuotient A.representation) :
    Classification.HasIrreducibleHead A.representation := by
  obtain ⟨B, hB⟩ := exists_irreducibleQuotient_of_finiteLength A hA
  exact (Classification.irreducibleHeadProductCriterion G A A.representation).mpr
    ⟨⟨B, inferInstance, inferInstance, B.representation, hB⟩, hno⟩

/-- The actual smooth canonical quotient, certified to be a strong irreducible
head under finite length, nonzeroness, and the product-quotient obstruction. -/
def canonicalIrreducibleHeadOfFiniteLength
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : A.HasFiniteLength)
    (hno : NoIrreducibleProductQuotient A.representation) :
    {B : SmoothRep.{0, uG, uV} ℂ G //
      Classification.IsIrreducibleHead A.representation B.representation} :=
  ⟨A.headQuotient, SmoothRep.isIrreducibleHead_headQuotient_iff.mpr
    (hasIrreducibleHead_of_finiteLength_noProduct A hA hno)⟩

@[simp]
theorem canonicalIrreducibleHeadOfFiniteLength_val
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : A.HasFiniteLength)
    (hno : NoIrreducibleProductQuotient A.representation) :
    (canonicalIrreducibleHeadOfFiniteLength A hA hno).val = A.headQuotient := rfl

universe uF

/-- Normalized product induction of nonzero smooth blocks is nonzero, witnessed
by a compact local section with a prescribed nonzero tensor value. -/
theorem nontrivial_normalizedProductInduction
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hA : ∀ i, Nontrivial (A i)) :
    let := T.topology
    Nontrivial ((T.normalizedProductInductionFunctor B).obj A) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := hA
  let b := fun i => Basis.ofVectorSpace ℂ (A i)
  let bt := Basis.piTensorProduct b
  have hidx : ∀ i, Nonempty (Basis.ofVectorSpaceIndex ℂ (A i)) :=
    fun i => (b i).index_nonempty
  let v := bt (fun i => Classical.choice (hidx i))
  have hv : v ≠ 0 := bt.ne_zero _
  let P := B.parabolic F.Carrier
  let σ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor (fun i => (A i).representation)).comp (B.leviProjection F.Carrier))
  have hσ : IsSmooth σ :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous
        (FiniteTensor.isSmooth_external _ (fun i => (A i).isSmooth)))
  let f := Induction.compactLocalSection P σ hσ 1 v Set.univ isOpen_univ (Set.mem_univ _)
  change Nontrivial (Induction.SmoothFunctions P σ)
  refine ⟨⟨f.val, 0, ?_⟩⟩
  intro hf
  apply hv
  have he := congrArg (fun z : Induction.SmoothFunctions P σ => Induction.eval P σ z 1) hf
  rw [Induction.compactLocalSection_apply] at he
  exact he

section StandardModule

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (d : T.TemperedLanglandsDatum.{uV, uF} n)

/-- Real determinant twists of the inducing tempered blocks remain irreducible. -/
theorem twistedBlock_irreducible (i : Fin d.shape.length) :
    letI := T.topology
    Representation.IsIrreducible
      (T.twistedBlocks d.shape d.blocks d.exponent i).representation := by
  let := T.topology
  exact (SmoothRep.isIrreducible_twist_iff _
    (T.isOpen_ker_determinantPowerCharacter _ _) (d.blocks i)).mpr (d.irreducible i)

/-- The inducing twisted blocks satisfy precisely the admissibility and finite
length premises of normalized product finite-length preservation. -/
theorem twistedBlock_admissible_finiteLength (i : Fin d.shape.length) :
    letI := T.topology
    (T.twistedBlocks d.shape d.blocks d.exponent i).IsAdmissible ∧
      (T.twistedBlocks d.shape d.blocks d.exponent i).HasFiniteLength := by
  let := T.topology
  have : Representation.IsIrreducible
      (T.twistedBlocks d.shape d.blocks d.exponent i).representation :=
    twistedBlock_irreducible T d i
  constructor
  · exact (SmoothRep.isAdmissible_twist_iff _
      (T.isOpen_ker_determinantPowerCharacter _ _) (d.blocks i)).mpr
      (d.tempered i).isAdmissible
  · exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The actual standard module attached to a tempered datum is nonzero. -/
theorem standardModule_nontrivial :
    letI := T.topology
    Nontrivial d.standardModule := by
  let := T.topology
  exact nontrivial_normalizedProductInduction T d.shape
    (T.twistedBlocks d.shape d.blocks d.exponent) (fun i =>
      nontrivial_of_isIrreducible _ (twistedBlock_irreducible T d i))

/-- Product finite-length preservation, if supplied, gives finite length of
the actual standard module. This does not prove that preservation statement. -/
theorem standardModule_finiteLength_of_productPreservation
    (hn : 0 < n)
    (hfinite : Classification.AdmissibleFiniteLengthProductPreservation.{uF, uV} F T) :
    letI := T.topology
    d.standardModule.HasFiniteLength := by
  let := T.topology
  exact hfinite n hn d.shape (T.twistedBlocks d.shape d.blocks d.exponent)
    (twistedBlock_admissible_finiteLength T d)

/-- A canonical Langlands head follows once finite length and the actual
two-irreducible-product obstruction have been proved for this standard module. -/
theorem standardModule_hasHead_of_finiteLength_noProduct
    (hfinite : letI := T.topology
      d.standardModule.HasFiniteLength)
    (hno : letI := T.topology
      NoIrreducibleProductQuotient d.standardModule.representation) :
    letI := T.topology
    d.IsLanglandsHead d.standardModule.headQuotient := by
  let := T.topology
  let := standardModule_nontrivial T d
  exact (canonicalIrreducibleHeadOfFiniteLength d.standardModule hfinite hno).property


end StandardModule

end Langlands.RegularHeadExistence
