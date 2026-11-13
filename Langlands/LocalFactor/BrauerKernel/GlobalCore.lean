import Langlands.LocalFactor.BrauerKernel.BrauerArch
import Langlands.LocalFactor.BrauerKernel.GlobalEpsilonIdentity
import Langlands.LocalFactor.BrauerKernel.GlobalLocalRelation
import Langlands.LocalFactor.BrauerKernel.PlaceEuler
import Langlands.LocalFactor.BrauerKernel.ArchimedeanTrivial
import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Global.Factors.HeckeFunctionalEquationProof
import Langlands.Global.Factors.HeckeConductorSupport
import Langlands.Global.Factors.HeckeEpsilonProduct
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.Factors.RelativeWeilAssemblyExceptional
import Langlands.Global.Arithmetic.RamifiedTwistIsolationProof
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement

/-! # The epsilon product at the distinguished place of a global Brauer relation -/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open ClassField.Global ClassField.Global.RelativeWeilGroup VirtualRepresentation
open scoped NumberField

section Helpers

variable {k : Type u} [Field k] [NumberField k]

omit [NumberField k] in
/-- A finite place lying over `z` restricts to `z`. -/
theorem under_eq_of_liesOver {M : Type u} [Field M] [NumberField M] [Algebra k M]
    {z : Langlands.Global.FinitePlace k} (q : Langlands.Global.FinitePlace M)
    [h : q.asIdeal.LiesOver z.asIdeal] : q.under (𝓞 k) = z :=
  HeightOneSpectrum.ext h.over.symm

variable {E : Type u} [Field E] [NumberField E] [Algebra k E]

/-- The epsilon factors of the Brauer product package are continuous in `s`. -/
theorem continuous_brauerEpsilon {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField k E)
    (Λ₁ Λ₂ : ∀ i, HeckeCharacter (K i)) (χ : HeckeCharacter k)
    (ψf : ∀ v : Langlands.Global.FinitePlace k,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : Langlands.Global.FinitePlace k,
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (μK : ∀ i (u : Langlands.Global.FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u))
    (d : ℤ) (B : Finset (Langlands.Global.FinitePlace k)) :
    Continuous (fun s => ∏ z ∈ B, (finiteEpsilon χ ψf μ z s ^ d * ∏ i ∈ Finset.univ,
      ((∏ u ∈ placesAbove (K i) z, finiteEpsilon (Λ₁ i) (traceComponents ψf) (μK i) u s) *
        (∏ u ∈ placesAbove (K i) z,
          finiteEpsilon (Λ₂ i) (traceComponents ψf) (μK i) u s)⁻¹) ^ r i)) := by
  have hc : ∀ i (Λ : HeckeCharacter (K i)) (z : Langlands.Global.FinitePlace k),
      Continuous (fun s => ∏ u ∈ placesAbove (K i) z,
        finiteEpsilon Λ (traceComponents ψf) (μK i) u s) := fun i Λ z =>
    continuous_finsetProd _ fun u _ =>
      (finiteEpsilon_differentiable Λ (traceComponents ψf) (μK i) u).continuous
  have hne : ∀ i (Λ : HeckeCharacter (K i)) (z : Langlands.Global.FinitePlace k) (s : ℂ),
      ∏ u ∈ placesAbove (K i) z, finiteEpsilon Λ (traceComponents ψf) (μK i) u s ≠ 0 :=
    fun i Λ z s => Finset.prod_ne_zero_iff.mpr fun u _ =>
      finiteEpsilon_ne_zero Λ (traceComponents ψf) (μK i) u s
  refine continuous_finsetProd _ fun z _ => ?_
  refine Continuous.mul ?_ (continuous_finsetProd _ fun i _ => ?_)
  · exact (finiteEpsilon_differentiable χ ψf μ z).continuous.zpow₀ d fun s =>
      Or.inl (finiteEpsilon_ne_zero χ ψf μ z s)
  · exact ((hc i (Λ₁ i) z).mul ((hc i (Λ₂ i) z).inv₀ (hne i (Λ₂ i) z))).zpow₀ (r i) fun s =>
      Or.inl (mul_ne_zero (hne i (Λ₁ i) z s) (inv_ne_zero (hne i (Λ₂ i) z s)))

end Helpers

section Core

attribute [local instance] relativeGaloisTopology isTotallyReal_intermediateField

/-- For a totally real Galois `E/k`, the archimedean components of `(α ∘ N) · ‖·‖^t · Θ` are those
of `‖·‖^t` when `α` is trivial at infinity and the reciprocity character of `Θ` is trivial on
the idele classes of `E`. -/
theorem infiniteComponent_twist_eq {k E : Type u} [Field k] [NumberField k] [Field E]
    [NumberField E] [Algebra k E] [IsGalois k E] [IsTotallyReal E]
    {c : FundamentalClass.ClassFamily.{u}} (M : IntermediateField k E) (α : HeckeCharacter k)
    (hα : α.HasPrescribedInfinityComponent 1) (t : ℂ) (Θ : HeckeCharacter M)
    (hΘ : ∀ a, continuousReciprocityCharacter c M E Θ (inclusion c M E a) = 1)
    (w : NumberField.InfinitePlace M) :
    (HeckeCharacter.normComp α * HeckeCharacter.normPower M t * Θ).infiniteComponent w =
      (HeckeCharacter.normPower M t).infiniteComponent w := by
  rw [HeckeCharacter.infiniteComponent_mul, HeckeCharacter.infiniteComponent_mul,
    HeckeCharacter.normComp_infiniteComponent_eq_one α hα w,
    infiniteComponent_eq_one_of_isTotallyReal (c := c) Θ hΘ w]
  refine DFunLike.ext _ _ fun x => ?_
  change (1 : ℂˣ) * (HeckeCharacter.normPower M t).infiniteComponent w x * 1 = _
  rw [one_mul, mul_one]

set_option maxHeartbeats 4000000 in
/-- **The epsilon product at a distinguished place.** Assume the existence of normalized local
reciprocity families, of local-to-relative Weil maps, and the transfer reciprocity of p-adic
extensions. Let `E/k` be a totally real Galois extension of number fields, `K i` intermediate
fields with nonzero weights `r i`, and `Θ_j i` Hecke characters whose reciprocity characters are
trivial on the idele classes of `E`. Suppose that for every Hecke character `α` of `k` the
characters `(α ∘ N) · ‖·‖^{t_j i} · Θ_j i` satisfy the global relation, and that the types are
balanced (`hdim`). Then at every finite place `v` there are a twist `α`, trivial at `v` and at
infinity, a nontrivial additive character `ψv` and Haar measures for which the epsilon product of
the place `v` is `1`. -/
theorem exists_twist_placeEpsilonRatioProduct_eq_one
    (hM : LocalRelativeWeilMapExistenceStatement.{0})
    (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{0, 0})
    (hCC : LocalClassField.CommonClosureReciprocityExistence.{0})
    (I : ∀ (p : ℕ) [Fact p.Prime], ClassFieldTheory.Local.InvariantFamily.{0, 0} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (c : FundamentalClass.ClassFamily.{0})
    (hc : FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
      FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c)
    {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    [IsGalois k E] [IsTotallyReal E]
    {n : ℕ} (r : Fin n → ℤ) (hr : ∀ i, r i ≠ 0) (K : Fin n → IntermediateField k E)
    (t₁ t₂ : Fin n → ℂ) (Θ₁ Θ₂ : ∀ i, HeckeCharacter (K i))
    (hΘ₁ : ∀ i a, continuousReciprocityCharacter c (K i) E (Θ₁ i) (inclusion c (K i) E a) = 1)
    (hΘ₂ : ∀ i a, continuousReciprocityCharacter c (K i) E (Θ₂ i) (inclusion c (K i) E a) = 1)
    (hrel : ∀ α : HeckeCharacter k, ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
        (restrictionInclusion c k E (K i) hc.2.1)
        (isOpenEmbedding_restrictionInclusion c k E (K i) hc.2.1)
        (ExactGrothendieckGroup.characterClass.{0, uV}
            (continuousReciprocityCharacter c (K i) E
              (HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i)) -
          ExactGrothendieckGroup.characterClass.{0, uV}
            (continuousReciprocityCharacter c (K i) E
              (HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i))) =
      (0 : ContinuousVirtual.{0, uV} c k E))
    (hdim : ∀ τ, ∑ i ∈ Finset.univ, r i * (Module.finrank k (K i) : ℤ) *
      ((if t₁ i = τ then 1 else 0) - (if t₂ i = τ then 1 else 0)) = 0)
    (v : Langlands.Global.FinitePlace k) :
    ∃ (ψv : Correspondence.NontrivialAdditiveCharacter (padicField v))
      (μv : ∀ j : (Σ i, FinitePlacesAbove (K i) v),
        Correspondence.LocalAdditiveHaarMeasure (towerPadicField v j.2.1))
      (α : HeckeCharacter k), α.finiteComponent v = 1 ∧ α.HasPrescribedInfinityComponent 1 ∧
      placeEpsilonRatioProduct r K
        (fun i => HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i)
        (fun i => HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i)
        v ψv μv = 1 := by
  classical
  -- normalized reciprocity families at every finite place
  choose eC heC using fun z : Langlands.Global.FinitePlace k =>
    hCC (residuePrime z) (padicField z) (padicField z).canonicalTopologicalData
  -- the global additive character, its components and self-dual measures
  obtain ⟨ψ, hψ, ψc, hψc, -⟩ := exists_associatedAdditiveInputs k
  let ψf : ∀ z : Langlands.Global.FinitePlace k,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField z).Carrier _
        (topologicalData z).topology := fun z => ofCanonicalCharacter z (ψc z)
  have hψf : ∀ z, IsFiniteAdditiveComponent ψ z (ψf z) := fun z => hψc z
  have hψ1 : ∃ x : Adeles k, ψ x ≠ 1 := by
    by_contra! h0
    exact ψ.nontrivial (DFunLike.ext _ _ h0)
  have hH := heckeGlobalFunctionalEquation_proof.{0}
  obtain ⟨DF⟩ := nonempty_heckeArchData hH (1 : HeckeCharacter k) ψ hψ1 hψ
  let μ : ∀ z, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData z) (ψf z) := fun z =>
    Classical.choice (nonempty_selfDualHaar z (ψf z))
  let μK : ∀ i (u : Langlands.Global.FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u) :=
    fun i u => Classical.choice (nonempty_selfDualHaar u (traceComponents ψf u))
  -- the auxiliary set `T` of ramified places other than `v`
  have hramfin : ∀ i, {q : HeightOneSpectrum (𝓞 (K i)) |
      q.asIdeal.ramificationIdx (𝓞 k) ≠ 1}.Finite := fun i =>
    AdelicFunctoriality.finite_setOf_ramificationIdx_ne_one k (K i)
  choose SΘ₁ hSΘ₁ using fun i => exists_finset_isUnramifiedAt (K i) (Θ₁ i)
  choose SΘ₂ hSΘ₂ using fun i => exists_finset_isUnramifiedAt (K i) (Θ₂ i)
  let R : ∀ i, Finset (Langlands.Global.FinitePlace (K i)) := fun i =>
    (hramfin i).toFinset ∪ SΘ₁ i ∪ SΘ₂ i
  let T : Finset (Langlands.Global.FinitePlace k) :=
    (Finset.univ.biUnion fun i => (R i).image fun q => q.under (𝓞 k)).erase v
  have hvT : v ∉ T := Finset.notMem_erase v _
  have hT : ∀ z, z ≠ v → z ∉ T → ∀ i (q : FinitePlacesAbove (K i) z),
      q.1.asIdeal.ramificationIdx (𝓞 k) = 1 ∧ (Θ₁ i).IsUnramifiedAt q.1 ∧
        (Θ₂ i).IsUnramifiedAt q.1 := by
    intro z hzv hzT i q
    have : q.1.asIdeal.LiesOver z.asIdeal := q.2
    have hq : q.1 ∉ R i := by
      intro hqR
      apply hzT
      exact Finset.mem_erase.mpr ⟨hzv, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨q.1, hqR, under_eq_of_liesOver q.1⟩⟩⟩
    simp only [R, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or,
      not_not] at hq
    exact ⟨hq.1.1, hSΘ₁ i q.1 hq.1.2, hSΘ₂ i q.1 hq.2⟩
  -- conductor bounds of the untwisted characters
  have hKb : ∀ z : Langlands.Global.FinitePlace k, ∃ Kb : ℕ,
      ∀ i (q : FinitePlacesAbove (K i) z),
        (towerPadicField z q.1).canonicalTopologicalData.multiplicativeConductor
            (quasicharacterAt q.1 (residuePrime_eq z q.1)
              ((HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i).finiteComponent q.1)) ≤ Kb ∧
        (towerPadicField z q.1).canonicalTopologicalData.multiplicativeConductor
            (quasicharacterAt q.1 (residuePrime_eq z q.1)
              ((HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i).finiteComponent q.1)) ≤ Kb := by
    intro z
    obtain ⟨Kb, hKb⟩ := (Set.finite_range (fun j : (Σ i, FinitePlacesAbove (K i) z) =>
      (towerPadicField z j.2.1).canonicalTopologicalData.multiplicativeConductor
          (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
            ((HeckeCharacter.normPower (K j.1) (t₁ j.1) * Θ₁ j.1).finiteComponent j.2.1)) +
      (towerPadicField z j.2.1).canonicalTopologicalData.multiplicativeConductor
          (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
            ((HeckeCharacter.normPower (K j.1) (t₂ j.1) * Θ₂ j.1).finiteComponent
              j.2.1)))).bddAbove
    refine ⟨Kb, fun i q => ?_⟩
    have hle := hKb ⟨⟨i, q⟩, rfl⟩
    exact ⟨le_trans (Nat.le_add_right _ _) hle, le_trans (Nat.le_add_left _ _) hle⟩
  choose Kb hKbspec using hKb
  -- the conductor depths required of the twist
  choose Bd hBd using fun z : Langlands.Global.FinitePlace k =>
    exists_bound_placeEpsilonRatioProduct_eq_one.{0, uV} r K z (eC z) (heC z) (ψc z) (Kb z)
  -- the twist
  have hdisj : Disjoint ({v} : Finset (Langlands.Global.FinitePlace k)) T :=
    Finset.disjoint_singleton_left.mpr hvT
  obtain ⟨α, -, hαS, hαinf, hαT⟩ := ramifiedTwistIsolation k {v} T hdisj (fun _ => 1)
    (fun z => Bd z.1) (fun _ => ⟨1, one_pos, pow_one _⟩)
  have hαv : α.finiteComponent v = 1 := hαS ⟨v, Finset.mem_singleton_self v⟩
  let Λ₁ : ∀ i, HeckeCharacter (K i) := fun i =>
    HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i
  let Λ₂ : ∀ i, HeckeCharacter (K i) := fun i =>
    HeckeCharacter.normComp α * HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i
  have hrelz : ∀ z, LocalPlaceRelation.{0, uV} r K Λ₁ Λ₂ z (eC z) := fun z =>
    localPlaceRelation_of_global hM hsq I hI c hc r K Λ₁ Λ₂ (hrel α) z (eC z) (heC z)
  have hΛ₁ : ∀ i w, (Λ₁ i).infiniteComponent w =
      (HeckeCharacter.normPower (K i) (t₁ i)).infiniteComponent w := fun i w =>
    infiniteComponent_twist_eq (c := c) (K i) α hαinf (t₁ i) (Θ₁ i) (hΘ₁ i) w
  have hΛ₂ : ∀ i w, (Λ₂ i).infiniteComponent w =
      (HeckeCharacter.normPower (K i) (t₂ i)).infiniteComponent w := fun i w =>
    infiniteComponent_twist_eq (c := c) (K i) α hαinf (t₂ i) (Θ₂ i) (hΘ₂ i) w
  let DK : ∀ i, HeckeArchData (Λ₁ i) (traceAdditiveCharacter (L := K i) ψ hψ) := fun i =>
    normPowerArchData ψ hψ DF.aR DF.haR (t₁ i) (Λ₁ i) (hΛ₁ i)
  let DK' : ∀ i, HeckeArchData (Λ₂ i) (traceAdditiveCharacter (L := K i) ψ hψ) := fun i =>
    normPowerArchData ψ hψ DF.aR DF.haR (t₂ i) (Λ₂ i) (hΛ₂ i)
  -- the epsilon supports
  choose S₁ hS₁ using fun i => exists_finset_finiteEpsilon_eq_one
    (traceAdditiveCharacter (L := K i) ψ hψ) (traceAdditiveCharacter_diagonal ψ hψ)
    (traceComponents ψf) (isFiniteAdditiveComponent_traceComponents ψ hψ ψf hψf)
    (DK i).aR (DK i).haR (DK i).aC (DK i).haC (Λ₁ i) (μK i)
  choose S₂ hS₂ using fun i => exists_finset_finiteEpsilon_eq_one
    (traceAdditiveCharacter (L := K i) ψ hψ) (traceAdditiveCharacter_diagonal ψ hψ)
    (traceComponents ψf) (isFiniteAdditiveComponent_traceComponents ψ hψ ψf hψf)
    (DK' i).aR (DK' i).haR (DK' i).aC (DK' i).haC (Λ₂ i) (μK i)
  obtain ⟨Sχ, hSχ⟩ := exists_finset_finiteEpsilon_eq_one ψ hψ ψf hψf DF.aR DF.haR DF.aC DF.haC
    (1 : HeckeCharacter k) μ
  let B : Finset (Langlands.Global.FinitePlace k) := insert v (T ∪ Sχ ∪
    Finset.univ.biUnion fun i => (S₁ i ∪ S₂ i).image fun q => q.under (𝓞 k))
  have hBK₁ : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (Λ₁ i) (traceComponents ψf) (μK i) u s = 1 := by
    intro i z hz u hu s
    refine hS₁ i u (fun huS => hz ?_) s
    rw [mem_placesAbove] at hu
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨u, Finset.mem_union_left _ huS, hu⟩⟩))
  have hBK₂ : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (Λ₂ i) (traceComponents ψf) (μK i) u s = 1 := by
    intro i z hz u hu s
    refine hS₂ i u (fun huS => hz ?_) s
    rw [mem_placesAbove] at hu
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨u, Finset.mem_union_right _ huS, hu⟩⟩))
  have hBF : ∀ z ∉ B, ∀ s : ℂ, finiteEpsilon (1 : HeckeCharacter k) ψf μ z s = 1 :=
    fun z hz s => hSχ z (fun h0 => hz (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ h0)))) s
  -- the global functional equation of the Brauer product
  have hP := hasGlobalEquation_brauerProduct hH ψ hψ1 hψ ψf hψf μ 0 1 DF r K Λ₁ Λ₂ μK DK DK' B
    hBF hBK₁ hBK₂
  let e : Langlands.Global.FinitePlace k → ℂ → ℂ := fun z s =>
    finiteEpsilon (1 : HeckeCharacter k) ψf μ z s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((∏ u ∈ placesAbove (K i) z, finiteEpsilon (Λ₁ i) (traceComponents ψf) (μK i) u s) *
        (∏ u ∈ placesAbove (K i) z,
          finiteEpsilon (Λ₂ i) (traceComponents ψf) (μK i) u s)⁻¹) ^ r i
  have hprod : ∏ z ∈ B, e z 0 = 1 := prod_epsilon_eq_one_of_hasGlobalEquation hP
    (fun z s hne => by
      rw [zpow_zero, one_mul] at hne ⊢
      exact prod_heckeL_eq_one_of_ne_zero r K Λ₁ Λ₂ z (eC z) (heC z) (hrelz z) hr s hne)
    (fun z s hne => by
      rw [zpow_zero, one_mul] at hne ⊢
      exact prod_heckeL_eq_one_of_ne_zero r K (fun i => (Λ₁ i)⁻¹) (fun i => (Λ₂ i)⁻¹) z (eC z)
        (heC z) (localPlaceRelation_inv r K Λ₁ Λ₂ z (eC z) (hrelz z)) hr s hne)
    (meromorphicEq_brauerArch_A ψ hψ DF.aR DF.haR r K t₁ t₂ Λ₁ Λ₂ hΛ₁ hΛ₂ hdim DF)
    (meromorphicEq_brauerArch_Ad ψ hψ DF.aR DF.haR r K t₁ t₂ Λ₁ Λ₂ hΛ₁ hΛ₂ hdim DF)
    (meromorphicEq_of_eq fun s =>
      brauerArch_Ae_eq_one ψ hψ DF.aR DF.haR r K t₁ t₂ Λ₁ Λ₂ hΛ₁ hΛ₂ hdim DF s)
    0 (continuous_brauerEpsilon r K Λ₁ Λ₂ 1 ψf μ μK 0 B).continuousAt
  -- the epsilon factors at the places of `B`
  have hez : ∀ z, e z 0 = placeEpsilonRatioProduct r K Λ₁ Λ₂ z (ψc z)
      (fun j => haarMeasureAt j.2.1 (residuePrime_eq z j.2.1) (μK j.1 j.2.1).val) := by
    intro z
    change finiteEpsilon (1 : HeckeCharacter k) ψf μ z 0 ^ (0 : ℤ) * _ = _
    rw [zpow_zero, one_mul]
    exact prod_finiteEpsilon_eq_placeEpsilonRatioProduct r K Λ₁ Λ₂ z ψf (ψc z) rfl μK
  have hone : ∀ z, z ≠ v → e z 0 = 1 := by
    intro z hzv
    rw [hez z]
    by_cases hzT : z ∈ T
    · refine hBd z α ?_ Λ₁ Λ₂ (fun i => HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i)
        (fun i => HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i) (hrelz z)
        (fun i => mul_assoc (HeckeCharacter.normComp α) (HeckeCharacter.normPower (K i) (t₁ i)) (Θ₁ i))
        (fun i => mul_assoc (HeckeCharacter.normComp α) (HeckeCharacter.normPower (K i) (t₂ i)) (Θ₂ i)) (fun i q => hKbspec z i q) _
      exact (lt_multiplicativeConductor_quasicharacterBase z (α.finiteComponent z) (Bd z)
        (hαT ⟨z, hzT⟩)).le
    · exact placeEpsilonRatioProduct_eq_one_of_unramified r K Λ₁ Λ₂ z (eC z) (heC z) (hrelz z) α
        (fun i => HeckeCharacter.normPower (K i) (t₁ i) * Θ₁ i)
        (fun i => HeckeCharacter.normPower (K i) (t₂ i) * Θ₂ i)
        (fun i => mul_assoc (HeckeCharacter.normComp α) (HeckeCharacter.normPower (K i) (t₁ i)) (Θ₁ i))
        (fun i => mul_assoc (HeckeCharacter.normComp α) (HeckeCharacter.normPower (K i) (t₂ i)) (Θ₂ i))
        (fun i q => (hT z hzv hzT i q).1)
        (fun i q => ⟨isUnramifiedAt_mul (HeckeCharacter.normPower_isUnramifiedAt (K i) _ _)
            (hT z hzv hzT i q).2.1,
          isUnramifiedAt_mul (HeckeCharacter.normPower_isUnramifiedAt (K i) _ _)
            (hT z hzv hzT i q).2.2⟩) (ψc z) _
  have hev : e v 0 = 1 := by
    rw [← hprod]
    exact (Finset.prod_eq_single_of_mem v (Finset.mem_insert_self v _)
      fun z _ hzv => hone z hzv).symm
  exact ⟨ψc v, _, α, hαv, hαinf, (hez v).symm.trans hev⟩

end Core

end Langlands.LocalFactor.NonabelianBrauer
