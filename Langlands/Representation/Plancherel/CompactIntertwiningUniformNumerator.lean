import Langlands.Representation.Plancherel.CompactInductionGeneration

/-! # A uniform regular numerator for the actual standard compact operator -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uG uI uV

section Scalars

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- The regular function `χ ↦ δ^{1/2}(p) χ(proj p)` of the actual inducing
scalar at `p ∈ P`. -/
def inductionScalarRegularOf (p : P) : unramifiedRegularFunctions ν :=
  (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
    unramifiedEvaluationRegular ν (h.projection p)

theorem inductionScalarRegularOf_apply (p : P) (χ : unramifiedCharacters ν) :
    (inductionScalarRegularOf h hU ν p).val χ = inductionScalar h hU ν χ p := rfl

end Scalars

section Uniform

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The actual standard compact operator intertwines the parameter translates
of the source and target compact pictures. -/
theorem standardCompactOperator_compactTranslate (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (g : G) (f : CompactInductionPicture h K A) :
    standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
        qν μU' μI hqν hM hsq χ A hfull
        (compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g f) =
      compactTranslate h' hU' hδ' K hP' hK hP'K ν hν hr' A χ g
        (standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
          qν μU' μI hqν hM hsq χ A hfull f) := by
  simp only [standardCompactOperator, compactIntertwiningOperator, compactTranslate,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  congr 1
  exact (fullSourceIntertwiner h hU h' hU' _ qν μU' μI hqν hM hsq hfull).isIntertwining _ _ g _

/-- The value of the actual standard compact operator at `k ∈ K` is the identity
value of the `k`-translate. -/
theorem eval_standardCompactOperator_eq (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
        qν μU' μI hqν hM hsq χ A hfull f) k =
      compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ hfull
        (compactPictureAction h K A k f) := by
  rw [standardCompactOperator_eval]
  have he : (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm
      (compactPictureAction h K A k f) =
      (UnramifiedLeviInduction h hU ν χ A).representation (k : G)
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f) := by
    apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).injective
    rw [LinearEquiv.apply_symm_apply, unramifiedLeviInductionCompactEquiv_translate,
      LinearEquiv.apply_symm_apply]
  change _ = operator h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
    qν hM (sourceToDomain h hU _ qν hfull
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm
        (compactPictureAction h K A k f))) 1
  rw [he]
  have hact := operator_right_action h hU U'
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν hM
    (sourceToDomain h hU _ qν hfull
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)) (k : G)
  have h2 : sourceToDomain h hU _ qν hfull ((UnramifiedLeviInduction h hU ν χ A).representation
      (k : G) ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)) =
      ⟨((DynamicNormalization.leviTwistedInductionFunctor h hU).obj
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation (k : G)
          (sourceToDomain h hU _ qν hfull
            ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)).val,
        (domainSubrepresentation h hU U' _ qν).apply_mem_toSubmodule (k : G)
          (sourceToDomain h hU _ qν hfull
            ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)).property⟩ :=
    Subtype.ext rfl
  rw [h2]
  have h3 := congrFun hact 1
  simp only [one_mul] at h3
  exact h3.symm

omit [LocallyCompactSpace G] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G] in
/-- A right translate of a section fixed by `L₀` is fixed by every subgroup
whose `K`-conjugates lie in `L₀`. -/
theorem compactPictureAction_mem_compactFixed {L₀ H₁ : OpenSubgroup G}
    (hcore : ∀ x : K, (x : G) ∈ H₁ → ∀ k : K, ((k⁻¹ * x * k : K) : G) ∈ L₀)
    (φ : CompactFixedVectors h K A L₀) (k : K) :
    compactPictureAction h K A k φ.val ∈ CompactFixedVectors h K A H₁ := by
  intro x
  have hx : (((x : K)⁻¹ : K) : G) ∈ H₁ := H₁.inv_mem x.property
  have hk := hcore _ x.property k
  change compactPictureAction h K A (x : K) (compactPictureAction h K A k φ.val) =
    compactPictureAction h K A k φ.val
  rw [← Module.End.mul_apply, ← map_mul]
  have e : (x : K) * k = k * (k⁻¹ * (x : K) * k) := by group
  rw [e, map_mul, Module.End.mul_apply]
  congr 1
  exact φ.property ⟨_, hk⟩

/-- For a section fixed by `L₀` and any `g ∈ G`, the `g`-translate of `b`
times the standard compact operator is a polynomial family, provided `b`
makes identity values of sections fixed by `H₁` polynomial, and the
`K`-conjugates of `H₁` lie in `L₀`. -/
theorem isPolynomialOn_compactTranslate_standardCompactOperator {L₀ H₁ : OpenSubgroup G}
    (hL₀K : (L₀ : Subgroup G) ≤ K)
    (hcore : ∀ x : K, (x : G) ∈ H₁ → ∀ k : K, ((k⁻¹ * x * k : K) : G) ∈ L₀)
    (Ω : Set (unramifiedCharacters ν))
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤)
    (b : unramifiedRegularFunctions ν)
    (hb : ∀ w : CompactFixedVectors h K A H₁, IsPolynomialOn Ω (fun χ : Ω => b.val χ.val •
      compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val (hfull χ) w.val))
    (φ : CompactFixedVectors h K A L₀) (g : G) :
    IsPolynomialOn Ω (fun χ : Ω => compactTranslate h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val g
      (b.val χ.val • standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
        qν μU' μI hqν hM hsq χ.val A (hfull χ) φ.val)) := by
  set F : Ω → CompactInductionPicture h' K A := fun χ => b.val χ.val •
    standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
      qν μU' μI hqν hM hsq χ.val A (hfull χ) φ.val with hFdef
  have hFfix : ∀ χ : Ω, ∀ l : K, (l : G) ∈ L₀ → compactPictureAction h' K A l (F χ) = F χ := by
    intro χ l hl
    rw [hFdef]
    simp only [map_smul]
    congr 1
    rw [← compactTranslate_of_mem h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val l,
      ← standardCompactOperator_compactTranslate, compactTranslate_of_mem h hU hδ K hP hK hPK ν hν
        hr A χ.val l]
    congr 1
    exact φ.property ⟨l, hl⟩
  let H' : OpenSubgroup G := L₀.comap (MulAut.conj g⁻¹).toMonoidHom
    (IsTopologicalGroup.continuous_conj g⁻¹)
  have hmemH' : ∀ x : G, x ∈ H' ↔ g⁻¹ * x * g ∈ L₀ := by
    intro x
    change g⁻¹ * x * g⁻¹⁻¹ ∈ L₀ ↔ _
    rw [inv_inv]
  have hXfix : ∀ χ : Ω, compactTranslate h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val g (F χ) ∈
      CompactFixedVectors h' K A H' := by
    intro χ x
    have hxL : g⁻¹ * ((x : K) : G) * g ∈ L₀ := (hmemH' _).mp x.property
    change compactPictureAction h' K A (x : K) _ = _
    rw [← compactTranslate_of_mem h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val (x : K),
      ← Module.End.mul_apply, ← compactTranslate_mul]
    have e : ((x : K) : G) * g = g * (g⁻¹ * ((x : K) : G) * g) := by group
    rw [e, compactTranslate_mul, Module.End.mul_apply]
    congr 1
    have := compactTranslate_of_mem h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val
      ⟨g⁻¹ * ((x : K) : G) * g, hL₀K hxL⟩
    rw [show (g⁻¹ * ((x : K) : G) * g) = (((⟨g⁻¹ * ((x : K) : G) * g, hL₀K hxL⟩ : K)) : G) from rfl,
      this]
    exact hFfix χ _ hxL
  let X : Ω → CompactFixedVectors h' K A H' := fun χ => ⟨_, hXfix χ⟩
  have hX : ∀ y : K, IsPolynomialOn Ω (fun χ => eval _ _ (X χ).val y) := by
    intro y
    obtain ⟨p', k', hyg⟩ := hP'K ((y : G) * g)
    let w : CompactFixedVectors h K A H₁ :=
      ⟨_, compactPictureAction_mem_compactFixed h K A hcore φ k'⟩
    have heq : (fun χ : Ω => eval _ _ (X χ).val y) = fun χ : Ω =>
        (inductionScalarRegularOf h' hU' ν p').val χ.val •
          A.representation (h'.projection p') (b.val χ.val •
            compactIdentityValue h hU hδ K hP hK hPK ν hν hr A U' qν hM χ.val (hfull χ) w.val) := by
      funext χ
      change eval _ _ (compactTranslate h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val g (F χ)) y = _
      rw [eval_compactTranslate, hyg, extension_eval_mul, inductionScalarRegularOf_apply, hFdef]
      congr 2
      rw [eval_compactPicture_smul, eval_standardCompactOperator_eq]
    rw [heq]
    exact ((hb w).linearMap (A.representation (h'.projection p'))).regular_smul _
  have hXpoly := isPolynomialOn_compactFixed_of_eval h' K hK ν A H' X hX
  exact hXpoly.linearMap (Submodule.subtype _)

include hqν hP hν hr hK in
/-- One nonzero regular scalar makes the actual standard compact operator a
polynomial family on every compact section, over any set of parameters of full
convergence. The hypotheses are explicit opposite Iwahori contraction bases for
the source radical and for the target radical, admissibility and finite length. -/
theorem exists_uniform_standardCompactOperator_numerator [LocallyCompactSpace U']
    {Ubar : Subgroup G} (hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G))
    (hPUbar : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1) (g : G)
    (hbasis : Jacquet.HasOppositeIwahoriContractionBasis U M Ubar g)
    {Obar : Subgroup G} (a : G) (htarget : Jacquet.HasOppositeIwahoriContractionBasis U' M Obar a)
    (hadm : A.IsAdmissible) (hfin : A.HasFiniteLength) (Ω : Set (unramifiedCharacters ν))
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) :
    ∃ b : unramifiedRegularFunctions ν, b ≠ 0 ∧ IsPolynomialOperatorOn Ω (fun χ : Ω =>
      b.val χ.val • standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
        qν μU' μI hqν hM hsq χ.val A (hfull χ)) := by
  obtain ⟨L₀, -, -, hL₀K, hspan⟩ := exists_regularTranslateSpan_eq_top h hU hδ K hP hK hPK ν hν
    hr A hMUbar hPUbar g hbasis hfin Set.univ isOpen_univ trivial
  -- the normal core of `L₀ ∩ K` in `K`
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let L₀K : OpenSubgroup K := L₀.comap K.toSubgroup.subtype continuous_subtype_val
  have : Finite (K ⧸ L₀K.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ L₀K.isOpen
  have : L₀K.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let core : Subgroup K := L₀K.toSubgroup.normalCore
  have hcoreOpen : IsOpen (core : Set K) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (L₀K.toSubgroup.normalCore_isClosed L₀K.isClosed)
  have hOopen : IsOpen ((K.toSubgroup.subtype : K → G) '' (core : Set K)) :=
    K.isOpen.isOpenMap_subtype_val _ hcoreOpen
  obtain ⟨H₁, hH₁c, hH₁O, hI, -⟩ := htarget _ hOopen ⟨1, core.one_mem, rfl⟩
  have hH₁K : H₁ ≤ K := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hH₁O hx
    exact y.property
  have hcore : ∀ x : K, (x : G) ∈ H₁ → ∀ k : K, ((k⁻¹ * x * k : K) : G) ∈ L₀ := by
    intro x hx k
    obtain ⟨y, hy, hyx⟩ := hH₁O hx
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    have := hy k⁻¹
    rw [inv_inv] at this
    exact this
  obtain ⟨b, hb, hpoly⟩ := exists_regular_compactIdentityValue_numerator h hU hδ K hP hK hPK ν hν
    hr A U' h'.levi_le_normalizer qν μU' μI hqν hM hH₁c hH₁K hI hadm Ω hfull
  refine ⟨b, hb, fun f => ?_⟩
  have hf : f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨n, c, gs, j, hf⟩ := hf
  have heq : (fun χ : Ω => (b.val χ.val • standardCompactOperator h hU hδ K hP hK hPK ν hν hr
      h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ.val A (hfull χ)) f) = fun χ : Ω =>
      ∑ i, (c i).val χ.val • compactTranslate h' hU' hδ' K hP' hK hP'K ν hν hr' A χ.val (gs i)
        (b.val χ.val • standardCompactOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
          qν μU' μI hqν hM hsq χ.val A (hfull χ) (j i).val) := by
    funext χ
    rw [LinearMap.smul_apply, hf χ.val, _root_.map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, standardCompactOperator_compactTranslate, map_smul, smul_comm]
  change IsPolynomialOn Ω _
  rw [heq]
  exact isPolynomialOn_finset_sum _ _ fun i _ =>
    (isPolynomialOn_compactTranslate_standardCompactOperator h hU hδ K hP hK hPK ν hν hr A h' hU'
      hδ' hP' hP'K hr' qν μU' μI hqν hM hsq hL₀K hcore Ω hfull b hpoly (j i) (gs i)).regular_smul
      (c i)

end Uniform

end Langlands.Plancherel
