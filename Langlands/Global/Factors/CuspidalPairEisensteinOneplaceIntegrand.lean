import Langlands.Global.Factors.CuspidalPairEisensteinOneplaceLaw

/-! # The open-cell integrand on a cell at one unramified place

For a section built from cusp forms spherical outside `S`, a finite place `v ∉ S`, an adelic
matrix `Z` integral at `v` and a local matrix `y`, the open-cell integrand at `y_v + Z` is the
local factor `f_v(w u'(y)) conj(ψ_v(y_(t,0)))` times the integrand at `Z`. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairEisenstein.Oneplace

open MeasureTheory NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight OpenCellExhaustion
open scoped CategoryTheory.MonObj

section Local

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (r t : ℕ)

theorem fromBlocks_unipotent_mem {R : Type*} [CommRing R] {S : Type*} [SetLike S R]
    [SubringClass S R] (O : S) {m n : ℕ} (X : Matrix (Fin m) (Fin n) R)
    (hX : ∀ i j, X i j ∈ O) (i j : Fin m ⊕ Fin n) : Matrix.fromBlocks 1 X 0 1 i j ∈ O := by
  rcases i with a | a <;> rcases j with b | b
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · simp only [Matrix.fromBlocks_apply₁₂]
    exact hX a b
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    exact zero_mem _
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

/-- The block Weyl representative is integral. -/
theorem blockWeyl_mem_integralGroup :
    Shahidi.blockWeyl (r + 1) (t + 1) K.Carrier ∈ Shahidi.UnramifiedSection.integralGroup K r t := by
  rw [Shahidi.UnramifiedSection.mem_integralGroup_iff]
  have hent : ∀ (σ : Equiv.Perm (Fin (r + 1 + (t + 1)))) (i j : Fin (r + 1 + (t + 1))),
      GeneralLinear.permutation _ K.Carrier σ i j ∈ K.canonicalTopologicalData.Integers := by
    intro σ i j
    rw [GeneralLinear.permutation_entry]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => hent _ i j, fun i j => ?_⟩
  rw [Shahidi.blockWeyl, ← map_inv]
  exact hent _ i j

/-- The matrix `u'(Z)` of an integral matrix `Z` is integral. -/
theorem intertwiningUnipotent_mem_integralGroup (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hZ : ∀ i j, Z i j ∈ K.canonicalTopologicalData.Integers) :
    Shahidi.intertwiningUnipotent (r + 1) (t + 1) K.Carrier Z ∈
      Shahidi.UnramifiedSection.integralGroup K r t := by
  have hent : ∀ (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier),
      (∀ i j, Z i j ∈ K.canonicalTopologicalData.Integers) → ∀ i j,
        Shahidi.intertwiningUnipotent (r + 1) (t + 1) K.Carrier Z i j ∈
          K.canonicalTopologicalData.Integers :=
    fun Z hZ i j => fromBlocks_unipotent_mem _ Z hZ _ _
  rw [Shahidi.UnramifiedSection.mem_integralGroup_iff]
  refine ⟨hent Z hZ, fun i j => ?_⟩
  rw [← Shahidi.intertwiningUnipotent_neg]
  exact hent (-Z) (fun i j => neg_mem (hZ i j)) i j

end Local

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

theorem openCellUnipotent_add (Y Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    openCellUnipotent F r t (Y + Z) = openCellUnipotent F r t Y * openCellUnipotent F r t Z := by
  simp only [openCellUnipotent, Shahidi.intertwiningUnipotent_add, map_mul]

theorem comp_openCellWeyl (v : FinitePlace F) :
    comp F (r + t + 2) v (openCellWeyl F r t) =
      GeneralLinear.reindex (blockEquiv r t) (Shahidi.blockWeyl (r + 1) (t + 1) (FiniteCompletion F v)) := by
  rw [comp_eq_map, openCellWeyl, map_reindex, map_blockWeyl]

theorem comp_openCellUnipotent (v : FinitePlace F) (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    comp F (r + t + 2) v (openCellUnipotent F r t Z) =
      GeneralLinear.reindex (blockEquiv r t)
        (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) (matrixComponent v Z)) := by
  rw [comp_eq_map, openCellUnipotent, map_reindex, map_intertwiningUnipotent]
  rfl

/-- The matrix `u'(y_v)` of a local matrix placed at `v` is `u'(y)` placed at `v`. -/
theorem openCellUnipotent_localMatrix (v : FinitePlace F)
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v)) :
    openCellUnipotent F r t (localMatrix v y) =
      blockAt F r t v (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) := by
  refine adelic_ext ?_ fun w => ?_
  · rw [infinite_adelicAt]
    rw [show AdelicGL.infinite F (r + t + 2) (openCellUnipotent F r t (localMatrix v y)) =
        GeneralLinear.reindex (blockEquiv r t)
          (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (InfiniteAdeleRing F)
            ((localMatrix v y).map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)))) from
      (map_reindex _ _ _).trans (congrArg _ (map_intertwiningUnipotent _ _ _ _))]
    have h0 : (localMatrix v y).map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)) = 0 := by
      funext i j
      rfl
    rw [h0, Shahidi.intertwiningUnipotent_zero, map_one]
  · rw [comp_openCellUnipotent]
    by_cases hw : w = v
    · subst hw
      rw [matrixComponent_localMatrix, comp_adelicAt]
    · rw [matrixComponent_localMatrix_of_ne hw, Shahidi.intertwiningUnipotent_zero, map_one,
        comp_adelicAt_of_ne _ hw]

/-- The integrand in terms of the twisted section and the corner entry. -/
theorem openCellIntegrand_eq (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    openCellIntegrand ψ φ s Y =
      leviWhittaker F r t ψ (twisted φ s) (openCellWeyl F r t * openCellUnipotent F r t Y) *
        starRingEnd ℂ (ψ (Y (Fin.last t) 0)) := by
  rw [openCellIntegrand, openCellUnipotent_superdiagonal_sum]
  rfl

open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
theorem complex_localAdele (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv) (x : FiniteCompletion F v) :
    ψ.complex (localAdele v x) = (ψv x : ℂ) := by
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hψv x]
  rfl

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 1600000 in
open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
/-- **The integrand on a cell.** For `v ∉ S` as in `leviWhittaker_mul_blockAt`, an adelic
matrix `Z` integral at `v` and a local matrix `y`, the open-cell integrand at `y_v + Z` is
`f_v(w u'(y)) conj(ψ_v(y_(t,0)))` times the integrand at `Z`. -/
theorem openCellIntegrand_localMatrix_add
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pd : CuspidalSpectralPresentation.{u, uQ} (dualRealization T'))
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSection T T' φ)
    (hsph : IsSphericalSectionOutside T T' S φ) (s : ℂ) (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (hψv0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (ϖ : (CompletionPadic.padicField v).Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) ϖ)
    (a : Fin (r + 1) → ℂˣ)
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (c : Fin (t + 1) → ℂˣ)
    (hc : Unramified.Eigenvalues.ofTuple c =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (hZ : ∀ i j, matrixComponent v Z i j ∈ v.adicCompletionIntegers F)
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v)) :
    openCellIntegrand ψ.complex φ s (localMatrix v y + Z) =
      Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s
          (Shahidi.blockWeyl (r + 1) (t + 1) (FiniteCompletion F v) *
            Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) *
        starRingEnd ℂ (ψv (y (Fin.last t) 0) : ℂ) *
        openCellIntegrand ψ.complex φ s Z := by
  -- the local integral matrix `k₀ = w u'(Z_v)`
  have hZv : Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v)
      (matrixComponent v Z) ∈
        Shahidi.UnramifiedSection.integralGroup (CompletionPadic.padicField v) r t :=
    intertwiningUnipotent_mem_integralGroup (CompletionPadic.padicField v) r t _
      (fun i j => (mem_adicCompletionIntegers_iff_canonical v _).1 (hZ i j))
  set k₀ := Shahidi.blockWeyl (r + 1) (t + 1) (FiniteCompletion F v) *
    Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) (matrixComponent v Z)
    with hk₀
  have hk₀int : k₀ ∈ Shahidi.UnramifiedSection.integralGroup (CompletionPadic.padicField v) r t :=
    mul_mem (blockWeyl_mem_integralGroup (CompletionPadic.padicField v) r t) hZv
  set g₀ := openCellWeyl F r t * openCellUnipotent F r t Z with hg₀
  have hcomp : comp F (r + t + 2) v g₀ = GeneralLinear.reindex (blockEquiv r t) k₀ := by
    rw [hg₀, map_mul, comp_openCellWeyl, comp_openCellUnipotent, hk₀, map_mul]
  set g' := g₀ * (blockAt F r t v k₀)⁻¹ with hg'
  have hg'1 : comp F (r + t + 2) v g' = 1 := by
    rw [hg', map_mul, map_inv, hcomp, blockAt, comp_adelicAt, mul_inv_cancel]
  have hg₀' : g₀ = g' * blockAt F r t v k₀ := by
    rw [hg', inv_mul_cancel_right]
  have law := leviWhittaker_mul_blockAt P Pd hP hPd ψ hψF hS hφ hsph s v hv ψv hψv hψv0 ϖ hϖ
    a ha c hc g' hg'1
  -- the value at `Z`
  have hWZ : leviWhittaker F r t ψ.complex (twisted φ s) g₀ =
      leviWhittaker F r t ψ.complex (twisted φ s) g' := by
    rw [hg₀', law, Shahidi.UnramifiedSection.sectionFunction_integral hϖ a c s hψv0 _ hk₀int,
      one_mul]
  -- the value at `y_v + Z`
  have hcommU : Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v)
        (matrixComponent v Z) *
      Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y =
      Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y *
        Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v)
          (matrixComponent v Z) := by
    rw [← Shahidi.intertwiningUnipotent_add, add_comm (matrixComponent v Z) y,
      Shahidi.intertwiningUnipotent_add]
  have hsec : Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s
      (k₀ * Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) =
      Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s
        (Shahidi.blockWeyl (r + 1) (t + 1) (FiniteCompletion F v) *
          Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) := by
    rw [hk₀, mul_assoc, hcommU, ← mul_assoc]
    exact Shahidi.UnramifiedSection.sectionFunction_mul_integral hϖ a c s hψv0 _ _ hZv
  have hWY : leviWhittaker F r t ψ.complex (twisted φ s)
      (openCellWeyl F r t * openCellUnipotent F r t (localMatrix v y + Z)) =
      Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s
        (Shahidi.blockWeyl (r + 1) (t + 1) (FiniteCompletion F v) *
          Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) *
      leviWhittaker F r t ψ.complex (twisted φ s) g₀ := by
    have e : openCellWeyl F r t * openCellUnipotent F r t (localMatrix v y + Z) =
        g' * blockAt F r t v
          (k₀ * Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y) := by
      rw [add_comm (localMatrix v y) Z, openCellUnipotent_add, openCellUnipotent_localMatrix, blockAt_mul, ← mul_assoc,
        ← mul_assoc, ← hg₀, hg₀']
    rw [e, law, hsec, hWZ]
  have hchar : starRingEnd ℂ (ψ.complex ((localMatrix v y + Z) (Fin.last t) 0)) =
      starRingEnd ℂ (ψv (y (Fin.last t) 0) : ℂ) * starRingEnd ℂ (ψ.complex (Z (Fin.last t) 0)) := by
    rw [Matrix.add_apply, AddChar.map_add_eq_mul, map_mul]
    exact congrArg (fun z => starRingEnd ℂ z * _) (complex_localAdele ψ v ψv hψv _)
  rw [openCellIntegrand_eq, openCellIntegrand_eq, hWY, hchar]
  ring

end Langlands.Global.CuspidalPairEisenstein.Oneplace
