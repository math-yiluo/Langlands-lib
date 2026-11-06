import Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds
import Langlands.Representation.Plancherel.ParabolicRootCone
import Langlands.Representation.Plancherel.ParabolicIntertwiningDecayAssembly
import Langlands.Representation.Plancherel.ParabolicIntertwiningTopology
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.Representation.Plancherel.ParabolicSquaredModulusReduction
import Langlands.Representation.Plancherel.RationalModerateGrowthUniformization

/-! # The character decay on the opposite chart from the relative root system -/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped NNReal CategoryTheory.MonObj Matrix

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- **Exponential bound from a cone bound and a height bound.** If
`H ≤ -(s' D) |h| + K`, `log y = h` and `X ≤ C max(1, y⁻¹) ^ D` with `X ≥ 1`, then
`exp H ≤ exp (K + s' log C) X ^ (-s)` for every `s ≤ s'` with `s' ≥ 0`. -/
theorem exp_le_of_cone_height {Hν Hψ K₁ sp s C₃ X y : ℝ} {D : ℕ} (hsp : 0 ≤ sp) (hs : s ≤ sp)
    (hC₃ : 0 < C₃) (hX : 1 ≤ X)
    (hcone : Hν ≤ -(sp * D) * |Hψ| + K₁) (hψ : Real.log y = Hψ)
    (hheight : X ≤ C₃ * max 1 y⁻¹ ^ D) :
    Real.exp Hν ≤ Real.exp (K₁ + sp * Real.log C₃) * X ^ (-s) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hmax : 0 < max 1 y⁻¹ := lt_max_of_lt_left one_pos
  have hlogmax : Real.log (max 1 y⁻¹) ≤ |Hψ| := by
    rcases le_total y⁻¹ 1 with h1 | h1
    · rw [max_eq_left h1, Real.log_one]
      exact abs_nonneg _
    · rw [max_eq_right h1, Real.log_inv, hψ]
      exact neg_le_abs _
  have hlogX : Real.log X ≤ Real.log C₃ + D * |Hψ| := by
    have h1 := Real.log_le_log hX0 hheight
    rw [Real.log_mul hC₃.ne' (pow_pos hmax D).ne', Real.log_pow] at h1
    have h2 := mul_le_mul_of_nonneg_left hlogmax (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    linarith
  have h2 : sp * Real.log X ≤ sp * Real.log C₃ + sp * D * |Hψ| := by
    have h3 := mul_le_mul_of_nonneg_left hlogX hsp
    rw [mul_add, ← mul_assoc] at h3
    exact h3
  have hkey : Hν ≤ K₁ + sp * Real.log C₃ + Real.log X * (-sp) := by
    have h4 : -(sp * D) * |Hψ| = -(sp * D * |Hψ|) := by ring
    rw [h4] at hcone
    nlinarith
  calc Real.exp Hν ≤ Real.exp (K₁ + sp * Real.log C₃ + Real.log X * (-sp)) :=
        Real.exp_le_exp.2 hkey
    _ = Real.exp (K₁ + sp * Real.log C₃) * X ^ (-sp) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hX0]
    _ ≤ Real.exp (K₁ + sp * Real.log C₃) * X ^ (-s) := by
        gcongr

/-- **Closed representations of positive dimension.** A smooth connected affine group over a
field has a closed matrix representation on `Fin (N + 1)`: a Chevalley line for the identity
subgroup gives a monomorphism, which is a closed embedding. -/
theorem exists_isClosedSubgroup_fin_succ {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin (N + 1))), IsClosedSubgroup ρ := by
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G _ (kernelUnit G)
    (kernelUnit_isClosedSubgroup G)
  refine ⟨n, ρ, ?_⟩
  have : Mono ρ.hom.hom := by
    constructor
    intro Z x y hxy
    have hm : ρ.pointMatrix Z x = ρ.pointMatrix Z y := by
      rw [MatrixRepresentation.pointMatrix_apply, MatrixRepresentation.pointMatrix_apply, hxy]
    have h1 : ρ.pointMatrix Z (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hm, inv_mul_cancel]
    have hmem : x⁻¹ * y ∈ (SubgroupFunctor.range (kernelUnit G)).carrier Z := by
      refine (hρ Z _).2 ⟨1, ?_⟩
      rw [h1, Units.val_one, Matrix.one_mulVec, Units.val_one, one_smul]
    rw [range_kernelUnit] at hmem
    have h2 : x⁻¹ * y = 1 := by
      simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hmem
    exact (inv_mul_eq_one.mp h2)
  have : Smooth (GeneralLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin (n + 1)) (CommRingCat.of k)
  exact HomImage.isClosedSubgroup_of_mono ρ

section Host

open Aubert.General Induction StandardIntertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
  (hLevi : l ≫ p = l' ≫ p')
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  {n' : U' ⟶ P'} (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
  {q : Q ⟶ G}
  (hQ : (Dynamic.parabolic
    (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
  {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v)

local instance charDecayProofAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance charDecayProofTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance charDecayProofTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt U'pt : Subgroup (rationalPoints G)}
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
  (hU'pt : U'pt = (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))

/-- **The real exponent of the half modulus.** The normalized real part, on the split
component `A`, of the half modulus `δ_P^{1/2}` on `M(F)`: the vector `ρ_P` of the real
character space of `A` with `log ‖δ_P^{1/2}(m)‖ = ⟨ρ_P, H_M(m)⟩` for every logarithm vector
`H_M(m)` of `m`. -/
def parabolicHalfModulusRealPart
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) : RealTorusSpace.Vstar A :=
  SplitTorus.normalizedRealPart r.isCompatible.splitComponent.1.isSplitSubtorus.1
    ((parabolicLeviHalfModulus r h hU).comp (rationalPoints.map a))

include r' hLevi hn hn' hQ hv hUpt hU'pt in
/-- **The character decay on the opposite chart.** For connected reductive `G`, assuming the
relative root system statement and that central split tori detect nonzero rational characters,
the half modulus times every character of the intertwining regions decays at the Levi
components of `Ū(F) ∩ U'(F)` faster than any power of the height, locally uniformly. -/
theorem parabolicOppositeCharacterDecay_of_statements
    (hRS : RelativeRootSystemStatement.{u}) (hS : CentralSplitTorusCharacterStatement.{u})
    (hG : IsConnectedReductive G)
    [Mono r.data.i.hom.hom.left] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Fintype (relativeWeylGroup r.data.i)]
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G)))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N))
    (hρ₀ : IsClosedSubgroup ρ₀) :
    ParabolicOppositeCharacterDecay r (U'pt := U'pt) h hU K ρ₀
      (parabolicPointUnramifiedIntertwiningRegion r
        (weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i) n q v) := by
  classical
  have hA : IsSplitTorus A.toGrp := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hM : IsConnectedReductive M := r.isCompatible.levi.isConnectedReductive
  have hs : IsSplitComponent a := r.isCompatible.splitComponent
  have hinj := characterRestrict_injective_of_centralSplitTorusCharacter hS hM hs
  set B := weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
    r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i with hB
  -- logarithm vectors of Levi points
  choose w hw using fun m : rationalPoints M => exists_splitComponentLogarithm hM hs hinj m
  -- the Chevalley line of the parabolic and its height bound
  obtain ⟨ξl, C₃, D, hC₃, hline⟩ := exists_parabolicLineCharacter_rationalMatrixNorm_le
    (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) ρ₀ hρ₀ hK
  have hPlam := Dynamic.Affine.isRepresentedBy_parabolicHom
    (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)
  have hlelam : SubgroupFunctor.range (l ≫ p) ≤ Dynamic.parabolic
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) :=
    r.levi_eq_splitComponentCocharacter.le.trans (Dynamic.centralizer_le_parabolic _)
  have hglam : hPlam.factorHom (l ≫ p) hlelam ≫ Dynamic.Affine.parabolicHom
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) = l ≫ p :=
    hPlam.factorHom_comp _ _
  obtain ⟨ξM, hξM⟩ : ∃ ξM : rationalCharacters M,
      ξM = characterRestrict (hPlam.factorHom (l ≫ p) hlelam) ξl := ⟨_, rfl⟩
  obtain ⟨ψl, hψl⟩ : ∃ ψl : RealTorusSpace.Vstar A, ψl = (1 : ℝ) ⊗ₜ[ℤ]
      rationalCharacters.equivCharacterLattice A (characterRestrict a ξM) := ⟨_, rfl⟩
  -- the admissible positive-weight lines
  have hle' : Dynamic.centralizer (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫
      a ≫ l ≫ p) ≤ Dynamic.centralizer
        (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) := by
    rw [← r.levi_eq_splitComponentCocharacter, hLevi, ← r'.levi_eq_splitComponentCocharacter]
  choose ξf Cf hCf hresf hlowf using fun (mu : cocharacterLattice A)
      (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p) r.splitComponentCocharacter
        r'.splitComponentCocharacter mu) =>
    exists_positiveWeightLine_le_abs r hn hUpt h hK r'.splitComponentCocharacter mu hle' hmu
  let c : cocharacterLattice A → ℝ := fun mu =>
    if hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p) r.splitComponentCocharacter
      r'.splitComponentCocharacter mu then -Real.log (Cf mu hmu) else 0
  -- the half modulus vector
  obtain ⟨νδ, hνδ⟩ : ∃ νδ : RealTorusSpace.Vstar A,
      νδ = parabolicHalfModulusRealPart r h hU := ⟨_, rfl⟩
  have hfin := hA.finite_relativeRoots (a ≫ l ≫ p)
  set RA := hfin.toFinset with hRA_def
  have hRA : ∀ α, α ∈ RA ↔ α ∈ relativeRoots (a ≫ l ≫ p) := fun α => hfin.mem_toFinset
  obtain ⟨Sδ, hSδ⟩ : ∃ Sδ : ℝ, Sδ = relativeRootAbsSum (a ≫ l ≫ p) B νδ := ⟨_, rfl⟩
  intro s
  set sp := max s 0 with hsp_def
  have hsp : 0 ≤ sp := le_max_right _ _
  have hssp : s ≤ sp := le_max_left _ _
  obtain ⟨R₀, K₀, hcone⟩ := exists_parabolicRootCone_decay r hA hT hRS hG
    r.splitComponentCocharacter r'.splitComponentCocharacter c ψl (sp * D)
  refine ⟨R₀ + Sδ, fun σ hσ hσŪ => ?_⟩
  intro χ₀ hχ₀
  obtain ⟨νf, hνf⟩ : ∃ νf : unramifiedCharacters (parabolicLeviRationalNormCharacters r) →
      RealTorusSpace.Vstar A, νf = fun χ => SplitTorus.normalizedRealPart hA
        (χ.val.toMonoidHom.comp (parabolicSplitComponentPointHom r)) := ⟨_, rfl⟩
  have hcontα : ∀ α : characterLattice A,
      Continuous fun χ => B (νf χ) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    intro α
    rw [hνf]
    exact SplitTorus.continuous_normalizedRealPart_apply hA _
      (fun x => (continuous_eval_const (parabolicSplitComponentPointHom r x)).comp
        continuous_subtype_val) (B.flip ((1 : ℝ) ⊗ₜ[ℤ] α))
  have hSeq : ∀ ν, relativeRootAbsSum (a ≫ l ≫ p) B ν =
      ∑ α ∈ RA, |B ν ((1 : ℝ) ⊗ₜ[ℤ] α)| :=
    fun ν => relativeRootAbsSum_eq_sum (a ≫ l ≫ p) B RA hRA ν
  have hcontS : Continuous fun χ => relativeRootAbsSum (a ≫ l ≫ p) B (νf χ) := by
    simp_rw [hSeq]
    exact continuous_finsetSum _ fun α _ => (hcontα α).abs
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℝ, S₀ = relativeRootAbsSum (a ≫ l ≫ p) B (νf χ₀) := ⟨_, rfl⟩
  have hopen := isOpen_parabolicPointUnramifiedIntertwiningRegion r B n q v (R₀ + Sδ)
  have hlt : χ₀ ∈ {χ | relativeRootAbsSum (a ≫ l ≫ p) B (νf χ) < S₀ + 1} := by
    change relativeRootAbsSum (a ≫ l ≫ p) B (νf χ₀) < S₀ + 1
    rw [← hS₀]
    exact lt_add_one S₀
  refine ⟨parabolicPointUnramifiedIntertwiningRegion r B n q v (R₀ + Sδ) ∩
    {χ | relativeRootAbsSum (a ≫ l ≫ p) B (νf χ) < S₀ + 1},
    Filter.inter_mem (hopen.mem_nhds hχ₀) ((isOpen_lt hcontS continuous_const).mem_nhds hlt), ?_⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = max K₀ 0 * (2 + S₀ + Sδ) := ⟨_, rfl⟩
  refine ⟨Real.exp (K₁ + sp * Real.log C₃), fun χ hχ qq pp κ hpκ => ?_⟩
  dsimp only
  -- the point and its Levi component
  obtain ⟨x, hx_def⟩ : ∃ x : rationalPoints G, x = ((σ qq : U'pt) : rationalPoints G) :=
    ⟨_, rfl⟩
  rw [← hx_def] at hpκ ⊢
  obtain ⟨mm, hmm⟩ : ∃ mm : parabolicLeviPointSubgroup p l, mm = h.projection pp := ⟨_, rfl⟩
  rw [← hmm]
  obtain ⟨m', hm'⟩ : ∃ m' : rationalPoints M,
      m' = (parabolicLeviPointHomeomorph r).symm mm := ⟨_, rfl⟩
  have hmm' : parabolicLeviPointHomeomorph r m' = mm := by
    rw [hm']
    exact (parabolicLeviPointHomeomorph r).apply_symm_apply mm
  obtain ⟨Hm, hHm⟩ : ∃ Hm : RealTorusSpace.Vstar A →ₗ[ℝ] ℝ,
      Hm = (RealTorusSpace.pair A).flip (w m') := ⟨_, rfl⟩
  -- memberships
  have hx1 : x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))).rationalPoints := by
    rw [hx_def]
    exact hσŪ qq
  have hU'eq : U'pt = (Dynamic.unipotent (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫
      a ≫ l ≫ p)).rationalPoints := by
    rw [hU'pt, r'.range_comp_radical_eq hn', ← hLevi]
  have hx2 : x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫
      a ≫ l ≫ p)).rationalPoints := by
    rw [hx_def]
    exact hU'eq.le (σ qq).2
  have hκ : (κ : rationalPoints G) ∈ (K : Set (rationalPoints G)) := κ.2
  have hUeq : Upt = (Dynamic.unipotent (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
      a ≫ l ≫ p)).rationalPoints := by
    rw [hUpt, r.range_comp_radical_eq hn]
  have hu : (mm : rationalPoints G)⁻¹ * (pp : rationalPoints G) ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)).rationalPoints := by
    rw [hmm]
    exact hUeq.le (h.projection_inv_mul_mem pp)
  have hxm : x = (mm : rationalPoints G) * ((mm : rationalPoints G)⁻¹ * (pp : rationalPoints G)) *
      (κ : rationalPoints G) := by
    rw [hpκ]
    group
  have hm'map : rationalPoints.map (l ≫ p) m' = (mm : rationalPoints G) := by
    have h1 := parabolicLeviPointHomeomorph_apply_coe r m'
    rw [hmm'] at h1
    exact h1.symm
  -- the height bound
  have hqline : rationalPoints.map (Dynamic.Affine.parabolicHom
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))
      (rationalPoints.map (hPlam.factorHom (l ≫ p) hlelam) m') = (mm : rationalPoints G) := by
    change (m' ≫ (hPlam.factorHom (l ≫ p) hlelam).hom.hom) ≫
      (Dynamic.Affine.parabolicHom _).hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hglam]
    exact hm'map
  have hheight := hline x mm _ κ _ hx1 hu hκ hxm hqline
  have hψ : Real.log (LocalField.residueNormalizedAbsoluteValue F
      (rationalCharacterEval ξl (rationalPoints.map (hPlam.factorHom (l ≫ p) hlelam) m') : F)) =
      Hm ψl := by
    have h1 := (hw m').1 ξM
    rw [hξM, rationalCharacterEval_characterRestrict] at h1
    rw [hHm, LinearMap.flip_apply, hψl, hξM]
    exact h1.symm
  -- the logarithms of the half modulus and of the character
  have hδlog : Real.log ‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
      h.levi_le_normalizer mm : ℂ)‖ = Hm νδ := by
    have h1 := (hw m').2 (parabolicLeviHalfModulus r h hU)
      (rationalCommonNormKernel_le_ker_parabolicLeviHalfModulus r hn hUpt hG h hU)
    rw [parabolicLeviHalfModulus_apply, hmm'] at h1
    rw [h1, hHm, LinearMap.flip_apply, hνδ]
    rfl
  obtain ⟨χM, hχM⟩ : ∃ χM : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul),
      χM = (parabolicLeviUnramifiedCharactersHomeomorph r).symm χ := ⟨_, rfl⟩
  have hχlog : Real.log ‖(χ.val mm : ℂ)‖ = Hm (νf χ) := by
    have h1 := (hw m').2 χM.val.toMonoidHom χM.2
    have h2 : (χM.val m' : ℂˣ) = χ.val mm := by
      rw [hχM, parabolicLeviUnramifiedCharactersHomeomorph_symm_apply, hmm']
    have h3 : χM.val.toMonoidHom.comp (rationalPoints.map a) =
        χ.val.toMonoidHom.comp (parabolicSplitComponentPointHom r) := by
      rw [hχM]
      rfl
    change Real.log ‖((χM.val m' : ℂˣ) : ℂ)‖ = _ at h1
    rw [h2, h3] at h1
    rw [h1, hHm, LinearMap.flip_apply, hνf]
  -- the two cone hypotheses
  have hcone1 : ∀ mu : cocharacterLattice A, (∀ α ∈ relativeRoots (a ≫ l ≫ p),
      latticePairing A α r.splitComponentCocharacter < 0 →
        0 < latticePairing A α r'.splitComponentCocharacter → 0 ≤ latticePairing A α mu) →
      -c mu ≤ Hm ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (positiveWeightCharacter (a ≫ l ≫ p) mu)) := by
    intro mu hmu
    have hmu' : IsOppositeIntersectionAdmissible (a ≫ l ≫ p) r.splitComponentCocharacter
        r'.splitComponentCocharacter mu := hmu
    have hc : c mu = -Real.log (Cf mu hmu') := dite_eq_left hmu'
    rw [hc, neg_neg, ← hresf mu hmu', hHm, LinearMap.flip_apply, (hw m').1 (ξf mu hmu')]
    have h1 := hlowf mu hmu' x pp κ hx1 hx2 hκ hpκ
    rw [← hmm, ← hm'] at h1
    exact Real.log_le_log (hCf mu hmu') h1
  have hcone2 : ∀ ξ : rationalCharacters G, Hm ((1 : ℝ) ⊗ₜ[ℤ]
      (rationalCharacters.equivCharacterLattice A) (characterRestrict (a ≫ l ≫ p) ξ)) = 0 := by
    intro ξ
    rw [characterRestrict_comp, AddMonoidHom.comp_apply, hHm, LinearMap.flip_apply, (hw m').1,
      rationalCharacterEval_characterRestrict, hm'map]
    have h1 := abs_rationalCharacterEval_projection_eq_one r hn hUpt h (K := K.toSubgroup) hK ξ _
      hx1 pp κ.2 hpκ
    rw [← hmm] at h1
    rw [h1, Real.log_one]
  -- the region and the size term
  have hν := (mem_parabolicPointUnramifiedIntertwiningRegion r r' hLevi hn hQ hv B (R₀ + Sδ)
    χ).1 hχ.1
  have hreg : ∀ α ∈ relativeRoots (a ≫ l ≫ p),
      0 < latticePairing A α r.splitComponentCocharacter →
        latticePairing A α r'.splitComponentCocharacter < 0 →
          R₀ < B (νf χ + νδ) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    intro α hα h1 h2
    have h3 : R₀ + Sδ < B (νf χ) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
      rw [hνf]
      exact hν α hα h1 h2
    have h4 : |B νδ ((1 : ℝ) ⊗ₜ[ℤ] α)| ≤ Sδ := by
      rw [hSδ, hSeq]
      exact Finset.single_le_sum (f := fun β => |B νδ ((1 : ℝ) ⊗ₜ[ℤ] β)|)
        (fun _ _ => abs_nonneg _) ((hRA α).2 hα)
    rw [map_add, LinearMap.add_apply]
    have h5 := neg_abs_le (B νδ ((1 : ℝ) ⊗ₜ[ℤ] α))
    linarith
  have hmain := hcone Hm hcone1 hcone2 (νf χ + νδ) hreg
  have hSadd : relativeRootAbsSum (a ≫ l ≫ p) B (νf χ + νδ) ≤
      relativeRootAbsSum (a ≫ l ≫ p) B (νf χ) + Sδ := by
    rw [hSδ, hSeq, hSeq, hSeq, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [map_add, LinearMap.add_apply]
    exact abs_add_le _ _
  have hSnn : 0 ≤ relativeRootAbsSum (a ≫ l ≫ p) B (νf χ + νδ) := by
    rw [hSeq]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS1 : relativeRootAbsSum (a ≫ l ≫ p) B (νf χ) < S₀ + 1 := hχ.2
  have hKb : K₀ * (1 + relativeRootAbsSum (a ≫ l ≫ p) B (νf χ + νδ)) ≤ K₁ := by
    rw [hK₁]
    calc K₀ * (1 + relativeRootAbsSum (a ≫ l ≫ p) B (νf χ + νδ))
        ≤ max K₀ 0 * (1 + relativeRootAbsSum (a ≫ l ≫ p) B (νf χ + νδ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      _ ≤ max K₀ 0 * (2 + S₀ + Sδ) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
  have hcone' : Hm (νf χ + νδ) ≤ -(sp * D) * |Hm ψl| + K₁ := by
    linarith
  have hδpos : 0 < ‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
      h.levi_le_normalizer mm : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hχpos : 0 < ‖(χ.val mm : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  calc ‖(HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
        h.levi_le_normalizer mm : ℂ)‖ * (‖(χ.val mm : ℂ)‖ * 1)
      = Real.exp (Hm (νf χ + νδ)) := by
        rw [mul_one, map_add, Real.exp_add, ← hδlog, ← hχlog, Real.exp_log hδpos,
          Real.exp_log hχpos, mul_comm]
    _ ≤ Real.exp (K₁ + sp * Real.log C₃) *
          MatrixRepresentation.rationalMatrixNorm F ρ₀ x ^ (-s) :=
        exp_le_of_cone_height hsp hssp hC₃ (MatrixRepresentation.one_le_rationalMatrixNorm F ρ₀ x)
          hcone' hψ hheight

end Host

/-- **The character-decay input from the relative root system.** The relative root system
statement and the detection of nonzero rational characters by central split tori imply
`ParabolicCharacterDecayInput`. -/
theorem parabolicCharacterDecayInput_of_statements (hRS : RelativeRootSystemStatement.{u})
    (hS : CentralSplitTorusCharacterStatement.{u}) : ParabolicCharacterDecayInput.{u} := by
  intro F _ _ _ _ G hG _ _ _ A M P P' Q U U' V _ _ p l p' l' a n n' q v r r' hLevi hn hn' hQ hv
    _ B C Ppt Mpt Upt U'pt h hU K hK _
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hG.connectedSpace
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
    let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := r.isCompatible.levi.isClosedSubgroup.mono
    let := r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ l ≫ p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
  obtain ⟨N, ρ₀, hρ₀⟩ := exists_isClosedSubgroup_fin_succ G
  refine ⟨N, ρ₀, hρ₀, ?_⟩
  exact parabolicOppositeCharacterDecay_of_statements r r' hLevi hn hn' hQ hv rfl rfl hRS hS hG
    h hU K hK ρ₀ hρ₀

/-- **The squared-modulus input from the relative root system.** The relative root system
statement and the detection of nonzero rational characters by central split tori imply
`ParabolicSquaredModulusInput`, by `parabolic_squaredModulusCompatibility_of_structural`. -/
theorem parabolicSquaredModulusInput_of_statements (hRS : RelativeRootSystemStatement.{u})
    (hS : CentralSplitTorusCharacterStatement.{u}) : ParabolicSquaredModulusInput.{u} := by
  intro F _ _ _ _ G hG _ _ _ A M P P' U U' _ _ p l p' l' a n n' r r' hLevi hn hn'
    Ppt P'pt Mpt Upt U'pt h hU h' hU' _ _ _ _
  have := hG.isAffineHom
  have := hG.smooth
  exact parabolic_squaredModulusCompatibility_of_structural r r' hRS hS hG hLevi hn hn'
    h hU h' hU'

/-- **The conditional intertwining theorem from the remaining structural statements.**
Coefficientwise moderate growth (Waldspurger I.4.4), the relative root system statement and
the detection of nonzero rational characters by central split tori imply
`ConditionalParabolicIntertwiningStatement`. -/
theorem conditionalParabolicIntertwiningStatement_of_statements
    (hcoeff : RationalCoefficientModerateGrowthStatement.{u, uV})
    (hRS : RelativeRootSystemStatement.{u}) (hS : CentralSplitTorusCharacterStatement.{u}) :
    ConditionalParabolicIntertwiningStatement.{u, uV, uW} :=
  conditionalParabolicIntertwiningStatement_of_characterDecay
    (rationalFiniteLengthModerateGrowth_of_coefficientGrowth hcoeff)
    (parabolicSquaredModulusInput_of_statements hRS hS)
    (parabolicCharacterDecayInput_of_statements hRS hS)

end Langlands.Plancherel
