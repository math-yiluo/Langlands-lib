import Langlands.Global.AdelicEisensteinRegularAutomorphyReductionStatement
import Langlands.Global.AdelicEisensteinCommonGrowthProof
import Langlands.Global.AdelicEisensteinLinearConvergence

/-! # Automorphy of convergent Eisenstein series from automorphy of the twists

For an automorphic inducing function `φ` on `U(𝔸)M(F) \ G(𝔸)` and a maximal compact `K` with
`P(𝔸)K = G(𝔸)`, the Eisenstein series `E(φ, λ)` at sufficiently regular `λ` is smooth, left
`G(F)`-invariant, `K_∞`-finite and of moderate growth, and every element of the enveloping
algebra that annihilates the infinite slices of the twist `φ_λ` annihilates the infinite slices
of `E(φ, λ)`. Hence `E(φ, λ)` is automorphic as soon as `φ_λ` is `𝔷`-finite
(`exists_regular_eisensteinSeries_isAutomorphicFunctionOn`). For the standard parabolics of a
standard family this gives `EisensteinRegularAutomorphyReductionStatement`. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField Filter Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints RepresentationGrowth

section TermwiseDerivatives

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "H" => InfiniteAdelicGroupPoints F G
local notation "S" => InfinitePlotSmoothFunctions F G
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "E" => smoothModel F d
local notation "IH" => 𝓘(ℝ, E)

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1600000 in
/-- Termwise differentiation of a series of plot-smooth functions on the archimedean points.
If every enveloping derivative of the terms `f i` is bounded by `C_a m_i w` with a summable
`m ≥ 0` and a continuous `w`, the pointwise sum is plot-smooth and each of its enveloping
derivatives is the sum of the derivatives of the terms. -/
theorem exists_plotSmooth_tsum_envelopingAction {Idx : Type v} (f : Idx → S)
    (m : Idx → ℝ) (hm : Summable m) (hm₀ : ∀ i, 0 ≤ m i) (w : H → ℝ) (hw : Continuous w)
    (hbound : ∀ a : UEA, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (f i)).val x‖ ≤ C * m i * w x) :
    ∃ g : S, ∀ (a : UEA) (x : H),
      (plotSmoothEnvelopingAction F G hsmooth hcalc a g).val x =
        ∑' i, (plotSmoothEnvelopingAction F G hsmooth hcalc a (f i)).val x := by
  let := fun p : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F p
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup IH (minSmoothness ℝ 3) H := LieGroup.of_le (n := ∞) (by simp)
  let Act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let term (a : UEA) (i : Idx) (x : H) := (Act a (f i)).val x
  let value (a : UEA) (x : H) := ∑' i, term a i x
  let gen (X : E) : UEA := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
  choose C hC hterm using hbound
  have hnorm (a : UEA) (x : H) : Summable (fun i => ‖term a i x‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm a · x) ?_
    exact (hm.mul_left _).mul_right _
  have hlim (a : UEA) :
      TendstoLocallyUniformly (fun T : Finset Idx => fun x => ∑ i ∈ T, term a i x)
        (value a) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro Q hQ
    obtain ⟨B, hB⟩ := (hQ.image hw).bddAbove
    exact tendstoUniformlyOn_tsum ((hm.mul_left (C a)).mul_right B) fun i x hx =>
      (hterm a i x).trans (mul_le_mul_of_nonneg_left (hB ⟨x, hx, rfl⟩)
        (mul_nonneg (hC a) (hm₀ i)))
  have hsum :
      (∀ a, ContMDiff IH 𝓘(ℝ, ℂ) ∞ (value a)) ∧
        ∀ a X, groupDirectionalValue IH X (value a) = value (gen X * a) := by
    let partialSum (T : Finset Idx) (a : UEA) : S := ∑ i ∈ T, Act a (f i)
    have hp (T : Finset Idx) (a : UEA) :
        (partialSum T a).val = fun x => ∑ i ∈ T, term a i x := by
      funext x
      simp only [partialSum, Submodule.coe_sum, Finset.sum_apply, term]
    apply contMDiff_of_tendstoLocallyUniformly_invariantDerivatives (l := atTop)
        (fun X a => gen X * a) (f := fun T a => (partialSum T a).val) (g := fun a => value a)
    · intro T a
      exact (isPlotSmooth_iff_contMDiff F G hsmooth (partialSum T a).val).mp
        (partialSum T a).property
    · intro T a X
      change (plotSmoothDifferential F G hsmooth X (partialSum T a)).val =
        (partialSum T (gen X * a)).val
      rw [← plotSmoothEnvelopingAction_real_generator F G hsmooth hcalc X]
      change (Act (gen X) (partialSum T a)).val = _
      simp only [partialSum, map_sum, map_mul, Module.End.mul_apply]
    · intro a
      simpa only [hp] using hlim a
  let series : UEA →ₗ[ℂ] S :=
    { toFun := fun a => ⟨value a, (isPlotSmooth_iff_contMDiff F G hsmooth (value a)).mpr
        (hsum.1 a)⟩
      map_add' := fun a c => Subtype.ext (funext fun x => by
        change (∑' i, term (a + c) i x) = (∑' i, term a i x) + (∑' i, term c i x)
        rw [← (hnorm a x).of_norm.tsum_add (hnorm c x).of_norm]
        apply tsum_congr
        intro i
        simp only [term, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply])
      map_smul' := fun z a => Subtype.ext (funext fun x => by
        change (∑' i, term (z • a) i x) = z * (∑' i, term a i x)
        rw [← tsum_mul_left]
        apply tsum_congr
        intro i
        simp only [term, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
          smul_eq_mul]) }
  have hgen (X : E) (a : UEA) : Act (gen X) (series a) = series (gen X * a) := by
    apply Subtype.ext
    change (plotSmoothEnvelopingAction F G hsmooth hcalc (gen X) (series a)).val = _
    rw [plotSmoothEnvelopingAction_real_generator]
    exact hsum.2 a X
  have hgenC (Z : ℂ ⊗[ℝ] GroupLieAlgebra IH H) (a : UEA) :
      Act (UniversalEnvelopingAlgebra.ι ℂ Z) (series a) =
        series (UniversalEnvelopingAlgebra.ι ℂ Z * a) := by
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hz, map_smul, map_smul, LinearMap.smul_apply, smul_mul_assoc]
      change z • Act (gen X) (series a) = series (z • (gen X * a))
      rw [map_smul, hgen]
    | add Z W hZ hW => simp only [map_add, LinearMap.add_apply, add_mul, hZ, hW]
  have hact (a : UEA) : ∀ c : UEA, Act a (series c) = series (a * c) := by
    obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] GroupLieAlgebra IH H)) a
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      intro c
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply,
        Module.End.one_apply, smul_mul_assoc, one_mul]
    | «ι» Z => exact hgenC Z
    | mul v w hv hw =>
      intro c
      simp only [map_mul, Module.End.mul_apply, hw, hv, mul_assoc]
    | add v w hv hw =>
      intro c
      simp only [map_add, LinearMap.add_apply, add_mul, hv, hw]
  refine ⟨series 1, fun a x => ?_⟩
  rw [hact, mul_one]
  rfl

end TermwiseDerivatives

section RightTranslation

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)

/-- Right translation by an element of the Iwasawa compact preserves the existence of
compact summable majorants for the Eisenstein terms. -/
theorem AdelicGroupPoints.IsIwasawaCompact.rightTranslate_mem_compactMajorantSections
    {φ : AdelicGroupPoints F G → ℂ} (hφ : φ ∈ hK.compactMajorantSections lam)
    {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    (fun g => φ (g * k)) ∈ hK.compactMajorantSections lam := by
  intro C hC
  obtain ⟨u, hu, hb⟩ := hφ ((fun g => g * k) '' C) (hC.image (continuous_id.mul continuous_const))
  refine ⟨u, hu, fun c x hx => ?_⟩
  have hterm : hK.eisensteinTerm (fun g => φ (g * k)) lam x c =
      hK.eisensteinTerm φ lam (x * k) c := by
    simp only [IsIwasawaCompact.eisensteinTerm, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower]
    rw [← mul_assoc, hK.height_mul_right _ hk]
  rw [hterm]
  exact hb c (x * k) ⟨x, hx, rfl⟩

/-- If `φ` is finite under an archimedean subgroup `Kinf` whose image lies in `K` and its
Eisenstein terms have compact summable majorants at `λ`, then `E(φ, λ)` is `Kinf`-finite: its
right translates are the Eisenstein series of the right translates of `φ`, and the series is
linear on the finite-dimensional span of these translates. -/
theorem AdelicGroupPoints.IsIwasawaCompact.eisensteinSeries_isInfiniteSubgroupFiniteFunction
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (hKinf : ∀ k ∈ Kinf, ofInfinite F G k ∈ K) {φ : AdelicGroupPoints F G → ℂ}
    (hφK : IsInfiniteSubgroupFiniteFunction F G Kinf φ)
    (hφ : φ ∈ hK.compactMajorantSections lam) :
    IsInfiniteSubgroupFiniteFunction F G Kinf (hK.eisensteinSeries φ lam) := by
  let V := Submodule.span ℂ (Set.range fun k : Kinf =>
    fun g : AdelicGroupPoints F G => φ (g * ofInfinite F G k))
  have hV : V ≤ hK.compactMajorantSections lam := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact hK.rightTranslate_mem_compactMajorantSections lam hφ (hKinf k k.2)
  let V' := V.comap (hK.compactMajorantSections lam).subtype
  have : FiniteDimensional ℂ V := hφK
  have : FiniteDimensional ℂ V' :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hV).symm
  let W := V'.map (hK.eisensteinSeriesLinear lam)
  have : FiniteDimensional ℂ W := inferInstance
  unfold IsInfiniteSubgroupFiniteFunction
  refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  have hkK : ofInfinite F G k ∈ K := hKinf k k.2
  refine ⟨⟨fun g => φ (g * ofInfinite F G k), hV (Submodule.subset_span ⟨k, rfl⟩)⟩,
    Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext g
  change hK.eisensteinSeries (fun g => φ (g * ofInfinite F G k)) lam g =
    hK.eisensteinSeries φ lam (g * ofInfinite F G k)
  rw [← hK.eisensteinSeries_parameterRightAction lam (ofInfinite F G k) φ g]
  congr 1
  funext x
  exact (hK.parameterRightAction_compact lam _ hkK φ x).symm

end RightTranslation

section RegularSeries

set_option maxHeartbeats 5000000 in
/-- Regular Eisenstein series of an automorphic inducing function. In the setting of
`EisensteinCommonGrowthStatement` there is `R₀` such that for every `R₀`-regular `λ` the series
`E(φ, λ)` is smooth and of moderate growth, its terms have compact summable majorants, and every
element of the enveloping algebra annihilating all infinite slices of the twist `φ_λ` annihilates
all infinite slices of `E(φ, λ)`. -/
theorem exists_regular_eisensteinSeries_slices (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ)
    (hmax : IsMaximalCompactSubgroup F G K)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
      IsAdelicSmoothFunction F G (hK.eisensteinSeries φ lam) ∧
      HasModerateGrowthFunction F G rho (hK.eisensteinSeries φ lam) ∧
      φ ∈ hK.compactMajorantSections lam ∧
      ∀ D : AdelicEnvelopingAlgebra F G hsmooth,
        (∀ (b : FiniteAdelicGroupPoints F G)
          (h : functionInfiniteSlice F G (hK.parameterTwist φ lam) b ∈
            InfinitePlotSmoothFunctions F G),
          plotSmoothEnvelopingAction F G hsmooth hcalc D ⟨_, h⟩ = 0) →
        ∀ (b : FiniteAdelicGroupPoints F G)
          (h : functionInfiniteSlice F G (hK.eisensteinSeries φ lam) b ∈
            InfinitePlotSmoothFunctions F G),
          plotSmoothEnvelopingAction F G hsmooth hcalc D ⟨_, h⟩ = 0 := by
  let : Smooth G.X.hom := hG.smooth
  let Points := AdelicGroupPoints F G
  let FinPts := FiniteAdelicGroupPoints F G
  let InfPts := InfiniteAdelicGroupPoints F G
  let S := InfinitePlotSmoothFunctions F G
  let UEA := AdelicEnvelopingAlgebra F G hsmooth
  let height := adelicHeight F G rho
  let norm₀ := adelicSourceNorm F G rho
  have hH₁ (g : Points) : 1 ≤ height g := one_le_adelicHeight F G rho hN g
  have hH₀ (g : Points) : 0 ≤ height g := zero_le_one.trans (hH₁ g)
  have hHpos (g : Points) : 0 < height g := zero_lt_one.trans_le (hH₁ g)
  obtain ⟨_, hφs, L₀, hL₀, hφL⟩ := hφ.2.1
  obtain ⟨e₀, he₀, hderφ⟩ := exists_uniformGrowth_functionInfiniteSlices F G hsmooth hcalc rho hN hG
    (K.comap (ofInfinite F G).toMonoidHom) hmax.isMaximalCompact_comap_ofInfinite
    φ hφs hφ.2.2.1 hφ.2.2.2.1 hφ.2.2.2.2
  have hH := hK.hasSmoothHeightPairings_of_maximal hmax hsmooth
  let KF := K.map (finite F G).toMonoidHom
  let L := L₀ ⊓ KF
  have hLo : IsOpen (L : Set FinPts) :=
    hL₀.inter (IsMaximalCompactSubgroup.isOpen_finite F G K hmax)
  have hLK (s : FinPts) (hs : s ∈ L) : ofFinite F G s ∈ K := by
    obtain ⟨k, hk, rfl⟩ := show s ∈ KF from hs.2
    exact ((hmax.mem_iff k).mp hk).2
  obtain ⟨nσ, j, σ, hstab⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  obtain ⟨B, d₀, hB, hd₀, hrep⟩ := exists_polynomial_rationalCoset_representatives rho σ j hG
    r.isCompatible.parabolic hstab
  choose rep hrepq hreph using hrep
  let C := ParabolicRationalCosets F p
  let proj := parabolicRationalProjectiveEmbedding σ j hstab
  let Hc (c : C) := (proj c).mulHeight
  let representative (c : C) := rational F G (rep c)
  have hHc (c : C) : 0 < Hc c := (proj c).mulHeight_pos
  obtain ⟨t, ht, hsum⟩ := summable_projectivization_mulHeight_rpow F (Fin (nσ + 1))
  let m (c : C) := Hc c ^ (-t)
  have hm : Summable m := by
    change Summable ((fun y : Projectivization F (Fin (nσ + 1) → F) => y.mulHeight ^ (-t)) ∘ proj)
    exact (hsum t le_rfl).comp_injective proj.injective
  have hm₀ (c : C) : 0 ≤ m c := Real.rpow_nonneg (hHc c).le _
  let decay := d₀ * e₀ + t
  obtain ⟨R₀, hdec⟩ := hK.exists_norm_heightPower_rational_le_projectiveHeight r hA hT hG σ j
    hstab decay (add_nonneg (mul_nonneg hd₀ he₀) ht)
  refine ⟨R₀, fun lam hsreg => ?_⟩
  let e₁ : (Fin 1 → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P :=
    (LinearMap.toSpanSingleton ℂ _ lam).comp (LinearMap.proj 0)
  let s₁ : Fin 1 → ℂ := fun _ => 1
  have he₁ : e₁ s₁ = lam := by
    simp [e₁, s₁]
  obtain ⟨B₁, d₁, hB₁, _, htranslation⟩ := hK.exists_uniform_heightPower_mul_le rho hN hrho
    e₁ (Bornology.isBounded_singleton (x := s₁))
  let R₁ := e₀ + d₁
  obtain ⟨B₂, hB₂, hbase⟩ := hdec 1 e₁ {s₁} isCompact_singleton (by
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, he₁]
    exact hsreg)
  have hparam (c : C) (g : Points) :
      ‖hK.heightPower lam (representative c * g)‖ ≤
        B₁ * height g ^ d₁ * (B₂ * Hc c ^ (-decay)) := by
    have hb := hbase (rep c) s₁ (Set.mem_singleton s₁)
    have htr := htranslation s₁ (Set.mem_singleton s₁) (representative c) g
    rw [he₁] at hb htr
    change ‖hK.heightPower lam (representative c)‖ ≤ B₂ * (proj (Quotient.mk _
      ⟨representative c, ⟨rep c, rfl⟩⟩ : C)).mulHeight ^ (-decay) at hb
    rw [hrepq c] at hb
    exact htr.trans
      (mul_le_mul_of_nonneg_left hb (mul_nonneg hB₁.le (Real.rpow_nonneg (hH₀ g) _)))
  have hrepGrowth (c : C) (g : Points) :
      height (representative c * g) ^ e₀ ≤ B ^ e₀ * Hc c ^ (d₀ * e₀) * height g ^ e₀ := by
    have hrepresentative : height (representative c) ≤ B * Hc c ^ d₀ := by
      simpa only [adelicHeightAtLeastOne_eq hN] using hreph c
    have hmul : height (representative c * g) ≤ (B * Hc c ^ d₀) * height g :=
      (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_right hrepresentative (hH₀ g))
    refine (Real.rpow_le_rpow (hH₀ _) hmul he₀).trans_eq ?_
    rw [Real.mul_rpow (mul_nonneg hB.le (Real.rpow_nonneg (hHc c).le _)) (hH₀ g),
      Real.mul_rpow hB.le (Real.rpow_nonneg (hHc c).le _), Real.rpow_mul (hHc c).le]
  let twisted := hK.parameterTwistSlice hsmooth hH φ hφs lam
  let term (c : C) (b : FinPts) : S :=
    plotSmoothLeftTranslation F G (infinite F G (representative c))
      (twisted (finite F G (representative c) * b))
  have hpair (c : C) (b : FinPts) (x : InfPts) :
      pair F G (infinite F G (representative c) * x) (finite F G (representative c) * b) =
        representative c * pair F G x b := by
    conv_rhs => rw [← pair_projections F G (representative c), AdelicGroupPoints.pair_mul]
  have htermEq (c : C) (b : FinPts) (x : InfPts) :
      (term c b).val x = hK.eisensteinTerm φ lam (pair F G x b) c := by
    rw [hK.eisensteinTerm_eq_of_representative hφ.1 r.isCompatible.levi hU lam _ c
      ⟨representative c, ⟨rep c, rfl⟩⟩ (hrepq c)]
    rw [show (term c b).val x = hK.parameterTwist φ lam
      (pair F G (infinite F G (representative c) * x) (finite F G (representative c) * b))
      from rfl, hpair]
  let weight (b : FinPts) (x : InfPts) := height (pair F G x b) ^ R₁
  have hw (b : FinPts) : Continuous (weight b) :=
    ((continuous_adelicHeight F G rho hN).comp ((continuous_pair F G).comp
      (continuous_id.prodMk continuous_const))).rpow_const (fun x => Or.inl (hHpos _).ne')
  have hterms (D : UEA) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ c b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D (term c b)).val x‖ ≤ C₀ * m c * weight b x := by
    obtain ⟨C₀, hC₀, hb⟩ := hK.exists_parameterTwist_derivative_bound hmax hsmooth hcalc rho
      hH φ hφs hN e₀ hderφ lam D
    refine ⟨C₀ * B ^ e₀ * B₁ * B₂, by positivity, fun c b x => ?_⟩
    let g := pair F G x b
    have h₁ := hb (finite F G (representative c) * b) (infinite F G (representative c) * x)
    rw [hpair] at h₁
    have hτ : ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D (term c b)).val x‖ ≤
        C₀ * (height (representative c * g) ^ e₀ *
          ‖hK.heightPower lam (representative c * g)‖) := by
      simpa only [term, plotSmoothEnvelopingAction_leftTranslate F G hsmooth hcalc,
        plotSmoothLeftTranslation_apply, twisted, g] using h₁
    refine hτ.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul (hrepGrowth c g) (hparam c g) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg (hHc c).le _))
          (Real.rpow_nonneg (hH₀ g) _))) hC₀).trans_eq ?_)
    change C₀ * (B ^ e₀ * Hc c ^ (d₀ * e₀) * height g ^ e₀ *
      (B₁ * height g ^ d₁ * (B₂ * Hc c ^ (-decay)))) =
        C₀ * B ^ e₀ * B₁ * B₂ * Hc c ^ (-t) * height g ^ (e₀ + d₁)
    rw [show Hc c ^ (-t) = Hc c ^ (d₀ * e₀) * Hc c ^ (-decay) by
      rw [← Real.rpow_add (hHc c), show d₀ * e₀ + -decay = -t by dsimp [decay]; ring]]
    rw [Real.rpow_add (hHpos g)]
    ring
  choose slice hslice using fun b : FinPts =>
    exists_plotSmooth_tsum_envelopingAction F G hsmooth hcalc (fun c => term c b) m hm hm₀
      (weight b) (hw b) (fun D => by
        obtain ⟨C₀, hC₀, hb⟩ := hterms D
        exact ⟨C₀, hC₀, fun c x => hb c b x⟩)
  let series := hK.eisensteinSeries φ lam
  have hseries (b : FinPts) (x : InfPts) : (slice b).val x = series (pair F G x b) := by
    have h := hslice b 1 x
    simp only [map_one, Module.End.one_apply] at h
    rw [h]
    exact tsum_congr (fun c => htermEq c b x)
  obtain ⟨C₁, hC₁, hbound₁⟩ := hterms 1
  have hterm₁ (c : C) (g : Points) :
      ‖hK.eisensteinTerm φ lam g c‖ ≤ C₁ * m c * height g ^ R₁ := by
    have h := hbound₁ c (finite F G g) (infinite F G g)
    simp only [map_one, Module.End.one_apply] at h
    rw [htermEq, pair_projections] at h
    simpa only [weight, pair_projections] using h
  have hright (y : FinPts) (hy : y ∈ L) (g : Points) : series (g * ofFinite F G y) = series g := by
    apply tsum_congr
    intro c
    change hK.parameterTwist φ lam ((Quotient.out c : rationalSubgroup F G).val *
      (g * ofFinite F G y)) =
        hK.parameterTwist φ lam ((Quotient.out c : rationalSubgroup F G).val * g)
    rw [← mul_assoc, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.parameterTwist,
      hφL y hy.1, IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower,
      hK.height_mul_right _ (hLK y hy)]
  have hcont : Continuous series :=
    (continuous_evaluatePlotSmoothSlices F G hsmooth slice ⟨L, hLo⟩ (fun b y =>
      Subtype.ext (funext fun x => by
        rw [hseries, hseries, ← show pair F G x b * ofFinite F G y.val = pair F G x (b * y.val) by
          rw [ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]]
        exact hright y y.property _))).congr (fun g => by
          change (slice (finite F G g)).val (infinite F G g) = series g
          rw [hseries, pair_projections])
  have hsmoothSeries : IsAdelicSmoothFunction F G series := by
    refine ⟨hcont, fun b => ?_, L, hLo, hright⟩
    have heq : functionInfiniteSlice F G series b = (slice b).val :=
      funext fun x => (hseries b x).symm
    exact heq ▸ (slice b).property
  refine ⟨hsmoothSeries, ?_, ?_, ?_⟩
  · -- moderate growth, from the majorant of the terms
    let c₀ : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hc₀ : 0 ≤ c₀ := pow_nonneg (Nat.cast_nonneg _) _
    let M₀ := C₁ * (∑' c, m c) * c₀ ^ R₁
    have hM₀ : 0 ≤ M₀ :=
      mul_nonneg (mul_nonneg hC₁ (tsum_nonneg hm₀)) (Real.rpow_nonneg hc₀ _)
    refine ⟨M₀ + 1, by linarith, R₁, fun g => ?_⟩
    have hsn : Summable (fun c => ‖hK.eisensteinTerm φ lam g c‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm₁ · g)
        ((hm.mul_left _).mul_right _)
    have hsr : series g = ∑' c, hK.eisensteinTerm φ lam g c := rfl
    have hnorm₀ : 0 ≤ norm₀ g ^ R₁ := Real.rpow_nonneg (adelicSourceNorm_pos F G rho hN g).le _
    calc
      ‖series g‖ ≤ ∑' c, ‖hK.eisensteinTerm φ lam g c‖ := by
        rw [hsr]
        exact norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' c, C₁ * m c * height g ^ R₁ :=
        hsn.tsum_le_tsum (hterm₁ · g) ((hm.mul_left _).mul_right _)
      _ = C₁ * (∑' c, m c) * height g ^ R₁ := by rw [tsum_mul_right, tsum_mul_left]
      _ = M₀ * norm₀ g ^ R₁ := by
        rw [show height g = c₀ * norm₀ g from adelicHeight_eq_scalar_mul_sourceNorm F G rho _,
          Real.mul_rpow hc₀ (adelicSourceNorm_pos F G rho hN _).le]
        ring
      _ ≤ (M₀ + 1) * norm₀ g ^ R₁ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hnorm₀
  · -- compact summable majorants
    intro Q hQ
    obtain ⟨Bh, hBh⟩ := (hQ.image ((continuous_adelicHeight F G rho hN).rpow_const
      (fun g => Or.inl (hHpos g).ne') (p := R₁))).bddAbove
    refine ⟨fun c => C₁ * m c * Bh, (hm.mul_left _).mul_right _, fun c g hg => ?_⟩
    exact (hterm₁ c g).trans (mul_le_mul_of_nonneg_left (hBh ⟨g, hg, rfl⟩)
      (mul_nonneg hC₁ (hm₀ c)))
  · -- annihilators of the twist annihilate the series
    intro D hD b h
    have hsl : (⟨functionInfiniteSlice F G series b, h⟩ : S) = slice b :=
      Subtype.ext (funext fun x => (hseries b x).symm)
    rw [hsl]
    apply Subtype.ext
    funext x
    rw [hslice b D x]
    have hzero (c : C) : (plotSmoothEnvelopingAction F G hsmooth hcalc D (term c b)).val x = 0 := by
      have hz : plotSmoothEnvelopingAction F G hsmooth hcalc D
          (twisted (finite F G (representative c) * b)) = 0 :=
        hD _ (twisted (finite F G (representative c) * b)).property
      simp only [term]
      rw [plotSmoothEnvelopingAction_leftTranslate F G hsmooth hcalc, hz, map_zero]
      rfl
    simp only [hzero, tsum_zero]
    rfl

/-- Automorphy of regular Eisenstein series from `𝔷`-finiteness of the twist. In the setting of
`EisensteinCommonGrowthStatement` there is `R₀` such that for every `R₀`-regular `λ` at which the
twist `φ_λ` is `𝔷`-finite, the Eisenstein series `E(φ, λ)` is automorphic on `G(F) \ G(𝔸)`
for the archimedean part of `K` and `rho`. -/
theorem exists_regular_eisensteinSeries_isAutomorphicFunctionOn (F : Type u) [Field F]
    [NumberField F] (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ)
    (hmax : IsMaximalCompactSubgroup F G K)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
      IsCenterFiniteFunction F G hsmooth hcalc (hK.parameterTwist φ lam) →
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
        (K.comap (ofInfinite F G).toMonoidHom) rho (hK.eisensteinSeries φ lam) := by
  obtain ⟨R₀, hR₀⟩ := exists_regular_eisensteinSeries_slices F G P M U A p iU l a r hA hT hG hU
    K hK rho hN hrho hsmooth hcalc φ hmax hφ
  refine ⟨R₀, fun lam hreg hZ => ?_⟩
  obtain ⟨hs, hgrowth, hmaj, hann⟩ := hR₀ lam hreg
  obtain ⟨J, hJ, hJann⟩ := hZ
  exact ⟨eisensteinSeries_leftRationalInvariant hK hφ.1 hU r.isCompatible.levi lam, hs,
    hK.eisensteinSeries_isInfiniteSubgroupFiniteFunction lam _ (fun _ hk => hk) hφ.2.2.1 hmaj,
    ⟨J, hJ, fun z hz b h => hann z.val (fun b' h' => hJann z hz b' h') b h⟩, hgrowth⟩

end RegularSeries

/-- `ParameterTwistAutomorphyStatement` implies `EisensteinRegularAutomorphyStatement`. -/
theorem eisensteinRegularAutomorphyReduction :
    EisensteinRegularAutomorphyReductionStatement.{u} := by
  intro hTw F _ _ G _ _ _ fam I _ _ _ K hK hmax hmin hlevi N d rho hsmooth hrho Kinf r hA hT φ hφ
  have hTwφ (lam : ComplexCharacterParameter F (fam.P I)) :
      fam.IsAutomorphicOn hsmooth Kinf rho I (hK.parameterTwist φ lam) :=
    hTw F G fam I K hK hmax hmin hlevi rho hsmooth hrho φ hφ lam
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hsub : Subsingleton (AdelicGroupPoints F G) := by
      let : IsClosedImmersion rho.hom.hom.left := hrho
      let : Mono rho.hom.hom := Over.mono_of_mono_left _
      exact ⟨fun x y => rho.pointMatrix_injective _ (Subsingleton.elim _ _)⟩
    have hsubR : Subsingleton (rationalSubgroup F G) :=
      ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
    have hsubC : Subsingleton (ParabolicRationalCosets F (fam.p I)) := by
      refine ⟨fun x y => ?_⟩
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y => rw [Subsingleton.elim x y]
    refine ⟨0, fun lam _ => ?_⟩
    have hE : hK.eisensteinSeries φ lam = hK.parameterTwist φ lam := by
      funext g
      let c₀ : ParabolicRationalCosets F (fam.p I) := Quotient.mk _ 1
      unfold IsIwasawaCompact.eisensteinSeries
      rw [tsum_eq_single c₀ (fun c hc => absurd (Subsingleton.elim c c₀) hc)]
      unfold IsIwasawaCompact.eisensteinTerm
      rw [Subsingleton.elim (((Quotient.out c₀ : rationalSubgroup F G) :
        AdelicGroupPoints F G) * g) g]
    rw [hE]
    obtain ⟨_, h₂, h₃, h₄, h₅⟩ := hTwφ lam
    exact ⟨fun x _ g => by rw [Subsingleton.elim (x * g) g], h₂, h₃, h₄, h₅⟩
  · obtain ⟨R₀, hR₀⟩ := exists_regular_eisensteinSeries_isAutomorphicFunctionOn F G (fam.P I)
      (fam.M I) (fam.U I) (fam.A I) (fam.p I) (fam.iU I) (fam.l I) (fam.a I) r hA hT
      fam.connectedReductive (fam.isUnipotentRadical I) K hK rho hN hrho hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) φ hmax hφ
    exact ⟨R₀, fun lam hreg => hR₀ lam hreg (hTwφ lam).2.2.2.1⟩

end Langlands.Global
