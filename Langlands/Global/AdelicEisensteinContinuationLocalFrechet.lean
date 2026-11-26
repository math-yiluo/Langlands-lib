import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.AdelicEisensteinScalarEquations
import Langlands.Automorphic.GroupSchemeUniformGrowthJointEvaluation

/-! # Local Fréchet representations of Eisenstein continuations

Consequences of the meromorphic continuation of Eisenstein series
(`EisensteinMeromorphicContinuationStatement`, Bernstein–Lapid Theorem 2.3 (1) in the Fréchet
form of their Corollary 8.6) for an arbitrary pointwise continuation `E` with domain `D`:

* `exists_local_frechet_of_eisensteinContinuation`: near every point of a linear chart, `E` is
  the underlying function of a meromorphic function with values in a space `𝔉^R_L` of uniform
  moderate growth, on an open dense part of the chart;
* `continuousOn_of_local_frechet`: where `E` is holomorphic in the parameter, it is jointly
  continuous in the parameter and the point of `G(𝔸)`;
* `exists_isMeromorphicOn_rightConvolution`: the right convolutions `λ ↦ R(ψ)(E λ)(g)` by a
  continuous compactly supported `ψ` are meromorphic, with one domain for all `g`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A meromorphic function remains meromorphic with a smaller open dense domain of holomorphy. -/
theorem IsMeromorphicOn.mono_of_isOpen_of_dense {f : M → V} {U U' : Set M}
    (hf : IsMeromorphicOn I f U) (hU'o : IsOpen U') (hU'd : Dense U') (hU'U : U' ⊆ U) :
    IsMeromorphicOn I f U' := by
  obtain ⟨-, -, hhol, hloc⟩ := hf
  refine ⟨hU'o, hU'd, fun κ => (hhol κ).mono hU'U, fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, hgh⟩ := hloc s₀
  exact ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, fun s hs => hgh s ⟨hU'U hs.1, hs.2⟩⟩

end Langlands.Analysis.Meromorphic

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Generic

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {hN : 0 < N} {hrho : IsClosedSubgroup rho}

/-- A family `Φ s` of functions on `G(𝔸)` which is the underlying function of a meromorphic
`𝔉^R_L`-valued function on its domain of holomorphy is jointly continuous near every point of
`W` at which `s ↦ Φ s g` is holomorphic for every `g`. -/
theorem continuousOn_of_local_frechet {m : ℕ} {W : TopologicalSpace.Opens (Fin m → ℂ)}
    {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}
    {f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L} {Df : Set W}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f Df)
    {Φ : (Fin m → ℂ) → AdelicGroupPoints F G → ℂ}
    (hfΦ : ∀ t ∈ Df, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) = Φ t)
    {O : Set (Fin m → ℂ)} (hO : IsOpen O) (hΦ : ∀ g, DifferentiableOn ℂ (fun s => Φ s g) O)
    {s₀ : Fin m → ℂ} (hs₀W : s₀ ∈ W) (hs₀O : s₀ ∈ O) :
    ∃ T : Set (Fin m → ℂ), IsOpen T ∧ s₀ ∈ T ∧ T ⊆ O ∧
      ContinuousOn (fun q : (Fin m → ℂ) × AdelicGroupPoints F G => Φ q.1 q.2) (T ×ˢ univ) := by
  classical
  obtain ⟨hDfo, hDfd, -, hloc⟩ := hf
  obtain ⟨W', hW'o, hW'c, hsW', g, h, hg, ⟨t₁, ht₁, hg₁⟩, hh, hgh⟩ := hloc ⟨s₀, hs₀W⟩
  set V' : Set (Fin m → ℂ) := Subtype.val '' W' with hV'
  have hV'o : IsOpen V' := W.isOpen.isOpenMap_subtype_val _ hW'o
  have hV'c : IsPreconnected V' :=
    (hW'c.image _ continuous_subtype_val.continuousOn).isPreconnected
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hV'o.inter hO) s₀ ⟨⟨_, hsW', rfl⟩, hs₀O⟩
  set T := Metric.ball s₀ ε
  have hTV' : T ⊆ V' := fun s hs => (hεsub hs).1
  have hTO : T ⊆ O := fun s hs => (hεsub hs).2
  refine ⟨T, Metric.isOpen_ball, Metric.mem_ball_self hε, hTO, ?_⟩
  let q : (Fin m → ℂ) → ℂ := extendOpens (B := W) g
  let a : (Fin m → ℂ) → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L :=
    extendOpens (B := W) h
  have hqV' : DifferentiableOn ℂ q V' := differentiableOn_extendOpens hW'o hg
  have hqne : ∃ s ∈ T, q s ≠ 0 :=
    exists_ne_zero_of_differentiableOn hV'o hV'c hqV'
      ⟨t₁, ⟨t₁, ht₁, rfl⟩, by simpa [q, extendOpens_coe] using hg₁⟩ Metric.isOpen_ball hTV'
      ⟨s₀, Metric.mem_ball_self hε⟩
  have ha : ∀ κ : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ,
      DifferentiableOn ℂ (fun s => κ (a s)) T := by
    intro κ
    have hcomp : (fun s => κ (a s)) = extendOpens (B := W) (fun t => κ (h t)) := by
      funext s
      simp only [a, extendOpens]
      split_ifs <;> simp
    rw [hcomp]
    exact (differentiableOn_extendOpens hW'o (hh κ)).mono hTV'
  -- the identity `q s * Φ s y = ev_y (a s)` on a dense part of `T`, then on `T`
  have hdense : T ⊆ closure (T ∩ Subtype.val '' (Df ∩ W')) := by
    intro s hs
    refine Metric.isOpen_ball.inter_closure ⟨hs, ?_⟩
    obtain ⟨t, ht, rfl⟩ := hTV' hs
    have ht' : t ∈ closure (W' ∩ Df) := hW'o.inter_closure ⟨ht, hDfd t⟩
    rw [inter_comm] at ht'
    exact image_closure_subset_closure_image continuous_subtype_val ⟨t, ht', rfl⟩
  have heq : ∀ s ∈ T, ∀ y, q s * Φ s y =
      1 * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (a s) y := by
    intro s hs y
    have hL : ContinuousOn (fun s => q s * Φ s y) T :=
      (hqV'.mono hTV').continuousOn.mul ((hΦ y).mono hTO).continuousOn
    have hR : ContinuousOn (fun s => 1 * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc
        hN hrho R L (a s) y) T := by
      refine continuousOn_const.mul ?_
      exact (ha (uniformGrowthEvalCLM y)).continuousOn
    refine EqOn.of_subset_closure ?_ hL hR inter_subset_left hdense hs
    rintro _ ⟨-, ⟨t, ⟨htD, htW'⟩, rfl⟩⟩
    simp only [q, a, extendOpens_coe, one_mul]
    rw [← hgh t ⟨htD, htW'⟩, ← hfΦ t htD]
    exact (map_smul (uniformGrowthEvalCLM (hN := hN) (hrho := hrho) (R := R) (L := L)
      (hsmooth := hsmooth) (hcalc := hcalc) y) (g t) (f t)).symm
  exact UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval F G rho hsmooth hcalc hN hrho R L
    Metric.isOpen_ball (convex_ball s₀ ε).isPreconnected (hqV'.mono hTV') hqne continuousOn_const
    ha (fun y => (hΦ y).mono hTO) heq

variable [LocallyOfFiniteType G.X.hom]

/-- Right convolutions by a continuous compactly supported `ψ` of a family with local
`𝔉^R_L`-valued meromorphic representations are meromorphic with one domain of holomorphy. -/
theorem exists_isMeromorphicOn_rightConvolution {m : ℕ}
    {Φ : (Fin m → ℂ) → AdelicGroupPoints F G → ℂ}
    (hloc : ∀ s₀ : Fin m → ℂ, ∃ W : TopologicalSpace.Opens (Fin m → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))
        (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (Df : Set W),
        IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f Df ∧
        ∀ t ∈ Df, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) = Φ t)
    {ψ : AdelicGroupPoints F G → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∃ U : Set (Fin m → ℂ), ∀ g : AdelicGroupPoints F G,
      IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun s => rightConvolution F G ψ (Φ s) g) U := by
  refine exists_isMeromorphicOn_of_local fun s₀ => ?_
  obtain ⟨W, hs₀, R, L, f, Df, hf, hfD⟩ := hloc s₀
  refine hasLocalMeromorphicData_of_isMeromorphicOn hf
    (fun g => rightConvolutionEvalCLM F G rho hN hrho hsmooth hcalc R L hψc hψs g)
    (fun t ht g => ?_) hs₀
  rw [rightConvolutionEvalCLM_apply, hfD t ht]

end Generic

section Eisenstein

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Given the meromorphic continuation of Eisenstein series, every pointwise continuation `E`
of the Eisenstein series of an automorphic form on `U(𝔸) M(F) \ G(𝔸)`, meromorphic in
coordinates with domain `D`, is near every point of a linear chart the underlying function of a
meromorphic function with values in a space `𝔉^R_L` of uniform moderate growth, on the domain of
holomorphy of that function. -/
theorem exists_local_frechet_of_eisensteinContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {m : ℕ} (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin m → ℂ) :
    ∃ W : TopologicalSpace.Opens (Fin m → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))
        (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (Df : Set W),
        IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f Df ∧
        ∀ t ∈ Df, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) =
          E (e₀ t) := by
  classical
  have := finiteDimensional_complexCharacterParameter r hG
  obtain ⟨Ea, ⟨R₀, hR₀⟩, hloc⟩ :=
    hMero F G P M U A p iU l a r hA hT hG hUR K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  have hdata : ∀ s₁ : Fin m → ℂ,
      HasLocalMeromorphicData (fun (g : AdelicGroupPoints F G) s => Ea (e₀ s) g) s₁ := by
    intro s₁
    obtain ⟨W, hs₁, R, L, -, f, Df, hf, hfD⟩ := hloc m e₀ s₁
    refine hasLocalMeromorphicData_of_isMeromorphicOn hf (fun g => uniformGrowthEvalCLM g)
      (fun t ht g => ?_) hs₁
    change UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) g = _
    rw [(hfD t ht).1]
  obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_of_local hdata
  have hEa : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => Ea lam g) (e₀ '' U₀) := fun g =>
    isMeromorphicInCoordinatesOn_of_coordinates e₀ (by
      rw [e₀.injective.preimage_image]
      exact hU₀ g)
  obtain ⟨R₁, hR₁⟩ := hreg
  have heq : ∀ g, EqOn (fun lam => E lam g) (fun lam => Ea lam g) (D ∩ e₀ '' U₀) := fun g =>
    r.eqOn_of_regularParameter hA hT hG (hE g) (hEa g) (max R₁ R₀) fun lam hlam => by
      rw [hR₁ lam (isRegularParameter_mono r hA hT (le_max_left _ _) hlam),
        hR₀ lam (isRegularParameter_mono r hA hT (le_max_right _ _) hlam)]
  obtain ⟨W, hs₀, R, L, -, f, Df, hf, hfD⟩ := hloc m e₀ s₀
  have hO := ((hE 1).isOpenDenseInCoordinates.inter (hEa 1).isOpenDenseInCoordinates) m e₀
  refine ⟨W, hs₀, R, L, f, Df ∩ Subtype.val ⁻¹' (e₀ ⁻¹' (D ∩ e₀ '' U₀)), ?_, ?_⟩
  · exact hf.mono_of_isOpen_of_dense (hf.1.inter (hO.1.preimage continuous_subtype_val))
      (hf.2.1.inter_of_isOpen_left (hO.2.preimage W.isOpen.isOpenMap_subtype_val) hf.1)
      inter_subset_left
  · rintro t ⟨htD, htU⟩
    funext g
    rw [(hfD t htD).1]
    exact (heq g htU).symm

end Eisenstein

end Langlands.Global
