import Langlands.Analysis.PuncturedJointContinuity
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.Global.AdelicSquareIntegrableInducedForms

/-! # Eisenstein series along a complex line of parameters

The meromorphic continuation of Eisenstein series (`EisensteinMeromorphicContinuationStatement`)
and its root-hyperplane form jointly in the parameter and the group variable
(`EisensteinJointRootHyperplaneStatement`) restrict to a complex line `s ↦ s λ₁` of parameters
that meets every root hyperplane through a point in that point only. The restriction is one
function `E(s, g)` that is the Eisenstein series for `Re s` large and that has, near every `s₀`,
a power of `s - s₀` turning it into a function jointly continuous in `(s, g)`, holomorphic in `s`
and left `G(F)`-invariant. If moreover every continuation agrees with one that is holomorphic on a
set `Z` of parameters, no power is needed at the points `s₀` with `s₀ λ₁ ∈ Z`; for `Z` the
imaginary parameters this is `HasImaginaryAxisHolomorphy`, the conclusion of
`EisensteinImaginaryAxisHolomorphyStatement`, which passes from `ψ` to `ψ m_P^{iy}` for real `y`.
See the paired Markdown. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set Metric Filter Topology
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global.EisensteinLine

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Two functions continuous on an open set `O` that agree on `O ∩ D` for a dense set `D` agree
on `O`. -/
theorem eqOn_of_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f₁ f₂ : X → Y} {O D : Set X} (hO : IsOpen O) (hD : Dense D) (h₁ : ContinuousOn f₁ O)
    (h₂ : ContinuousOn f₂ O) (heq : EqOn f₁ f₂ (O ∩ D)) : EqOn f₁ f₂ O :=
  heq.of_subset_closure h₁ h₂ inter_subset_left (hD.open_subset_closure_inter hO)

section Translation

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- Meromorphy on `ℂᵐ` is preserved by translations. -/
theorem isMeromorphicOn_comp_add_const {m : ℕ} {f : (Fin m → ℂ) → V} {U : Set (Fin m → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f U) (w : Fin m → ℂ) :
    IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => f (z + w)) ((· + w) ⁻¹' U) := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  let T := Homeomorph.addRight w
  have hT : Differentiable ℂ fun z : Fin m → ℂ => z + w := differentiable_id.add_const w
  refine ⟨hUo.preimage T.continuous, hUd.preimage T.isOpenMap, fun ν => ?_, fun s₀ => ?_⟩
  · have h := mdifferentiableOn_iff_differentiableOn.1 (hhol ν)
    exact mdifferentiableOn_iff_differentiableOn.2
      (h.comp hT.differentiableOn (mapsTo_preimage _ _))
  · obtain ⟨W, hWo, hWc, hsW, g, h, hg, ⟨s₁, hs₁W, hs₁⟩, hh, hgh⟩ := hloc (s₀ + w)
    refine ⟨(· + w) ⁻¹' W, hWo.preimage T.continuous, ?_, hsW, fun z => g (z + w),
      fun z => h (z + w), ?_, ⟨s₁ - w, by simpa using hs₁W, by simpa using hs₁⟩, fun ν => ?_,
      fun s hs => hgh _ hs⟩
    · have : (· + w) ⁻¹' W = T.symm '' W := (T.image_symm_eq_preimage W).symm
      rw [this]
      exact hWc.image _ T.symm.continuous.continuousOn
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 hg).comp hT.differentiableOn
          (mapsTo_preimage _ _))
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 (hh ν)).comp hT.differentiableOn
          (mapsTo_preimage _ _))

/-- Meromorphy in linear coordinates is preserved by translations. -/
theorem isMeromorphicInCoordinatesOn_comp_add_const {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f : X → V} {U : Set X} (hf : IsMeromorphicInCoordinatesOn f U) (c : X) :
    IsMeromorphicInCoordinatesOn (fun x => f (x + c)) ((· + c) ⁻¹' U) := by
  refine ⟨hf.1, fun n e => ?_⟩
  have h1 : (fun x => f (x + c)) ∘ e = fun z => (f ∘ e) (z + e.symm c) := by
    funext z
    simp only [Function.comp_apply, map_add, LinearEquiv.apply_symm_apply]
  have h2 : e ⁻¹' ((· + c) ⁻¹' U) = (· + e.symm c) ⁻¹' (e ⁻¹' U) := by
    ext z
    simp only [mem_preimage, map_add, LinearEquiv.apply_symm_apply]
  rw [h1, h2]
  exact isMeromorphicOn_comp_add_const (hf.2 n e) (e.symm c)

end Translation

section Terms

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Each term `φ(γ g) exp ⟨λ, H_P(γ g)⟩` of the Eisenstein series is entire in linear coordinates
of `λ`. -/
theorem differentiable_eisensteinTerm (φ : AdelicGroupPoints F G → ℂ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (c : ParabolicRationalCosets F p) :
    Differentiable ℂ fun s => hK.eisensteinTerm φ (e s) g c := by
  let H := hK.height (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g)
  let ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => complexParameterPairing F P (e s) H
      map_add' := fun s t => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z s => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have h : (fun s => hK.eisensteinTerm φ (e s) g c) = fun s =>
      φ (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g) *
        Complex.exp (LinearMap.toContinuousLinearMap ℓ s) := rfl
  rw [h]
  exact (differentiable_const _).mul (LinearMap.toContinuousLinearMap ℓ).differentiable.cexp

end Terms

section Presented

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

omit [NumberField F] [IsAffine G.X.left] [IsClosedImmersion p.hom.hom.left]
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left] in
include r in
/-- The complex parameter space `X^*(P) ⊗ ℂ` of a presented parabolic of a connected reductive
group is finite-dimensional. -/
theorem finiteDimensional_parameters (hG : IsConnectedReductive G) :
    FiniteDimensional ℂ (ComplexCharacterParameter F P) := by
  have := (r.rationalCharacters_free_finite hG).2
  exact Module.Finite.base_change ℤ ℂ _

/-- Gluing the local Fréchet-valued continuations of `EisensteinMeromorphicContinuationStatement`:
for `N > 0`, the Eisenstein series of an automorphic form on `P(F) U(𝔸) \ G(𝔸)` has a
continuation `E'` such that every `λ ↦ E'(λ)(g)` is meromorphic in coordinates with one domain
of holomorphy `D₀` independent of `g`. -/
theorem exists_glued_continuation
    (hMero : EisensteinMeromorphicContinuationStatement.{u}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D₀ : Set (ComplexCharacterParameter F P)) (R₀ : ℝ),
      (∀ lam, r.IsRegularParameter hA hT R₀ lam → E' lam = hK.eisensteinSeries φ lam) ∧
      ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D₀ := by
  have := finiteDimensional_parameters r hG
  obtain ⟨E', ⟨R₀, hR₀⟩, hloc⟩ :=
    hMero F G P M U A p iU l a r hA hT hG hUR K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  have hdata : ∀ s₀ : Fin m → ℂ,
      HasLocalMeromorphicData (fun (g : AdelicGroupPoints F G) s => E' (e₀ s) g) s₀ := by
    intro s₀
    obtain ⟨W, hs₀, R, L, -, f, D, hf, hfD⟩ := hloc m e₀ s₀
    refine hasLocalMeromorphicData_of_isMeromorphicOn hf
      (fun g => UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L g)
      (fun t ht g => ?_) hs₀
    rw [UniformGrowthFrechetSpace.evalCLM_apply, (hfD t ht).1]
  obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_of_local hdata
  refine ⟨E', e₀ '' U₀, R₀, hR₀, fun g => isMeromorphicInCoordinatesOn_of_coordinates e₀ ?_⟩
  rw [e₀.injective.preimage_image]
  exact hU₀ g

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- In linear coordinates, the Eisenstein series is continuous in the parameter on the open set
of `R`-regular parameters, for the `R` of a uniform domination of its terms on compact sets. -/
theorem continuousOn_eisensteinSeries_of_bound (hG : IsConnectedReductive G)
    (φ : AdelicGroupPoints F G → ℂ) {R : ℝ}
    (hR : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (Λ : Set (Fin n → ℂ)), IsCompact Λ →
        (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
        ∃ b : ParabolicRationalCosets F p → ℝ, Summable b ∧
          ∀ c : ParabolicRationalCosets F p, ∀ g ∈ C, ∀ s ∈ Λ,
            ‖hK.eisensteinTerm φ (e s) g c‖ ≤ b c)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    ContinuousOn (fun s => hK.eisensteinSeries φ (e s) g)
      {s | r.IsRegularParameter hA hT R (e s)} := by
  intro s₀ hs₀
  have hO := isOpen_setOf_isRegularParameter r hA hT hG R e
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO s₀ hs₀
  have hsub : closedBall s₀ (ε / 2) ⊆ {s | r.IsRegularParameter hA hT R (e s)} :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεO
  obtain ⟨b, hb, hbd⟩ := hR {g} isCompact_singleton n e (closedBall s₀ (ε / 2))
    (isCompact_closedBall s₀ _) fun s hs => hsub hs
  have hc : ContinuousOn (fun s => ∑' c, hK.eisensteinTerm φ (e s) g c) (closedBall s₀ (ε / 2)) :=
    continuousOn_tsum (fun c => (differentiable_eisensteinTerm hK φ e g c).continuous.continuousOn)
      hb fun c s hs => hbd c g (mem_singleton g) s hs
  exact (hc.continuousAt (closedBall_mem_nhds s₀ (half_pos hε))).continuousWithinAt

/-- **Eisenstein series along a complex line.** Let `λ₁` be a parameter such that every root
form `B(·, β)` of a root `β` of `A` in the unipotent radical is nonzero at `λ₁`, and such that
`s λ₁` is `R`-regular for `Re s` large, for every `R`. Assume the meromorphic continuation
(`EisensteinMeromorphicContinuationStatement`) and its joint root-hyperplane form
(`EisensteinJointRootHyperplaneStatement`) in the universe of `F`. Let `Z` be a set of parameters
such that every meromorphic continuation of the Eisenstein series of `φ` agrees, on the common
domain of holomorphy, with one whose domain of holomorphy contains `Z`. Then there are `E` and
`σ` such that `E s` is the Eisenstein series at `s λ₁` for `σ < Re s`, and near every `s₀` a
power `(s - s₀)^m` turns `E` into a function of `(s, g)` that is continuous, holomorphic in `s`
and left `G(F)`-invariant; if `s₀ λ₁ ∈ Z` then `m = 0` and this function is `E` itself at
`s₀`. -/
theorem exists_lineContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{u})
    (hJoint : EisensteinJointRootHyperplaneStatement.{u})
    (hG : IsConnectedReductive G) (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (lam₁ : ComplexCharacterParameter F P)
    (hroot : ∀ β ∈ r.unipotentRoots, r.rootFunctional hA hT β lam₁ ≠ 0)
    (hreg : ∀ R : ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → r.IsRegularParameter hA hT R (s • lam₁))
    (Z : Set (ComplexCharacterParameter F P))
    (hZ : ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
      ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D' : Set (ComplexCharacterParameter F P)), Z ⊆ D' ∧
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
        ∀ lam ∈ D ∩ D', E' lam = E lam) :
    ∃ (E : ℂ → AdelicGroupPoints F G → ℂ) (σ : ℝ),
      (∀ s : ℂ, σ < s.re → E s = hK.eisensteinSeries φ (s • lam₁)) ∧
      ∀ s₀ : ℂ, ∃ (m : ℕ) (W : Set ℂ) (h : ℂ → AdelicGroupPoints F G → ℂ),
        IsOpen W ∧ s₀ ∈ W ∧
        ContinuousOn (fun q : ℂ × AdelicGroupPoints F G => h q.1 q.2) (W ×ˢ univ) ∧
        (∀ g, DifferentiableOn ℂ (fun s => h s g) W) ∧
        (∀ s ∈ W, ∀ c ∈ rationalSubgroup F G, ∀ g, h s (c * g) = h s g) ∧
        (∀ s ∈ W, s ≠ s₀ → ∀ g, h s g = (s - s₀) ^ m * E s g) ∧
        (s₀ • lam₁ ∈ Z → m = 0 ∧ ∀ g, h s₀ g = E s₀ g) := by
  classical
  have := finiteDimensional_parameters r hG
  obtain ⟨E', D₀, R₀, hE'reg, hE'⟩ :=
    exists_glued_continuation r hA hT hK hMero hG hUR rho hN hrho hsmooth hcalc hKmax φ hφ
  obtain ⟨Rc, hRc⟩ := eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hUR K hK rho
    hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨E'', D'', hZD, hE'', hE''eq⟩ := hZ E' D₀ hE' ⟨R₀, hE'reg⟩
  set Rs : ℝ := max R₀ Rc with hRs
  obtain ⟨σ, hσ⟩ := hreg Rs
  let n := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let v : Fin n → ℂ := e.symm lam₁
  have hev : ∀ s : ℂ, e (s • v) = s • lam₁ := fun s => by
    simp only [v, map_smul, LinearEquiv.apply_symm_apply]
  have hline : Continuous fun s : ℂ => s • v := continuous_id.smul continuous_const
  -- the joint root-hyperplane data at every center
  have hJ := fun z₀ : Fin n → ℂ => hJoint F G P M U A p iU l a r hA hT hG hUR K hK rho hsmooth
    hcalc φ hKmax hrho hφ E' D₀ hE' ⟨R₀, hE'reg⟩ n e z₀
  choose S m W' H hSroots hSne hW'o hz₀W' hHc hHd hHinv hHeq using hJ
  let Q : (Fin n → ℂ) → (Fin n → ℂ) → ℂ := fun z₀ z =>
    (∏ β ∈ S z₀, r.rootFunctional hA hT β (e z - e z₀)) ^ m z₀
  have hQc : ∀ z₀, Continuous (Q z₀) := by
    intro z₀
    refine Continuous.pow (continuous_finsetProd _ fun β _ => ?_) _
    have hlin : Continuous fun z => (r.rootFunctional hA hT β ∘ₗ e.toLinearMap) z :=
      LinearMap.continuous_of_finiteDimensional _
    have : (fun z => r.rootFunctional hA hT β (e z - e z₀)) =
        fun z => (r.rootFunctional hA hT β ∘ₗ e.toLinearMap) z -
          r.rootFunctional hA hT β (e z₀) := by
      funext z
      simp only [map_sub, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [this]
    exact hlin.sub continuous_const
  have hD₀d : Dense (e ⁻¹' D₀) := ((hE' 1).2 n e).2.1
  have hD''o : IsOpen (e ⁻¹' D'') := ((hE'' 1).2 n e).1
  have hE''d : ∀ g, DifferentiableOn ℂ (fun z => E'' (e z) g) (e ⁻¹' D'') := fun g =>
    differentiableOn_of_isHolomorphicOn ((hE'' g).2 n e).2.2.1
  have hRegO : IsOpen {z : Fin n → ℂ | r.IsRegularParameter hA hT Rs (e z)} :=
    isOpen_setOf_isRegularParameter r hA hT hG Rs e
  have hregR₀ : ∀ lam, r.IsRegularParameter hA hT Rs lam → r.IsRegularParameter hA hT R₀ lam :=
    fun lam h α hα => (le_max_left R₀ Rc).trans_lt (h α hα)
  have hregRc : ∀ lam, r.IsRegularParameter hA hT Rs lam → r.IsRegularParameter hA hT Rc lam :=
    fun lam h α hα => (le_max_right R₀ Rc).trans_lt (h α hα)
  have hserc : ∀ g, ContinuousOn (fun z => hK.eisensteinSeries φ (e z) g)
      {z | r.IsRegularParameter hA hT Rs (e z)} := fun g =>
    (continuousOn_eisensteinSeries_of_bound r hA hT hK hG φ hRc e g).mono
      fun z hz => hregRc _ hz
  -- the cleared quotient at a center agrees with every continuous function that is the
  -- continuation on the dense domain
  have hquot : ∀ (g : AdelicGroupPoints F G) (O : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ),
      IsOpen O → ContinuousOn f O → (∀ z ∈ O, e z ∈ D₀ → f z = E' (e z) g) →
      ∀ z₀, ∀ z ∈ O, z ∈ W' z₀ → Q z₀ z ≠ 0 → H z₀ z g / Q z₀ z = f z := by
    intro g O f hO hf hfE z₀ z hzO hzW hzQ
    let O' := O ∩ W' z₀ ∩ {z | Q z₀ z ≠ 0}
    have hO' : IsOpen O' := (hO.inter (hW'o z₀)).inter (isOpen_ne_fun (hQc z₀) continuous_const)
    have hc : ContinuousOn (fun z => H z₀ z g / Q z₀ z) O' :=
      (((hHd z₀ g).continuousOn).mono fun z hz => hz.1.2).div (hQc z₀).continuousOn
        fun z hz => hz.2
    refine eqOn_of_dense hO' hD₀d hc (hf.mono fun z hz => hz.1.1) ?_ ⟨⟨hzO, hzW⟩, hzQ⟩
    rintro z ⟨⟨⟨hzO, hzW⟩, hzQ⟩, hzD⟩
    change H z₀ z g / Q z₀ z = f z
    rw [hHeq z₀ g z hzW hzD, hfE z hzO hzD, mul_div_cancel_left₀ _ hzQ]
  -- (i) two centers give the same quotient
  have hcenters : ∀ g z₀ z₁ z, z ∈ W' z₀ → Q z₀ z ≠ 0 → z ∈ W' z₁ → Q z₁ z ≠ 0 →
      H z₁ z g / Q z₁ z = H z₀ z g / Q z₀ z := by
    intro g z₀ z₁ z hz₀ hQ₀ hz₁ hQ₁
    refine hquot g (W' z₀ ∩ {z | Q z₀ z ≠ 0}) (fun z => H z₀ z g / Q z₀ z)
      ((hW'o z₀).inter (isOpen_ne_fun (hQc z₀) continuous_const))
      ((((hHd z₀ g).continuousOn).mono fun z hz => hz.1).div (hQc z₀).continuousOn
        fun z hz => hz.2) ?_ z₁ z ⟨hz₀, hQ₀⟩ hz₁ hQ₁
    rintro z ⟨hzW, hzQ⟩ hzD
    rw [hHeq z₀ g z hzW hzD, mul_div_cancel_left₀ _ hzQ]
  -- (ii) at regular points the quotient is the Eisenstein series
  have hregular : ∀ g z₀ z, r.IsRegularParameter hA hT Rs (e z) → z ∈ W' z₀ → Q z₀ z ≠ 0 →
      H z₀ z g / Q z₀ z = hK.eisensteinSeries φ (e z) g := by
    intro g z₀ z hz hzW hzQ
    refine hquot g _ (fun z => hK.eisensteinSeries φ (e z) g) hRegO (hserc g) ?_ z₀ z hz hzW hzQ
    intro z hz _
    rw [hE'reg _ (hregR₀ _ hz)]
  -- (iii) on the domain of the second continuation the quotient is that continuation
  have hsecond : ∀ g z₀ z, e z ∈ D'' → z ∈ W' z₀ → Q z₀ z ≠ 0 →
      H z₀ z g / Q z₀ z = E'' (e z) g := by
    intro g z₀ z hz hzW hzQ
    refine hquot g _ (fun z => E'' (e z) g) hD''o (hE''d g).continuousOn ?_ z₀ z hz hzW hzQ
    intro z hz hzD
    rw [hE''eq (e z) ⟨hzD, hz⟩]
  -- (iv) at regular points of the second domain the series is the second continuation
  have hregsecond : ∀ g z, e z ∈ D'' → r.IsRegularParameter hA hT Rs (e z) →
      hK.eisensteinSeries φ (e z) g = E'' (e z) g := by
    intro g z hz hzR
    refine eqOn_of_dense (hD''o.inter hRegO) hD₀d ((hserc g).mono fun z hz => hz.2)
      ((hE''d g).continuousOn.mono fun z hz => hz.1) ?_ ⟨hz, hzR⟩
    rintro z ⟨⟨hz, hzR⟩, hzD⟩
    change hK.eisensteinSeries φ (e z) g = E'' (e z) g
    rw [hE''eq (e z) ⟨hzD, hz⟩, hE'reg _ (hregR₀ _ hzR)]
  -- the function on the line
  let Ψ : ℂ → AdelicGroupPoints F G → ℂ := fun s g =>
    if hc : ∃ z₀, s • v ∈ W' z₀ ∧ Q z₀ (s • v) ≠ 0 then
      H hc.choose (s • v) g / Q hc.choose (s • v) else 0
  let E : ℂ → AdelicGroupPoints F G → ℂ := fun s g =>
    if σ < s.re then hK.eisensteinSeries φ (s • lam₁) g
    else if s • lam₁ ∈ D'' then E'' (s • lam₁) g else Ψ s g
  have hEq : ∀ s g z₀, s • v ∈ W' z₀ → Q z₀ (s • v) ≠ 0 →
      E s g = H z₀ (s • v) g / Q z₀ (s • v) := by
    intro s g z₀ hW hQ
    simp only [E]
    split_ifs with h1 h2
    · rw [hregular g z₀ (s • v) (by rw [hev]; exact hσ s h1) hW hQ, hev]
    · rw [hsecond g z₀ (s • v) (by rw [hev]; exact h2) hW hQ, hev]
    · have hc : ∃ z₀, s • v ∈ W' z₀ ∧ Q z₀ (s • v) ≠ 0 := ⟨z₀, hW, hQ⟩
      simp only [Ψ, dite_eq_left hc]
      exact hcenters g z₀ hc.choose (s • v) hW hQ hc.choose_spec.1 hc.choose_spec.2
  have hEsecond : ∀ s g, s • lam₁ ∈ D'' → E s g = E'' (s • lam₁) g := by
    intro s g hs
    simp only [E]
    split_ifs with h1
    · rw [← hev, hregsecond g (s • v) (by rw [hev]; exact hs) (by rw [hev]; exact hσ s h1)]
    · rfl
  refine ⟨E, σ, fun s hs => funext fun g => ite_eq_left hs, fun s₀ => ?_⟩
  -- data on the line through the center `s₀ λ₁`
  set z₀ : Fin n → ℂ := s₀ • v with hz₀
  set κ : ℂ := ∏ β ∈ S z₀, r.rootFunctional hA hT β lam₁ with hκ
  have hκ0 : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β hβ => hroot β (hSroots z₀ hβ)
  set k : ℕ := (S z₀).card * m z₀ with hk
  have hQline : ∀ s : ℂ, Q z₀ (s • v) = (s - s₀) ^ k * κ ^ m z₀ := by
    intro s
    have h1 : e (s • v) - e z₀ = (s - s₀) • lam₁ := by rw [hz₀, hev, hev, sub_smul]
    have h2 : ∏ β ∈ S z₀, r.rootFunctional hA hT β (e (s • v) - e z₀) =
        (s - s₀) ^ (S z₀).card * κ := by
      rw [h1]
      simp only [map_smul, smul_eq_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    change (∏ β ∈ S z₀, r.rootFunctional hA hT β (e (s • v) - e z₀)) ^ m z₀ = _
    rw [h2, mul_pow, ← pow_mul]
  have hQne : ∀ s : ℂ, s ≠ s₀ → Q z₀ (s • v) ≠ 0 := fun s hs => by
    rw [hQline]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs)) (pow_ne_zero _ hκ0)
  let W : Set ℂ := (fun s : ℂ => s • v) ⁻¹' W' z₀
  have hWo : IsOpen W := (hW'o z₀).preimage hline
  have hs₀W : s₀ ∈ W := hz₀W' z₀
  have hcomp : ContinuousOn (fun q : ℂ × AdelicGroupPoints F G => H z₀ (q.1 • v) q.2)
      (W ×ˢ univ) :=
    (hHc z₀).comp ((hline.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun q hq => ⟨hq.1, mem_univ _⟩
  have hdiff : ∀ g, DifferentiableOn ℂ (fun s : ℂ => H z₀ (s • v) g) W := fun g =>
    (hHd z₀ g).comp ((differentiable_id.smul_const v).differentiableOn) fun s hs => hs
  by_cases hZs : s₀ • lam₁ ∈ Z
  · -- on the second domain: no power is needed
    have hD''s₀ : s₀ • lam₁ ∈ D'' := hZD hZs
    let W₁ : Set ℂ := W ∩ (fun s : ℂ => s • v) ⁻¹' (e ⁻¹' D'')
    have hW₁o : IsOpen W₁ := hWo.inter (hD''o.preimage hline)
    have hs₀W₁ : s₀ ∈ W₁ := ⟨hs₀W, show e (s₀ • v) ∈ D'' by rw [hev]; exact hD''s₀⟩
    let f : ℂ → AdelicGroupPoints F G → ℂ := fun s g => E'' (s • lam₁) g
    have hfz : ∀ s g, f s g = E'' (e (s • v)) g := fun s g => by simp only [f, hev]
    have hfd : ∀ g, DifferentiableOn ℂ (fun s => f s g) W₁ := by
      intro g
      have := (hE''d g).comp ((differentiable_id.smul_const v).differentiableOn)
        (fun s (hs : s ∈ W₁) => hs.2)
      refine this.congr fun s _ => ?_
      simp only [Function.comp_apply, hfz]
    have hfq : ∀ s ∈ W₁, s ≠ s₀ → ∀ g, f s g = H z₀ (s • v) g / Q z₀ (s • v) := by
      intro s hs hne g
      rw [hfz, hsecond g z₀ (s • v) hs.2 hs.1 (hQne s hne)]
    have hfc : ContinuousOn (fun q : ℂ × AdelicGroupPoints F G => f q.1 q.2)
        ((W₁ \ {s₀}) ×ˢ univ) := by
      have hQc' : ContinuousOn (fun q : ℂ × AdelicGroupPoints F G => Q z₀ (q.1 • v))
          ((W₁ \ {s₀}) ×ˢ univ) :=
        ((hQc z₀).comp (hline.comp continuous_fst)).continuousOn
      refine ((hcomp.mono fun q hq => ⟨hq.1.1.1, mem_univ _⟩).div hQc'
        fun q hq => hQne q.1 hq.1.2).congr fun q hq => ?_
      exact hfq q.1 hq.1.1 hq.1.2 q.2
    obtain ⟨ρ, hρ, hball, hcont⟩ :=
      Langlands.Analysis.exists_ball_continuousOn_of_punctured hW₁o hs₀W₁ hfd hfc
    refine ⟨0, ball s₀ ρ, f, isOpen_ball, mem_ball_self hρ, hcont,
      fun g => (hfd g).mono hball, ?_, ?_, fun _ => ⟨rfl, fun g => (hEsecond s₀ g hD''s₀).symm⟩⟩
    · intro s hs c hc g
      have hfc' : ∀ g', ContinuousOn (fun s => f s g') (ball s₀ ρ) := fun g' =>
        ((hfd g').mono hball).continuousOn
      refine eqOn_of_dense isOpen_ball (dense_compl_singleton s₀) (hfc' (c * g)) (hfc' g) ?_ hs
      rintro s ⟨hsb, hne⟩
      change f s (c * g) = f s g
      rw [hfq s (hball hsb) hne, hfq s (hball hsb) hne, hHinv z₀ (s • v) (hball hsb).1 c hc g]
    · intro s hs hne g
      rw [pow_zero, one_mul, hEsecond s g (by rw [← hev]; exact (hball hs).2)]
  · refine ⟨k, W, fun s g => (κ ^ m z₀)⁻¹ * H z₀ (s • v) g, hWo, hs₀W,
      continuousOn_const.mul hcomp, fun g => (hdiff g).const_mul _,
      fun s hs c hc g => by simp only [hHinv z₀ (s • v) hs c hc g], ?_,
      fun h => absurd h hZs⟩
    intro s hs hne g
    rw [hEq s g z₀ hs (hQne s hne), hQline]
    have h1 : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
    have h2 : κ ^ m z₀ ≠ 0 := pow_ne_zero _ hκ0
    field_simp

/-- The Eisenstein series of `φ` is holomorphic at the imaginary parameters `i(X^*(P) ⊗ ℝ)` in
the form of the conclusion of `EisensteinImaginaryAxisHolomorphyStatement`: every continuation
`E`, meromorphic in coordinates with one domain of holomorphy `D` and equal to the Eisenstein
series of `φ` for `Re λ` sufficiently regular, agrees on `D ∩ D'` with a continuation `E'`,
meromorphic in coordinates with a domain of holomorphy `D'` that contains the imaginary
parameters. -/
def HasImaginaryAxisHolomorphy (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P)),
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
    ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P)),
      Set.range (imaginaryParameter F P) ⊆ D' ∧
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
      ∀ lam ∈ D ∩ D', E' lam = E lam


omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Imaginary parameters have real part zero. -/
theorem parameterRealPart_imaginaryParameter' (x : RealCharacterParameter F P) :
    parameterRealPart F P (imaginaryParameter F P x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    simp [imaginaryParameter, AlgebraTensorModule.map_tmul, parameterRealPart_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Adding an imaginary parameter does not change regularity. -/
theorem isRegularParameter_add_imaginaryParameter {R : ℝ} (lam : ComplexCharacterParameter F P)
    (y : RealCharacterParameter F P) :
    r.IsRegularParameter hA hT R (lam + imaginaryParameter F P y) ↔
      r.IsRegularParameter hA hT R lam := by
  unfold ParabolicRootPresentation.IsRegularParameter
  rw [map_add, parameterRealPart_imaginaryParameter', add_zero]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Twisting a function by `m_P^c` shifts the parameter of its Eisenstein series by `c`. -/
theorem eisensteinSeries_of_eq_mul_heightPower {φ ψ : AdelicGroupPoints F G → ℂ}
    {c : ComplexCharacterParameter F P} (hφψ : ∀ x, φ x = ψ x * hK.heightPower c x)
    (lam : ComplexCharacterParameter F P) :
    hK.eisensteinSeries φ lam = hK.eisensteinSeries ψ (lam + c) := by
  funext g
  refine tsum_congr fun q => ?_
  simp only [IsIwasawaCompact.eisensteinTerm, IsIwasawaCompact.parameterTwist,
    IsIwasawaCompact.heightPower, hφψ, map_add, LinearMap.add_apply, Complex.exp_add]
  ring

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- **Imaginary twists.** If `φ = ψ m_P^{iy}` for a real parameter `y` and the Eisenstein series
of `ψ` has `HasImaginaryAxisHolomorphy`, so has the Eisenstein series of `φ`: the continuations of
the two series differ by the translation of the parameter by the imaginary parameter `iy`, which
preserves the imaginary parameters. -/
theorem hasImaginaryAxisHolomorphy_of_eq_mul_heightPower {φ ψ : AdelicGroupPoints F G → ℂ}
    (y : RealCharacterParameter F P)
    (hφψ : ∀ x, φ x = ψ x * hK.heightPower (imaginaryParameter F P y) x)
    (hψ : HasImaginaryAxisHolomorphy r hA hT hK ψ) : HasImaginaryAxisHolomorphy r hA hT hK φ := by
  intro E D hE ⟨R, hR⟩
  set c := imaginaryParameter F P y with hc
  have hregψ : ∀ lam, r.IsRegularParameter hA hT R lam →
      E (lam + -c) = hK.eisensteinSeries ψ lam := by
    intro lam hlam
    have hreg : r.IsRegularParameter hA hT R (lam + -c) := by
      have : lam + -c = lam + imaginaryParameter F P (-y) := by rw [hc, map_neg]
      rw [this, isRegularParameter_add_imaginaryParameter]
      exact hlam
    rw [hR _ hreg, eisensteinSeries_of_eq_mul_heightPower hK hφψ, neg_add_cancel_right]
  obtain ⟨E', D', hD', hE', heq⟩ := hψ (fun lam => E (lam + -c)) ((· + -c) ⁻¹' D)
    (fun g => isMeromorphicInCoordinatesOn_comp_add_const (hE g) (-c)) ⟨R, hregψ⟩
  refine ⟨fun lam => E' (lam + c), (· + c) ⁻¹' D', ?_,
    fun g => isMeromorphicInCoordinatesOn_comp_add_const (hE' g) c, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hD' ⟨x + y, by rw [map_add]⟩
  · rintro lam ⟨hlamD, hlamD'⟩
    change E' (lam + c) = E lam
    rw [heq (lam + c) ⟨by simpa using hlamD, hlamD'⟩, add_neg_cancel_right]

/-- **Eisenstein series along a complex line, with the imaginary axis.** The form of
`exists_lineContinuation` in which no power is needed at the points `s₀` with `s₀ λ₁`
imaginary, provided the Eisenstein series of `φ` has `HasImaginaryAxisHolomorphy`. -/
theorem exists_lineContinuation_imaginary
    (hMero : EisensteinMeromorphicContinuationStatement.{u})
    (hJoint : EisensteinJointRootHyperplaneStatement.{u})
    (hG : IsConnectedReductive G) (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (lam₁ : ComplexCharacterParameter F P)
    (hroot : ∀ β ∈ r.unipotentRoots, r.rootFunctional hA hT β lam₁ ≠ 0)
    (hreg : ∀ R : ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → r.IsRegularParameter hA hT R (s • lam₁)) :
    ∃ (E : ℂ → AdelicGroupPoints F G → ℂ) (σ : ℝ),
      (∀ s : ℂ, σ < s.re → E s = hK.eisensteinSeries φ (s • lam₁)) ∧
      ∀ s₀ : ℂ, ∃ (m : ℕ) (W : Set ℂ) (h : ℂ → AdelicGroupPoints F G → ℂ),
        IsOpen W ∧ s₀ ∈ W ∧
        ContinuousOn (fun q : ℂ × AdelicGroupPoints F G => h q.1 q.2) (W ×ˢ univ) ∧
        (∀ g, DifferentiableOn ℂ (fun s => h s g) W) ∧
        (∀ s ∈ W, ∀ c ∈ rationalSubgroup F G, ∀ g, h s (c * g) = h s g) ∧
        (∀ s ∈ W, s ≠ s₀ → ∀ g, h s g = (s - s₀) ^ m * E s g) ∧
        (HasImaginaryAxisHolomorphy r hA hT hK φ →
          s₀ • lam₁ ∈ Set.range (imaginaryParameter F P) →
            m = 0 ∧ ∀ g, h s₀ g = E s₀ g) := by
  classical
  let Z : Set (ComplexCharacterParameter F P) :=
    {x | HasImaginaryAxisHolomorphy r hA hT hK φ ∧ x ∈ Set.range (imaginaryParameter F P)}
  have hZ : ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
      ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D' : Set (ComplexCharacterParameter F P)), Z ⊆ D' ∧
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
        ∀ lam ∈ D ∩ D', E' lam = E lam := by
    intro E D hE hER
    by_cases hIm : HasImaginaryAxisHolomorphy r hA hT hK φ
    · obtain ⟨E', D', hD', hE', heq⟩ := hIm E D hE hER
      exact ⟨E', D', fun x hx => hD' hx.2, hE', heq⟩
    · exact ⟨E, D, fun x hx => absurd hx.1 hIm, hE, fun _ _ => rfl⟩
  obtain ⟨E, σ, h1, h2⟩ := exists_lineContinuation r hA hT hK hMero hJoint hG hUR rho hN hrho
    hsmooth hcalc hKmax φ hφ lam₁ hroot hreg Z hZ
  refine ⟨E, σ, h1, fun s₀ => ?_⟩
  obtain ⟨m, W, h, hW, hs₀, hc, hd, hinv, heq, hZs⟩ := h2 s₀
  exact ⟨m, W, h, hW, hs₀, hc, hd, hinv, heq, fun hIm hs => hZs ⟨hIm, hs⟩⟩

end Presented

end Langlands.Global.EisensteinLine
