import Langlands.Global.AdelicIntertwiningInvertedRootStatement
import Langlands.Global.AdelicStandardRootFunctional
import Langlands.Global.AdelicPositiveChamberProof
import Langlands.Analysis.Meromorphic.RootHyperplaneRestriction
import Langlands.GroupScheme.Rational.DominantWeylDisplacementRoots
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice

/-! # Restricted continuation of tested intertwining terms from the inverted-root continuation

For a standard parabolic family, standard indices `I' ≤ I` with the inclusion
`f : P_{I'} → P_I`, and a rational point `n` whose Weyl element maps the simple roots in `I` to
positive roots, the roots of `A_{I'}` in `U_{I'}` inverted by `n` restrict to roots of `A_I` in
`U_I`, with the same root forms on the restricted parameters `λ|`, `λ ∈ X^*(P_I) ⊗ ℂ`. So the
continuation of the tested intertwining terms in parameters of `P_{I'}` with poles along the
inverted roots (`IntertwiningInvertedRootCuspidalTestContinuationStatement`) restricts to a
continuation in parameters of `P_I` with poles along the root hyperplanes of `P_I`
(`IntertwiningRestrictedCuspidalTestContinuationStatement`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

section Roots

omit [NumberField F] in
/-- **Inverted roots lie outside the Levi.** If the Weyl element of `n` maps every simple root
in `I` to a positive root, then a positive root `χ` with `n · χ` not positive is not in the real
span of `I`. The proof pairs with a standard cocharacter `ζ` of `I`: a sum of simple roots with
zero pairing with `ζ` is a sum of simple roots in `I`, and `n` maps it to an element pairing
nonnegatively with the generic cocharacter. -/
theorem one_tmul_notMem_span_of_inverted {I : StandardIndex F G 𝓕.i 𝓕.ν}
    {n : normalizerPoints 𝓕.i}
    (hpos : ∀ α ∈ I.val, schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) α ∈
      positiveRelativeRoots 𝓕.i 𝓕.ν)
    {χ : characterLattice 𝓕.T} (hχ : χ ∈ positiveRelativeRoots 𝓕.i 𝓕.ν)
    (hwχ : schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) χ ∉
      positiveRelativeRoots 𝓕.i 𝓕.ν) :
    (1 : ℝ) ⊗ₜ[ℤ] χ ∉
      Submodule.span ℝ ((fun χ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ) '' I.val) := by
  intro hmem
  set w := schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n)
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
    𝓕.ν 𝓕.generic I.val I.property).1
  have hχζ : latticePairing 𝓕.T χ ζ = 0 := by
    have hle : Submodule.span ℝ ((fun χ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ) '' I.val) ≤
        LinearMap.ker ((pair 𝓕.T).flip ((1 : ℝ) ⊗ₜ[ℤ] ζ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨α, hα, rfl⟩
      simp [pair_tmul_tmul, hζ.2.1 α hα]
    have h := hle hmem
    simp only [LinearMap.mem_ker, LinearMap.flip_apply, pair_tmul_tmul, one_mul,
      Int.cast_eq_zero] at h
    exact h
  have key : ∀ x ∈ AddSubmonoid.closure (simpleRelativeRoots 𝓕.i 𝓕.ν),
      0 ≤ latticePairing 𝓕.T x ζ ∧
        (latticePairing 𝓕.T x ζ = 0 → 0 ≤ latticePairing 𝓕.T (w x) 𝓕.ν) := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem α hα =>
      by_cases hαI : α ∈ I.val
      · exact ⟨(hζ.2.1 α hαI).ge, fun _ => (hpos α hαI).2.le⟩
      · exact ⟨(hζ.2.2 α hα hαI).le, fun h => absurd h (hζ.2.2 α hα hαI).ne'⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, LinearMap.add_apply]
      refine ⟨add_nonneg hx.1 hy.1, fun h => ?_⟩
      have hx0 : latticePairing 𝓕.T x ζ = 0 := by linarith [hx.1, hy.1]
      have hy0 : latticePairing 𝓕.T y ζ = 0 := by linarith [hx.1, hy.1]
      exact add_nonneg (hx.2 hx0) (hy.2 hy0)
  have hnn := (key χ (DominantDisplacement.positive_mem_closure hχ)).2 hχζ
  have hroot : w χ ∈ relativeRoots 𝓕.i := by
    rw [← schemeWeylCharacterAction_image_relativeRoots 𝓕.i (QuotientGroup.mk n)]
    exact mem_image_of_mem _ hχ.1
  exact hwχ ⟨hroot, lt_of_le_of_ne hnn (Ne.symm (𝓕.generic _ hroot))⟩

/-- A positive root outside the real span of `I` restricts to a root of the split component
of `P_I` in its unipotent radical. -/
theorem restrict_mem_unipotentRoots_of_notMem_span {I : StandardIndex F G 𝓕.i 𝓕.ν}
    {χ : characterLattice 𝓕.T} (hχ : χ ∈ positiveRelativeRoots 𝓕.i 𝓕.ν)
    (hspan : (1 : ℝ) ⊗ₜ[ℤ] χ ∉
      Submodule.span ℝ ((fun χ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ) '' I.val)) :
    𝓕.f I ≫ χ ∈ (𝓕.rootPresentation I).unipotentRoots := by
  refine ⟨fun h => hspan ?_, χ, hχ, rfl⟩
  rw [← 𝓕.ker_restrictReal_splitComponent I, LinearMap.mem_ker]
  change (1 : ℝ) ⊗ₜ[ℤ] (𝓕.f I ≫ χ) = 0
  rw [h, TensorProduct.tmul_zero]

end Roots

section Forms

omit [NumberField F] in
/-- Restriction of real parameters along nested standard parabolics commutes with restriction
to the maximal split torus. -/
theorem torusRestrictReal_restrictReal {I I' : StandardIndex F G 𝓕.i 𝓕.ν}
    (f : 𝓕.P I' ⟶ 𝓕.P I) (hf : f ≫ 𝓕.p I = 𝓕.p I') (x : RealCharacterParameter F (𝓕.P I)) :
    𝓕.torusRestrictReal I' (rationalCharacterRestrictReal f x) = 𝓕.torusRestrictReal I x := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    change rationalCharacterRestrictReal (𝓕.torus I' ≫ 𝓕.l I')
        (s ⊗ₜ[ℤ] characterRestrict f χ) =
      rationalCharacterRestrictReal (𝓕.torus I ≫ 𝓕.l I) (s ⊗ₜ[ℤ] χ)
    rw [rationalCharacterRestrictReal_tmul, rationalCharacterRestrictReal_tmul,
      ← 𝓕.torus_comp_factor f hf, ← Category.assoc, characterRestrict_comp _ f,
      AddMonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField F] in
/-- The real part of a restricted complex parameter is the restriction of its real part. -/
theorem parameterRealPart_parameterRestrict {H H' : GroupScheme (Spec (CommRingCat.of F))}
    (f : H' ⟶ H) (lam : ComplexCharacterParameter F H) :
    parameterRealPart F H' (parameterRestrict f lam) =
      rationalCharacterRestrictReal f (parameterRealPart F H lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype (relativeWeylGroup 𝓕.i)] [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]

/-- **Root forms on restricted parameters, real version.** For `I' ≤ I`, the root form of
`χ ∘ f_{I'}` on `X^*(P_{I'}) ⊗ ℝ`, evaluated on the restriction of `x ∈ X^*(P_I) ⊗ ℝ`, is the root
form of `χ ∘ f_I` evaluated on `x`; both are `B_T(x|_T, χ)`. -/
theorem realRootFunctional_restrictReal {I I' : StandardIndex F G 𝓕.i 𝓕.ν}
    (f : 𝓕.P I' ⟶ 𝓕.P I) (hf : f ≫ 𝓕.p I = 𝓕.p I') (χ : characterLattice 𝓕.T)
    (x : RealCharacterParameter F (𝓕.P I)) :
    (𝓕.rootPresentation I').realRootFunctional
        (𝓕.isCompatible I').splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 (𝓕.f I' ≫ χ) (rationalCharacterRestrictReal f x) =
      (𝓕.rootPresentation I).realRootFunctional
        (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 (𝓕.f I ≫ χ) x := by
  rw [𝓕.realRootFunctional_eq, 𝓕.realRootFunctional_eq, 𝓕.torusRestrictReal_restrictReal f hf]

/-- **Root forms on restricted parameters.** For `I' ≤ I`, the root form of `χ ∘ f_{I'}`
composed with the restriction `X^*(P_I) ⊗ ℂ → X^*(P_{I'}) ⊗ ℂ` is the root form of `χ ∘ f_I`. -/
theorem rootFunctional_comp_parameterRestrict {I I' : StandardIndex F G 𝓕.i 𝓕.ν}
    (f : 𝓕.P I' ⟶ 𝓕.P I) (hf : f ≫ 𝓕.p I = 𝓕.p I') (χ : characterLattice 𝓕.T) :
    (𝓕.rootPresentation I').rootFunctional
        (𝓕.isCompatible I').splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 (𝓕.f I' ≫ χ) ∘ₗ parameterRestrict f =
      (𝓕.rootPresentation I).rootFunctional
        (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 (𝓕.f I ≫ χ) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ'
  rw [LinearMap.comp_apply]
  change (𝓕.rootPresentation I').rootFunctional _ _ (𝓕.f I' ≫ χ)
      (s ⊗ₜ[ℤ] characterRestrict f χ') = _
  rw [ParabolicRootPresentation.rootFunctional_tmul, ParabolicRootPresentation.rootFunctional_tmul]
  congr 2
  exact 𝓕.realRootFunctional_restrictReal f hf χ ((1 : ℝ) ⊗ₜ[ℤ] χ')

/-- The real part of a complex root form is the real root form of the real part. -/
theorem re_rootFunctional (J : StandardIndex F G 𝓕.i 𝓕.ν) (β : characterLattice (𝓕.A J))
    (lam : ComplexCharacterParameter F (𝓕.P J)) :
    ((𝓕.rootPresentation J).rootFunctional
        (𝓕.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 β lam).re =
      (𝓕.rootPresentation J).realRootFunctional
        (𝓕.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        𝓕.maximalSplit.isSplitSubtorus.1 β (parameterRealPart F (𝓕.P J) lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [ParabolicRootPresentation.rootFunctional_tmul, parameterRealPart_tmul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [show s.re ⊗ₜ[ℤ] χ = s.re • ((1 : ℝ) ⊗ₜ[ℤ] χ) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  | add x y hx hy => simp only [map_add, Complex.add_re, hx, hy]

end Forms

section Regularity

variable [Fintype (relativeWeylGroup 𝓕.i)] [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]

/-- A root form of a root of `A_I` in `U_I` is not zero: it has positive real part on the
positive chamber, which is nonempty (`positiveChamberNonempty`). -/
theorem rootFunctional_ne_zero (I : StandardIndex F G 𝓕.i 𝓕.ν) {β : characterLattice (𝓕.A I)}
    (hβ : β ∈ (𝓕.rootPresentation I).unipotentRoots) :
    (𝓕.rootPresentation I).rootFunctional
      (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
      𝓕.maximalSplit.isSplitSubtorus.1 β ≠ 0 := by
  intro h0
  obtain ⟨lam, hlam⟩ := positiveChamberNonempty F G (𝓕.P I) (𝓕.M I) (𝓕.A I) (𝓕.p I) (𝓕.l I)
    (𝓕.a I) (𝓕.rootPresentation I) (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
    𝓕.maximalSplit.isSplitSubtorus.1 𝓕.connectedReductive
  have hpos := hlam β hβ
  have hre := 𝓕.re_rootFunctional I β lam
  rw [h0, LinearMap.zero_apply, Complex.zero_re] at hre
  change 0 < (𝓕.rootPresentation I).realRootFunctional _ _ β (parameterRealPart F (𝓕.P I) lam)
    at hpos
  linarith

/-- **Restricted regular parameters are regular for the inverted roots.** For `I' ≤ I` and `n`
mapping the simple roots in `I` to positive roots, the restriction of an `R`-regular parameter
of `P_I` is `R`-regular for the roots of `A_{I'}` in `U_{I'}` inverted by `n`. -/
theorem isInvertedRootRegular_parameterRestrict {I I' : StandardIndex F G 𝓕.i 𝓕.ν}
    (f : 𝓕.P I' ⟶ 𝓕.P I) (hf : f ≫ 𝓕.p I = 𝓕.p I') {n : normalizerPoints 𝓕.i}
    (hpos : ∀ α ∈ I.val, schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) α ∈
      positiveRelativeRoots 𝓕.i 𝓕.ν)
    {R : ℝ} {lam : ComplexCharacterParameter F (𝓕.P I)}
    (hlam : (𝓕.rootPresentation I).IsRegularParameter
      (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
      𝓕.maximalSplit.isSplitSubtorus.1 R lam) :
    𝓕.IsInvertedRootRegular I' n R (parameterRestrict f lam) := by
  rintro β ⟨-, χ, hχ, rfl, hwχ⟩
  rw [parameterRealPart_parameterRestrict, 𝓕.realRootFunctional_restrictReal f hf]
  exact hlam _ (𝓕.restrict_mem_unipotentRoots_of_notMem_span hχ
    (𝓕.one_tmul_notMem_span_of_inverted hpos hχ hwχ))

end Regularity

end StandardParabolicFamily

/-- The reduction of the restricted continuation of the tested intertwining terms to their
continuation with poles along the inverted roots. -/
def IntertwiningRestrictedCuspidalTestContinuationReductionStatement : Prop :=
  IntertwiningInvertedRootCuspidalTestContinuationStatement.{u} →
    IntertwiningRestrictedCuspidalTestContinuationStatement.{u}

/-- **The inverted-root continuation restricts to parameters of `P_I`.** The coefficients of
the inverted-root continuation, composed with the restriction `λ ↦ λ|` and regularized off their
domain, are meromorphic on `X^*(P_I) ⊗ ℂ` with poles along the pulled-back forms of the inverted
roots (`exists_comp_linearMap_of_hasRootHyperplanePoles`); these are the root forms of roots of
`A_I` in `U_I` (`rootFunctional_comp_parameterRestrict`), and restricted regular parameters are
regular for the inverted roots (`isInvertedRootRegular_parameterRestrict`). -/
theorem intertwiningRestrictedCuspidalTestContinuationReduction :
    IntertwiningRestrictedCuspidalTestContinuationReductionStatement.{u} := by
  classical
  intro hinv F _ _ G _ _ _ 𝓕 _ _ K h₀ hKmax hLevi N d rho hsmooth hrho I I' J f n c π hf hW hπ
    hpos φ' hφ'
  obtain ⟨k, Φ, coeff, D, hmer, hpoles, R, hRD, hagree⟩ :=
    hinv F G 𝓕 K h₀ hKmax hLevi rho hsmooth hrho I' J n c π hW hπ φ' hφ'
  set hA := (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
  set hA' := (𝓕.isCompatible I').splitComponent.isCentralSplitTorus.1.1
  set hT := 𝓕.maximalSplit.isSplitSubtorus.1
  set τ : ComplexCharacterParameter F (𝓕.P I) →ₗ[ℂ] ComplexCharacterParameter F (𝓕.P I') :=
    parameterRestrict f
  -- a chosen positive lift of every inverted root
  have hlift : ∀ β ∈ 𝓕.invertedRoots I' n, ∃ χ : characterLattice 𝓕.T,
      χ ∈ positiveRelativeRoots 𝓕.i 𝓕.ν ∧ 𝓕.f I' ≫ χ = β ∧
        schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) χ ∉
          positiveRelativeRoots 𝓕.i 𝓕.ν := by
    rintro β ⟨-, χ, hχ, h1, h2⟩
    exact ⟨χ, hχ, h1, h2⟩
  let lift : characterLattice (𝓕.A I') → characterLattice 𝓕.T := fun β =>
    if hβ : β ∈ 𝓕.invertedRoots I' n then (hlift β hβ).choose else 0
  have hlift_spec : ∀ β ∈ 𝓕.invertedRoots I' n,
      lift β ∈ positiveRelativeRoots 𝓕.i 𝓕.ν ∧ 𝓕.f I' ≫ lift β = β ∧
        schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) (lift β) ∉
          positiveRelativeRoots 𝓕.i 𝓕.ν := by
    intro β hβ
    simp only [lift, hβ, ↓reduceDIte]
    exact (hlift β hβ).choose_spec
  let σ : characterLattice (𝓕.A I') → characterLattice (𝓕.A I) := fun β => 𝓕.f I ≫ lift β
  have hσ : ∀ β ∈ 𝓕.invertedRoots I' n, σ β ∈ (𝓕.rootPresentation I).unipotentRoots :=
    fun β hβ => 𝓕.restrict_mem_unipotentRoots_of_notMem_span (hlift_spec β hβ).1
      (𝓕.one_tmul_notMem_span_of_inverted hpos (hlift_spec β hβ).1 (hlift_spec β hβ).2.2)
  have hL : ∀ β ∈ 𝓕.invertedRoots I' n,
      (𝓕.rootPresentation I').rootFunctional hA' hT β ∘ₗ τ =
        (1 : ℂ) • (𝓕.rootPresentation I).rootFunctional hA hT (σ β) := by
    intro β hβ
    rw [one_smul]
    conv_lhs => rw [← (hlift_spec β hβ).2.1]
    exact 𝓕.rootFunctional_comp_parameterRestrict f hf (lift β)
  have hne : ∀ β ∈ 𝓕.invertedRoots I' n,
      (𝓕.rootPresentation I').rootFunctional hA' hT β ∘ₗ τ ≠ 0 := by
    intro β hβ
    rw [hL β hβ, one_smul]
    exact 𝓕.rootFunctional_ne_zero I (hσ β hβ)
  have : FiniteDimensional ℂ (ComplexCharacterParameter F (𝓕.P I)) := by
    have := ((𝓕.rootPresentation I).rationalCharacters_free_finite 𝓕.connectedReductive).2
    exact Module.Finite.base_change ℤ ℂ _
  have hres := fun i => exists_comp_linearMap_of_hasRootHyperplanePoles (hmer i) (hpoles i) τ hne
  choose coeff' D' hmer' hpoles' heq' using hres
  have hDc : IsOpenDenseInCoordinates (⋂ i, D' i) :=
    isOpenDenseInCoordinates_iInter_of_finite fun i => (hmer' i).isOpenDenseInCoordinates
  refine ⟨k, Φ, coeff', ⋂ i, D' i, fun i => ?_, fun i => ?_, R, fun lam hlam ψ hψ g => ?_⟩
  · exact (hmer' i).congr_mono hDc (iInter_subset _ i) fun _ _ => rfl
  · exact ((hpoles' i).of_proportional σ (fun _ => 1) hσ (fun _ _ => one_ne_zero) hL).mono
      (iInter_subset _ i)
  · have hreg : 𝓕.IsInvertedRootRegular I' n R (τ lam) :=
      𝓕.isInvertedRootRegular_parameterRestrict f hf hpos hlam
    have hD : τ lam ∈ D := hRD _ hreg
    rw [hagree (τ lam) hreg ψ hψ g]
    exact Finset.sum_congr rfl fun i _ => by rw [heq' i lam hD]

end Langlands.Global
