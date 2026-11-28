import Langlands.Global.AdelicFullSourceBruhatCovariance
import Langlands.Global.AdelicNestedSplitParameterRestriction
import Langlands.Global.AdelicWeakConstantTermShiftContinuation
import Langlands.Global.AdelicIntertwiningAdjunctionReduction

/-! # The unitary part of a continued Bruhat sum -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G}

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Param[" J "]" => ComplexCharacterParameter F (fam.P J)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)

namespace StandardBruhatConstantTermData

/-- The Weyl parameter of a Bruhat summand expressed on the full target parabolic. -/
def targetWeylParameter {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    (w : b.Index) : Param[I] →ₗ[ℂ] Param[J] :=
  (fam.nestedSplitParameter (b.targetIndex_le w)).comp (b.transportedParameter w)

/-- The target parameter gives exactly the character on the lifted target split point. -/
theorem parameterPower_targetWeylParameter {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    (w : b.Index) (lam : Param[I])
    (a : fam.positiveSplitComponent J) :
    parameterPower F (fam.P J) (b.targetWeylParameter w lam) a.val = b.splitWeylCharacter w lam a :=
  fam.parameterPower_nestedSplitParameter (b.targetIndex_le w) (b.transportedParameter w lam) a

theorem parameterRealPart_targetWeylParameter_eq_zero {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    (w : b.Index) {lam : Param[I]}
    (hlam : parameterRealPart F (fam.P I) lam = 0) :
    parameterRealPart F (fam.P J) (b.targetWeylParameter w lam) = 0 := by
  apply fam.parameterRealPart_nestedSplitParameter_eq_zero (b.targetIndex_le w)
  change parameterRealPart F (fam.P (b.targetIndex w))
    (parameterRestrict (b.targetLeviRetraction w ≫ (b.piece w).conjugation ≫ fam.l (b.sourceIndex w))
      (parameterRestrict (b.piece w).source.inclusion lam)) = 0
  rw [parameterRealPart_pullback, parameterRealPart_pullback, hlam, map_zero, map_zero]

end StandardBruhatConstantTermData

private theorem hasExponent_of_normalizedAction {J : Idx} {lam : Param[J]} {f : Fun}
    (h : ∀ a : fam.positiveSplitComponent J,
      fam.normalizedAction J a.val f = parameterPower F (fam.P J) lam a.val • f) :
    fam.HasExponent J lam f := by
  refine ⟨0, fun g => ⟨fun _ => f g, ?_, ?_⟩⟩
  · have hone : (1 : RealCharacterDual F (fam.P J) → ℂ) ∈ polynomialFunctions _ 0 := by
      apply Submodule.subset_span
      exact ⟨0, le_rfl, Fin.elim0, by funext y; simp⟩
    simpa only [Pi.smul_def, Pi.one_def, smul_eq_mul, mul_one] using
      Submodule.smul_mem (polynomialFunctions _ 0) (f g) hone
  · intro a ha
    rw [congrFun (h ⟨a, ha⟩) g, Pi.smul_apply, smul_eq_mul, mul_right_comm,
      ← parameterPower_add, add_neg_cancel, InducedInnerProductIntegrable.parameterPower_zero,
      one_mul]

set_option maxHeartbeats 1500000 in
/-- A finite family of automorphic split eigenfunctions with unitary labels has a decomposition
with exactly the distinct supplied labels. -/
theorem exists_unitaryExponentDecomposition_sum_of_normalizedAction
    {J : Idx} {κ : Type*} [Fintype κ] {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (lam : κ → Param[J]) (f : κ → Fun)
    (hauto : ∀ j, fam.IsAutomorphicOn hsmooth Kinf rho J (f j))
    (hunit : ∀ j, parameterRealPart F (fam.P J) (lam j) = 0)
    (hcov : ∀ j (a : fam.positiveSplitComponent J),
      fam.normalizedAction J a.val (f j) = parameterPower F (fam.P J) (lam j) a.val • f j) :
    ∃ (t : Finset (Param[J])) (c : Param[J] → Fun),
      (∀ z, z ∈ t ↔ ∃ j, lam j = z) ∧
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (∑ j, f j) t c ∧
      (∀ z ∈ t, parameterRealPart F (fam.P J) z = 0) := by
  classical
  let t : Finset (Param[J]) := Finset.univ.image lam
  let c (z : Param[J]) : Fun := ∑ j : κ, if z ∈ ({lam j} : Finset (Param[J])) then f j else 0
  have ht (z : Param[J]) : z ∈ t ↔ ∃ j, lam j = z := by simp [t]
  have hmem (j : κ) : ({lam j} : Finset (Param[J])) ⊆ t :=
    Finset.singleton_subset_iff.mpr ((ht _).mpr ⟨j, rfl⟩)
  refine ⟨t, c, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [c]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hmem j), Finset.sum_singleton]
  · intro z _
    apply (fam.automorphicSubmodule hsmooth Kinf rho J).sum_mem
    intro j _
    rw [fam.mem_automorphicSubmodule]
    by_cases h : z ∈ ({lam j} : Finset (Param[J]))
    · simpa only [ite_eq_left h] using hauto j
    · simpa only [ite_eq_right h] using fam.isAutomorphicOn_zero hsmooth Kinf rho J
  · intro z _
    apply (fam.hasExponent_iff J z _).mpr
    apply fam.hasUnnormalizedExponent_sum J
    intro j _
    by_cases h : z ∈ ({lam j} : Finset (Param[J]))
    · rw [ite_eq_left h, Finset.mem_singleton.mp h]
      exact (fam.hasExponent_iff J (lam j) _).mp (hasExponent_of_normalizedAction (hcov j))
    · rw [ite_eq_right h]
      exact fam.hasUnnormalizedExponent_zero J _
  · intro z hz
    obtain ⟨j, rfl⟩ := (ht _).mp hz
    exact hunit j

namespace StandardBruhatConstantTermData

/-- At an imaginary parameter the continued full-source summands give a unitary exponent
expansion, once the individual meromorphic continuations and their automorphy are supplied. -/
theorem exists_unitaryExponentDecomposition_fullSource_of_continuation
    {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
    {φ : Fun} (hc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (heq : IsSplitComponentEquivariant (fam.p I) (fam.l I) φ)
    (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (term : b.FullSourceIndex → Param[I] → Fun) (D : Set (Param[I]))
    (hterm : ∀ w g, IsMeromorphicInCoordinatesOn (fun lam => term w lam g) D)
    (R : ℝ) (hreg : ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ w : b.FullSourceIndex, term w lam = b.summand hKmin w.val φ lam)
    {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))
    (x : RealCharacterParameter F (fam.P I)) :
    let lam := imaginaryParameter F (fam.P I) x
    let Kinf := K.comap (ofInfinite F G).toMonoidHom
    lam ∈ D → (∀ w, fam.IsAutomorphicOn hsmooth Kinf rho J (term w lam)) →
    ∃ (t : Finset (Param[J])) (c : Param[J] → Fun),
      (∀ z, z ∈ t ↔ ∃ w : b.FullSourceIndex, b.targetWeylParameter w.val lam = z) ∧
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (∑ w, term w lam) t c ∧
      (∀ z ∈ t, parameterRealPart F (fam.P J) z = 0) := by
  classical
  intro lam Kinf hlam hauto
  apply exists_unitaryExponentDecomposition_sum_of_normalizedAction hsmooth Kinf rho
    (fun w : b.FullSourceIndex => b.targetWeylParameter w.val lam) (fun w => term w lam) hauto
  · exact fun w => b.parameterRealPart_targetWeylParameter_eq_zero w.val
      (parameterRealPart_imaginaryParameter x)
  · intro w a
    rw [b.parameterPower_targetWeylParameter]
    exact b.fullSourceBruhatCovariance_of_continuation w hKmin hc hφ heq r hA hT
      (term w) D (hterm w) R (fun t ht => hreg t ht w) lam hlam a

end StandardBruhatConstantTermData

private theorem exists_splitPoint_separating_nonunitary {J : Idx} {lam : Param[J]}
    (h : parameterRealPart F (fam.P J) lam ≠ 0) :
    ∃ a : fam.positiveSplitComponent J,
      ‖parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a.val‖ ≠
        ‖fam.halfModulus J a.val‖ := by
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  obtain ⟨_, hinj⟩ := eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J)
    (fam.p J) (fam.l J) (fam.a J) r
  by_contra hsep
  push Not at hsep
  let mu := parameterRealPart F (fam.P J) lam
  have hnorm (a : fam.positiveSplitComponent J) : ‖parameterPower F (fam.P J) lam a.val‖ = 1 := by
    have ha := hsep a
    rw [parameterPower_add, norm_mul] at ha
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))
      (ha.trans (one_mul _).symm)
  have hp (v : RealCharacterParameter F (fam.P J)) (H : RealCharacterDual F (fam.P J)) :
      complexParameterPairing F (fam.P J) (realToComplexParameter (fam.P J) v) H =
        (realParameterPairing F (fam.P J) v H : ℂ) := by
    induction v using TensorProduct.inductionOn with
    | tmul t χ => simp [realToComplexParameter_tmul, complexParameterPairing_tmul,
        realParameterPairing_tmul, Complex.ofReal_mul]
    | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw, Complex.ofReal_add]
  have hzero : realToComplexParameter (fam.P J) mu = 0 := by
    apply hinj
    funext a
    have ha := hnorm a
    rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, ← Real.exp_zero,
      Real.exp_eq_exp] at ha
    change parameterPower F (fam.P J) (realToComplexParameter (fam.P J) mu) a.val =
      parameterPower F (fam.P J) 0 a.val
    rw [InducedInnerProductIntegrable.parameterPower_zero, parameterPower, hp,
      show realParameterPairing F (fam.P J) mu
      (characterLog F (fam.P J) a.val) = 0 from ha,
      Complex.ofReal_zero, Complex.exp_zero]
  have hre := parameterRealPart_smul_realToComplexParameter (1 : ℂ) mu
  rw [one_smul, hzero, map_zero, Complex.one_re, one_smul] at hre
  exact h hre.symm

/-- A fixed finite list of proper-source affine exponent labels, each with a bounded polynomial
orbit degree. The linear parts preserve imaginary parameters and the offsets have nonzero real
part. The raw labels include the target half modulus. -/
def HasNonunitaryAffineExponentExpansion {I : Idx} (J : Idx) (V : Set (Param[I]))
    (rem : Param[I] → Fun) : Prop :=
  ∃ (n : ℕ) (L : Fin n → Param[I] →ₗ[ℂ] Param[J]) (c : Fin n → Param[J]) (k : Fin n → ℕ),
    (∀ i x, parameterRealPart F (fam.P J) (L i (imaginaryParameter F (fam.P I) x)) = 0) ∧
    (∀ i, parameterRealPart F (fam.P J) (c i) ≠ 0) ∧
    ∀ lam ∈ V, ∃ e : Fin n → Fun,
      rem lam = ∑ i, e i ∧ ∀ i, fam.HasPolynomialOrbit J
        (L i lam + c i + halfModulusParameter F (fam.P J)) (k i) (e i)

set_option maxHeartbeats 2000000 in
private theorem exists_affine_remainder_annihilator {I J : Idx}
    (V : Set (Param[I])) {rem : Param[I] → Fun} (hexp : HasNonunitaryAffineExponentExpansion J V rem) :
    ∃ (n : ℕ) (a : Fin n → fam.positiveSplitComponent J) (m : Fin n → ℕ)
        (z : Fin n → Param[I] → ℂ),
      (∀ (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] Param[I]) (i : Fin n),
        Differentiable ℂ (z i ∘ e)) ∧
      (∀ x i, ‖z i (imaginaryParameter F (fam.P I) x)‖ ≠ ‖fam.halfModulus J (a i).val‖) ∧
      ∀ lam ∈ V, fam.splitShiftProduct J Finset.univ a (fun i => z i lam) m (rem lam) = 0 := by
  obtain ⟨n, L, c, k, hLin, hOffset, hdecomp⟩ := hexp
  choose a ha using fun i => exists_splitPoint_separating_nonunitary (hOffset i)
  let z (i : Fin n) (lam : Param[I]) :=
    parameterPower F (fam.P J) (L i lam + c i + halfModulusParameter F (fam.P J)) (a i).val
  refine ⟨n, a, fun i => k i + 1, z, ?_, ?_, ?_⟩
  · intro d e i
    change Differentiable ℂ (fun s => z i (e s))
    simpa only [z, add_assoc, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      differentiable_parameterPower_affine ((L i).comp e.toLinearMap)
        (c i + halfModulusParameter F (fam.P J)) (a i).val
  · intro x i
    have hu : ‖parameterPower F (fam.P J) (L i (imaginaryParameter F (fam.P I) x)) (a i).val‖ = 1 := by
      rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, hLin]
      simp
    simpa only [z, add_assoc, parameterPower_add, norm_mul, hu, one_mul] using ha i
  · intro lam hlam
    obtain ⟨e, hr, he⟩ := hdecomp lam hlam
    rw [hr, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    apply fam.shiftAlgHom_prod_eq_zero Finset.univ a (fun j => z j lam) (fun j => k j + 1)
      (Finset.mem_univ i)
    have hl : fam.splitLift (le_refl J) (a i) = a i := by
      let : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
      apply Subtype.ext
      exact (isClosedEmbedding_map F (fam.P J) G (fam.p J)).injective
        (fam.map_splitLift (le_refl J) (a i))
    simpa only [hl] using fam.shiftAlgHom_factor_eq_zero (le_refl J) (he i) (a i)

/-- Reduce the weak Bruhat identity to individual full-source continuations, scalar meromorphy
of the remainder, affine exponent support on the convergence chamber, and an automorphic
exponent decomposition of the remainder on the imaginary axis. -/
def WeakBruhatUnitaryAssemblyStatement
    {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
    (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp) : Prop :=
  ∀ (φ : Fun), Continuous φ →
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ →
    IsSplitComponentEquivariant (fam.p I) (fam.l I) φ →
    ∀ (E : Param[I] → Fun) (term : b.FullSourceIndex → Param[I] → Fun) (D : Set (Param[I]))
      (R : ℝ),
      Set.range (imaginaryParameter F (fam.P I)) ⊆ D →
      (∀ w g, IsMeromorphicInCoordinatesOn (fun lam => term w lam g) D) →
      (∀ lam, r.IsRegularParameter hA hT R lam →
        ∀ w : b.FullSourceIndex, term w lam = b.summand hKmin w.val φ lam) →
      let rem := fun lam => fam.constantTerm J (E lam) - ∑ w, term w lam
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => rem lam g) D) →
      HasNonunitaryAffineExponentExpansion J {lam | r.IsRegularParameter hA hT R lam} rem →
      ∀ {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N)),
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        (∀ x w, fam.IsAutomorphicOn hsmooth Kinf rho J (term w (imaginaryParameter F (fam.P I) x))) →
        (∀ x, ∃ (u : Finset (Param[J])) (e : Param[J] → Fun),
          fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J
            (rem (imaginaryParameter F (fam.P I) x)) u e) →
        ∀ x, let lam := imaginaryParameter F (fam.P I) x
          fam.IsWeakConstantTerm hsmooth Kinf rho J (E lam) (∑ w, term w lam)

set_option maxHeartbeats 2500000 in
theorem weakBruhatUnitaryAssembly
    {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
    (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp) :
    WeakBruhatUnitaryAssemblyStatement b hKmin r hA hT := by
  intro φ hc hφ heq E term D R hD hterm hreg rem hrem hexp N d hsmooth rho Kinf hauto hdec x
  let lam := imaginaryParameter F (fam.P I) x
  have hlam : lam ∈ D := hD ⟨x, rfl⟩
  let : FiniteDimensional ℂ (Param[I]) := (hrem 1).1
  let : Module.Free ℂ (Param[I]) := Module.Free.of_divisionRing ℂ (Param[I])
  let chart := (Module.finBasis ℂ (Param[I])).equivFun.symm
  obtain ⟨n, a, m, z, hz, hnon, hkill⟩ := exists_affine_remainder_annihilator _ hexp
  have hOpen := isOpen_setOf_isRegularParameter r hA hT fam.connectedReductive R chart
  obtain ⟨lam₀, hreg₀⟩ := r.regularParameter_nonempty hA hT R
  have hne : {s | r.IsRegularParameter hA hT R (chart s)}.Nonempty :=
    ⟨chart.symm lam₀, by simpa only [Set.mem_ofPred_eq, LinearEquiv.apply_symm_apply] using hreg₀⟩
  have hRoot (i : Fin n) (_ : i ∈ Finset.univ) :
      IsMeromorphicOn 𝓘(ℂ, Fin (Module.finrank ℂ (Param[I])) → ℂ) (z i ∘ chart)
        (chart ⁻¹' D) := by
    have hd := (hrem 1).2 _ chart
    exact (isMeromorphicInCoordinatesOn_univ (hz · · i)).2 _ chart |>.restrict_domain
      hd.1 hd.2.1 (Set.subset_univ _)
  have hzero := fam.splitShiftProduct_eq_zero_of_meromorphic J hOpen hne Finset.univ a m
    (fun i => z i ∘ chart) hRoot (rem ∘ chart) (fun g => (hrem g).2 _ chart)
    (fun s hs => hkill (chart s) hs.1) (chart.symm lam) (by simpa using hlam)
  simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at hzero
  obtain ⟨t, c, _, hgood, hu⟩ := b.exists_unitaryExponentDecomposition_fullSource_of_continuation
    hKmin hc hφ heq r hA hT term D hterm R hreg hsmooth rho x hlam (hauto x)
  obtain ⟨u, e, he⟩ := hdec x
  exact fam.isWeakConstantTerm_of_splitShiftProduct J t u c e hgood hu he Finset.univ a
    (fun i => z i lam) m (fun i _ => hnon x i) hzero

end Langlands.Global.StandardParabolicFamily
