import Langlands.Global.AdelicEisensteinHarishChandraEquations
import Langlands.Global.AdelicEisensteinCuspidalTestSystemStatement
import Langlands.Global.AdelicEisensteinCommonGrowthStatement
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphyStatement
import Langlands.Global.AdelicLocalFinitenessProductBridge
import Langlands.Global.AdelicLocalFinitenessGroupData
import Langlands.Global.AdelicPositiveTorusSplitComponentStatement
import Langlands.Global.AdelicEisensteinScalarEquations
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances

/-! # Domination of the Eisenstein characterizing system by `Ξ_main`, as a reduction

Bernstein–Lapid, Proposition 8.4 with Lemma 8.1 (number field case): the statement
`EisensteinSystemDominationStatement` follows from the Harish-Chandra equations (8.2a), the
cuspidal tests (8.2b) with (8.3), (6.21), (6.22), a common growth space for regular Eisenstein
series, the vanishing criterion (8.1), automorphy of the solutions of `Ξ_main`, and the
comparison of positive torus points with split-component points. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The coefficients of a finite product of polynomial families with entire coefficients are
entire. -/
theorem differentiable_coeff_finset_prod {I : Type*} (S : Finset I) {n : ℕ}
    (D : I → (Fin n → ℂ) → Polynomial ℂ)
    (hD : ∀ i k, Differentiable ℂ fun s => (D i s).coeff k) (k : ℕ) :
    Differentiable ℂ fun s => (∏ i ∈ S, D i s).coeff k := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiable_const _
  | insert a S ha ih =>
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    exact Differentiable.fun_sum fun x _ => (hD a x.1).mul (ih x.2)

section Growth

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {hN : 0 < N} {hrho : IsClosedSubgroup rho} {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}

/-- Every element of `𝔉^R_L` has moderate growth (the order-zero bound). -/
theorem hasModerateGrowthFunction_toFun_uniformGrowth
    (v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :
    HasModerateGrowthFunction F G rho
      (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) := by
  obtain ⟨C, hC⟩ := (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).2.2 1
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), R, fun g => ?_⟩
  have hg := hC g
  rw [map_one, Module.End.one_apply] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (le_max_left C 1)
    (Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos (F := F) (G := G)
      (rho := rho) hN g).le R))

end Growth

/-- Regularity is antitone in the bound. -/
private theorem isRegularParameter_of_le_bound {F : Type u} [Field F] [NumberField F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) {R R' : ℝ} (hRR : R ≤ R')
    {lam : ComplexCharacterParameter F P} (h : r.IsRegularParameter hA hT R' lam) :
    r.IsRegularParameter hA hT R lam :=
  fun α hα => lt_of_le_of_lt hRR (h α hα)

/-- Bernstein–Lapid, Proposition 8.4 with Lemma 8.1 (number field case), as a reduction:
`EisensteinSystemDominationStatement` follows from

* `hHC`: the Harish-Chandra equations (8.2a) of the Eisenstein series;
* `hcusp`: the cuspidal tests (8.2b) with (8.3), (6.21) and (6.22);
* `hgrowth`: a common space `𝔉^R_L` for regular Eisenstein series on bounded sets;
* `hvan`: the parabolic cuspidal vanishing criterion (8.1);
* `hZ`: automorphy of the solutions of `Ξ_main` (Lemma 8.1 with Theorem 7.2);
* `hpos`: positive torus points killed by the simple roots of `J` lie in `A_J`. -/
theorem eisensteinSystemDomination_of
    (hHC : EisensteinHarishChandraEquationsStatement.{u})
    (hcusp : EisensteinCuspidalTestSystemStatement.{u})
    (hgrowth : EisensteinCommonGrowthStatement.{u})
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (hZ : LocalFinitenessSolutionAutomorphyStatement.{u})
    (hpos : PositiveTorusSplitComponentStatement.{u}) :
    EisensteinSystemDominationStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hN hrho hsmooth hcalc
    φ hKmax hφ
  obtain ⟨R₁', hHC'⟩ := hHC F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax
    hrho hφ
  obtain ⟨R₂, 𝓕, K', hK'max, hK'Iw, hcusp'⟩ := hcusp F G P M U A p iU l a r hA hT hG hU K hK rho
    hN hrho hsmooth hcalc φ hKmax hφ
  obtain ⟨R₃, hgrowth'⟩ := hgrowth F G P M U A p iU l a r hA hT hG hU K hK rho hN hrho hsmooth
    hcalc φ hKmax hφ
  refine ⟨max (max R₁' R₂) R₃, fun n e W hW => ?_⟩
  have : Finite (StandardIndex F G 𝓕.i 𝓕.ν) :=
    (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i
      𝓕.ν).finite_subsets.to_subtype
  let : Fintype (StandardIndex F G 𝓕.i 𝓕.ν) := Fintype.ofFinite _
  obtain ⟨Ua, hUa, u, hu, t, nZ, z, hdata⟩ :=
    exists_isLocalFinitenessGroupData (F := F) 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic
  -- the maximal standard parabolics `P_α` and the positive points `a_α ∈ A_{P_α}`
  let Jα : simpleRelativeRoots 𝓕.i 𝓕.ν → StandardIndex F G 𝓕.i 𝓕.ν :=
    fun α => ⟨simpleRelativeRoots 𝓕.i 𝓕.ν \ {α.1}, Set.sdiff_subset⟩
  have haα : ∀ α, ∃ b ∈ 𝓕.positiveSplitComponent (Jα α),
      map F (𝓕.P (Jα α)) G (𝓕.p (Jα α)) b = map F 𝓕.T.toGrp G 𝓕.i (t α) := fun α =>
    hpos F G 𝓕 (Jα α) (t α) (hdata.2.1 α) fun β hβ =>
      hdata.2.2.1 α ⟨β, hβ.1⟩ fun h => hβ.2 (congrArg Subtype.val h)
  choose aα haα_mem haα_eq using haα
  have hz' : ∀ j, ∃ b ∈ 𝓕.positiveSplitComponent 𝓕.top,
      map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) b = map F 𝓕.T.toGrp G 𝓕.i (z j) := fun j =>
    hpos F G 𝓕 𝓕.top (z j) (hdata.2.2.2.2.2.1 j) fun β hβ =>
      hdata.2.2.2.2.2.2.1 j ⟨β, hβ⟩
  choose az haz_mem haz_eq using hz'
  obtain ⟨Idx₁, m, h, b, c, hh, hb, hc, hc0, hHCeq⟩ := hHC' n e
  obtain ⟨D, deg, hDmon, hDdiff, hsys⟩ := hcusp' n e
  -- the data of `Ξ_main` on any open set of parameters
  let dat : ∀ W' : TopologicalSpace.Opens (Fin n → ℂ),
      LocalFinitenessData F G (simpleRelativeRoots 𝓕.i 𝓕.ν) nZ n W' := fun W' =>
    { Idx := Idx₁
      m := m
      h := h
      b := fun i k s => b i k s.1
      c := fun i s => c i s.1
      degree := fun α => ∑ Q, deg (Jα α) ⟨aα α, haα_mem α⟩ Q
      D := fun α s => ∏ Q, D (Jα α) ⟨aα α, haα_mem α⟩ Q s.1
      centralDegree := fun j => ∑ Q, deg 𝓕.top ⟨az j, haz_mem j⟩ Q
      centralD := fun j s => ∏ Q, D 𝓕.top ⟨az j, haz_mem j⟩ Q s.1 }
  have hadm : ∀ W', (dat W').IsAdmissible := fun W' => by
    refine ⟨fun i k => (hh i k).1, fun i k => isHolomorphicOn_opens_of_differentiable (hb i k),
      fun i => isHolomorphicOn_opens_of_differentiable (hc i), fun s => hc0 s.1,
      fun α s => ⟨Polynomial.monic_prod_of_monic _ _ fun Q _ => (hDmon _ _ Q s.1).1, ?_⟩,
      fun α k => isHolomorphicOn_opens_of_differentiable
        (differentiable_coeff_finset_prod _ _ (hDdiff _ _) k),
      fun j s => ⟨Polynomial.monic_prod_of_monic _ _ fun Q _ => (hDmon _ _ Q s.1).1, ?_, ?_⟩,
      fun j k => isHolomorphicOn_opens_of_differentiable
        (differentiable_coeff_finset_prod _ _ (hDdiff _ _) k)⟩
    · change (∏ Q, D (Jα α) ⟨aα α, haα_mem α⟩ Q s.1).natDegree =
        ∑ Q, deg (Jα α) ⟨aα α, haα_mem α⟩ Q
      rw [Polynomial.natDegree_prod_of_monic _ _ fun Q _ => (hDmon _ _ Q s.1).1]
      exact Finset.sum_congr rfl fun Q _ => (hDmon _ _ Q s.1).2.1
    · change (∏ Q, D 𝓕.top ⟨az j, haz_mem j⟩ Q s.1).natDegree =
        ∑ Q, deg 𝓕.top ⟨az j, haz_mem j⟩ Q
      rw [Polynomial.natDegree_prod_of_monic _ _ fun Q _ => (hDmon _ _ Q s.1).1]
      exact Finset.sum_congr rfl fun Q _ => (hDmon _ _ Q s.1).2.1
    · change (∏ Q, D 𝓕.top ⟨az j, haz_mem j⟩ Q s.1).coeff 0 ≠ 0
      rw [Polynomial.coeff_zero_prod]
      exact Finset.prod_ne_zero_iff.2 fun Q _ => (hDmon _ _ Q s.1).2.2
  obtain ⟨L, hLo, hLc, R₁, hR₁⟩ := hgrowth' n e (W : Set (Fin n → ℂ)) hW
  refine ⟨𝓕.T, 𝓕.i, 𝓕.ν, 𝓕.maximalSplit, 𝓕.generic, Ua, hUa, u, hu, t, nZ, z, hdata, dat ⊤,
    hadm ⊤, L, hLo, hLc, R₁, fun R hR => ?_⟩
  obtain ⟨Idx₂, eqn₂, c₂, hana₂, hcl2, hcl3, hcl4⟩ := hsys L hLo hLc R
  let X := dat W
  let eqs : (X.Idx × AdelicGroupPoints F G) ⊕ Idx₂ → W →
      UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ :=
    Sum.elim (X.convolutionEquation rho hN hrho hsmooth hcalc R L (hadm W))
      (fun j s => eqn₂ j s.1)
  let cc : (X.Idx × AdelicGroupPoints F G) ⊕ Idx₂ → W → ℂ :=
    Sum.elim (fun _ _ => 0) (fun j s => c₂ j s.1)
  have hval : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) (Subtype.val : W → Fin n → ℂ) :=
    (contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero
  have hsol : ∀ (s : W) v, v ∈ systemSolutions eqs cc s ↔
      v ∈ systemSolutions (X.convolutionEquation rho hN hrho hsmooth hcalc R L (hadm W))
          (fun _ _ => (0 : ℂ)) s ∧ v ∈ systemSolutions eqn₂ c₂ s.1 :=
    fun s v => ⟨fun hv => ⟨fun ix => hv (Sum.inl ix), fun j => hv (Sum.inr j)⟩,
      fun hv => by rintro (ix | j); exacts [hv.1 ix, hv.2 j]⟩
  have hdom : ∀ (s : W) v, v ∈ systemSolutions eqs cc s →
      v ∈ (dat ⊤).solutions u (fun α => map F 𝓕.T.toGrp G 𝓕.i (t α))
        (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j)) rho hN hrho hsmooth hcalc R L
        ⟨s.1, trivial⟩ := by
    intro s v hv
    obtain ⟨hv1, hv2⟩ := (hsol s v).1 hv
    have hmod := hasModerateGrowthFunction_toFun_uniformGrowth v
    refine ⟨(X.mem_systemSolutions_convolutionEquation_iff rho hN hrho hsmooth hcalc R L
      (hadm W) s v).1 hv1, fun α => ?_, fun j => ?_⟩
    · refine 𝓕.isTranslationPolynomialSolution_subgroupConstantTerm rho hvan K' hK'max hK'Iw hN
        hrho (Jα α) _ hmod ⟨aα α, haα_mem α⟩ Finset.univ (fun Q _ => Finset.mem_univ Q)
        (fun Q => D (Jα α) ⟨aα α, haα_mem α⟩ Q s.1) (fun Q hQ => ?_) (u α) (hdata.1 α) _
        (haα_eq α)
      convert hcl2 s.1 v hv2 (Jα α) ⟨aα α, haα_mem α⟩ Q hQ using 1
      exact funext fun g => aeval_adelicLeftShift_apply _ _ _ g
    · refine 𝓕.isTranslationPolynomialSolution_top rho hvan K' hK'max hK'Iw hN hrho _ hmod
        ⟨az j, haz_mem j⟩ Finset.univ (fun Q => Finset.mem_univ Q)
        (fun Q => D 𝓕.top ⟨az j, haz_mem j⟩ Q s.1) (fun Q => ?_) _ (haz_eq j)
      convert hcl2 s.1 v hv2 𝓕.top ⟨az j, haz_mem j⟩ Q (𝓕.le_top Q) using 1
      exact funext fun g => aeval_adelicLeftShift_apply _ _ _ g
  have haut : ∀ (s : W) v, v ∈ systemSolutions eqs cc s →
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
        (K.comap (ofInfinite F G).toMonoidHom) rho
        (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) :=
    fun s v hv => hZ F G 𝓕.T 𝓕.i 𝓕.ν hG 𝓕.maximalSplit 𝓕.generic Ua u t nZ z hdata rho hN hrho
      hsmooth hcalc n ⊤ (dat ⊤) (hadm ⊤) (K.comap (ofInfinite F G).toMonoidHom)
      (fun i k => (hh i k).2.2) L hLo hLc R ⟨s.1, trivial⟩ v (hdom s v hv)
  refine ⟨_, eqs, cc, ⟨?_, ?_⟩, fun s v hv => hdom s v hv, fun s hs => ?_, haut⟩
  · rintro (ix | j)
    · exact (X.isAnalyticSystem_convolutionEquation rho hN hrho hsmooth hcalc R L (hadm W)).1 ix
    · intro v ν'
      exact ((mdifferentiableOn_univ.1 (hana₂.1 j v ν')).comp hval).mdifferentiableOn
  · rintro (ix | j)
    · intro ν'
      exact mdifferentiableOn_const (I := 𝓘(ℂ, Fin n → ℂ)) (I' := 𝓘(ℂ, ℂ)) (c := ν' 0)
    · intro ν'
      exact ((mdifferentiableOn_univ.1 (hana₂.2 j ν')).comp hval).mdifferentiableOn
  · have hs1 : r.IsRegularParameter hA hT R₁' (e s) :=
      isRegularParameter_of_le_bound r hA hT ((le_max_left _ _).trans (le_max_left _ _)) hs
    have hs2 : r.IsRegularParameter hA hT R₂ (e s) :=
      isRegularParameter_of_le_bound r hA hT ((le_max_right _ _).trans (le_max_left _ _)) hs
    have hs3 : r.IsRegularParameter hA hT R₃ (e s) :=
      isRegularParameter_of_le_bound r hA hT (le_max_right _ _) hs
    obtain ⟨v₀, hv₀⟩ := hR₁ R hR s.1 s.2 hs3
    have hv₀sol : v₀ ∈ systemSolutions eqs cc s := (hsol s v₀).2
      ⟨(X.mem_systemSolutions_convolutionEquation_iff rho hN hrho hsmooth hcalc R L (hadm W) s
        v₀).2 fun i x => by rw [hv₀]; exact hHCeq s.1 hs1 i x, hcl3 s.1 hs2 v₀ hv₀⟩
    refine ⟨v₀, hv₀, Set.eq_singleton_iff_unique_mem.2 ⟨hv₀sol, fun v hv => ?_⟩⟩
    apply toFun_injective F G rho hsmooth hcalc hN hrho R L
    rw [hv₀]
    exact hcl4 s.1 hs2 v ((hsol s v).1 hv).2 (haut s v hv)

/-- The six premises of the reduction `eisensteinSystemDomination_of`, as one proposition:
the Harish-Chandra equations (8.2a), the cuspidal tests (8.2b) with (8.3), (6.21), (6.22),
a common growth space for regular Eisenstein series, the vanishing criterion (8.1), automorphy
of the solutions of `Ξ_main` (Lemma 8.1 with Theorem 7.2), and the comparison of positive
torus points with split-component points. -/
def EisensteinSystemDominationPremises : Prop :=
  EisensteinHarishChandraEquationsStatement.{u} ∧ EisensteinCuspidalTestSystemStatement.{u} ∧
    EisensteinCommonGrowthStatement.{u} ∧ ParabolicCuspidalVanishingStatement.{u} ∧
    LocalFinitenessSolutionAutomorphyStatement.{u} ∧ PositiveTorusSplitComponentStatement.{u}

/-- `EisensteinSystemDominationStatement` follows from the conjunction of its premises. -/
theorem eisensteinSystemDomination_of_premises (h : EisensteinSystemDominationPremises.{u}) :
    EisensteinSystemDominationStatement.{u} :=
  eisensteinSystemDomination_of h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end Langlands.Global
