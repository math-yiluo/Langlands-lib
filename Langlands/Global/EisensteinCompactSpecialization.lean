import Langlands.Global.EisensteinAutomorphicLine
import Langlands.Global.EisensteinCompactProjectedLifts
import Langlands.Global.EisensteinCyclicLiftDetection
import Langlands.Global.EisensteinSeedOperatorIdentity

/-! # Actual automorphic quotients from projected Eisenstein specializations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis.Meromorphic Langlands.Automorphic
open Langlands.Automorphic.GroupSchemeFunctions UniformGrowthFrechetSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (P : Module.End ℂ V) [FiniteDimensional ℂ P.range]

/-- The constant seeds obtained from a basis of the compact projection range. -/
def compactProjectionSeed (i : Fin (Module.finrank ℂ P.range)) : V :=
  (Module.finBasis ℂ P.range i).val

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance specializationGeneralLinearIsAffine :
    IsAffine (GL[F, r + 1] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin (r + 1)) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GL[F, r + 1]
local notation "Operators" => FreeOperatorAlgebra F (r + 1)
local notation "Stable" => StableAutomorphicFunctions F (r + 1)
local notation "I" => Fin (Module.finrank ℂ (LinearMap.range P))
local notation "Coordinates" => (Fin (Module.finrank ℂ (LinearMap.range P)) → ℂ)

local instance specializationRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance specializationContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance specializationSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance specializationStableAddCommGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance specializationStableComplexModule : Module ℂ Stable := Submodule.module _

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, r + 1] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, r + 1] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, r + 1] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, r + 1])

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F GL[F, r + 1] rho hsmooth hcalc hN hrho R L
local notation "value[" R "," L "]" =>
  UniformGrowthFrechetSpace.toFun F GL[F, r + 1] rho hsmooth hcalc hN hrho R L
local notation "isAut" =>
  IsAutomorphicFunctionOn F GL[F, r + 1] hsmooth hcalc
    (AdelicGroupPoints.rationalSubgroup F GL[F, r + 1])
    (generalLinearStandardInfiniteCompact F (r + 1)) rho

include hG in
/-- Compact-projected continued seeds realize the simple specialization as a
quotient of a stable automorphic free-operator submodule. -/
theorem exists_freeOperatorQuotient_of_compact_projected_seeds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E → Operators →ₐ[ℂ] Module.End ℂ V) (z : E)
    (hHol : ∀ w : I →₀ Operators,
      (fun t => operatorLinearCombination (T t) (compactProjectionSeed P) w) ∈
        finiteHolomorphicSections E V)
    (hProjection : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S →
      ∃ b : Operators, ∀ t v, v ∈ S → T t b v = P v)
    (f : I → E → Adeles → ℂ)
    (hLocal : ∀ i z, ∃ B : TopologicalSpace.Opens E, z ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, r + 1])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, r + 1])) ∧
        ∃ (g : B → Growth[R, L]) (D : Set B), IsMeromorphicOn 𝓘(ℂ, E) g D ∧
          ∀ t ∈ D, value[R, L] (g t) = f i t.val ∧ isAut (f i t.val))
    (hInject : ∃ t₀, t₀ ∈ regularParameterSet univ (continuedLinearCombination f) ∧
      Function.Injective (continuedLinearCombination f t₀))
    (hAnchor : ∀ (w : I →₀ Operators) (c : E → Coordinates),
      (∀ t, operatorLinearCombination (T t) (compactProjectionSeed P) w =
        ∑ i, c t i • compactProjectionSeed P i) →
      ∃ C : Set E, IsOpen C ∧ C.Nonempty ∧
        ∀ t ∈ C, scalarSeedOperatorCombination F (r + 1) f w t =
          continuedLinearCombination f t (c t))
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (a : Operators →ₐ[ℂ] Module.End ℂ W) (ha : Representation.IsIrreducible a.toMonoidHom) :
    letI := moduleOfAlgebraAction (T z)
    letI := moduleOfAlgebraAction a
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
    ∀ (S : Submodule Operators V) (q : S →ₗ[Operators] W), Function.Surjective q →
      ∀ y : W, y ≠ 0 →
        (∀ x : S, q x = y → ∃ x' : S, x'.val = P x.val ∧ q x' = y) →
        ∃ U : Submodule Operators Stable, ∃ p : U →ₗ[Operators] W, Function.Surjective p := by
  let := moduleOfAlgebraAction (T z)
  let := moduleOfAlgebraAction a
  let := (isSimpleModule_iff_irreducible_algebraAction a).mpr ha
  let := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
  intro S q hq y hy hπ
  let basis := Module.finBasis ℂ P.range
  let seed := compactProjectionSeed P
  let J := S.comap (operatorLinearCombination (T z) seed)
  let specialize := operatorSeedSpecialization (T z) seed S
  let qJ := q.comp specialize
  have hqJ : Function.Surjective qJ := by
    obtain ⟨x, hx⟩ := hq y
    obtain ⟨x', hx', hq'⟩ := hπ x hx
    have hmem : x'.val ∈ P.range := ⟨x.val, hx'.symm⟩
    exact surjective_comp_operatorSeedSpecialization (T z) basis S q x' hmem (hq'.trans_ne hy)
  have hLocal' (i : I) (x : E) : ∃ B : TopologicalSpace.Opens E, x ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, r + 1])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, r + 1])) ∧
        ∃ (g : B → Growth[R, L]) (D : Set B), IsMeromorphicOn 𝓘(ℂ, E) g D ∧
          ∀ t ∈ D, value[R, L] (g t) = f i t.val := by
    obtain ⟨B, hx, R, L, hL, g, D, hg, hf⟩ := hLocal i x
    exact ⟨B, hx, R, L, hL, g, D, hg, fun t ht => (hf t ht).1⟩
  choose B hB R L hL g D hg hf using fun i => hLocal i z
  obtain ⟨δ, hδ, R₀, L₀, hL₀, b, M, U₀, hb, hM, hU₀o, hU₀ball, hclosure, hReg⟩ :=
    exists_common_normalization_of_meromorphic F GL[F, r + 1] rho hsmooth hcalc hN hrho
      z B hB R L hL g D hg f (fun i t ht => (hf i t ht).1)
  have hNReg (t : E) (ht : t ∈ U₀) : b t ≠ 0 ∧
      ∀ c, value[R₀, L₀] (M t c) = b t • continuedLinearCombination f t c :=
    ⟨(hReg t ht).2.1, (hReg t ht).2.2⟩
  have hAut (i : I) (t : E) (ht : t ∈ U₀) : isAut (f i t) := by
    obtain ⟨s, hs, rfl⟩ := (hReg t ht).1 i
    exact (hf i s hs).2
  have hLocalNum := continuedLinearCombination_hasLocalHolomorphicNumerators F GL[F, r + 1]
    rho hsmooth hcalc hN hrho f hLocal'
  obtain ⟨t₀, ht₀, hInj⟩ := hInject
  obtain ⟨t₁, _, hUo, hU, hzU, hOo, h1O, hOU, hMi, hWeak, hForms, _⟩ :=
    exists_normalizedAutomorphicLine F (r + 1) rho hsmooth hcalc hN hrho hG R₀ L₀ hL₀
      z δ hδ f hLocalNum ht₀ hInj b M hM U₀ hU₀o hU₀ball hclosure hNReg hAut
  let line := AffineMap.lineMap (k := ℂ) z t₁
  let U := normalizedAutomorphicLineDomain z t₁ δ
  let O := line ⁻¹' U₀
  let valueMap : Growth[R₀, L₀] →ₗ[ℂ] (Adeles → ℂ) :=
    ⟨⟨value[R₀, L₀], fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let Ev (s : ℂ) : Coordinates →ₗ[ℂ] (Adeles → ℂ) := valueMap.comp (M (line s))
  have hEv (c : Coordinates) (x : Adeles) : AnalyticOnNhd ℂ (fun t => Ev t c x) U :=
    (hWeak c (UniformGrowthFrechetSpace.evaluation F GL[F, r + 1] rho hsmooth hcalc hN hrho R₀ L₀ x)).analyticOnNhd hUo
  have hEv1 : Function.Injective (Ev 1) := by
    change Function.Injective (fun c => value[R₀, L₀] (M (line 1) c))
    rw [show line 1 = t₁ from AffineMap.lineMap_apply_one z t₁]
    exact hMi
  let G (i : I) (s : ℂ) := M (line s) (Pi.single i 1)
  have hGForm (i : I) (s : ℂ) (hs : s ∈ O) : isAut (value[R₀, L₀] (G i s)) := hForms s hs _
  let C (k : ℕ) :=
    freeOperatorTaylorCoefficient F (r + 1) rho hsmooth hcalc hN hrho R₀ L₀
      hG hL₀ hU hUo hOo hOU ⟨1, h1O⟩ G (fun i => hWeak (Pi.single i 1)) hGForm ⟨0, hzU⟩ k
  let c (k : ℕ) : J →ₗ[Operators] Stable := (C k).comp J.subtype
  refine exists_subquotient_of_holomorphic_cyclic_lifts (J := ↥J) (R := Operators) (Z := Stable)
    U hU 0 1 hzU (hOU h1O) Ev hEv hEv1
    qJ hqJ c (stableGeneralLinearEvaluation F (r + 1)) y ?_
  intro w hw
  let v (t : E) := operatorLinearCombination (T t) seed w.val
  obtain ⟨B₀, hB₀, hMem⟩ := FiniteHolomorphicSections.exists_finiteDimensional_range (hHol w.val)
  obtain ⟨a₀, hₐ⟩ := hProjection B₀ hB₀
  let lift : J := a₀ • w
  let projected (t : E) : P.range := P.rangeRestrict (v t)
  let coord (t : E) : Coordinates := basis.equivFun (projected t)
  have hCoordMem : coord ∈ finiteHolomorphicSections E Coordinates :=
    FiniteHolomorphicSections.map_mem (basis.equivFun.toLinearMap.comp P.rangeRestrict) (hHol w.val)
  have hdiff (i : I) : Differentiable ℂ (fun t => coord t i) :=
    FiniteHolomorphicSections.differentiable_apply hCoordMem (LinearMap.proj i)
  have hEval (t : E) : operatorLinearCombination (T t) seed lift.val = (projected t).val := by
    let := moduleOfAlgebraAction (T t)
    have he := (operatorLinearCombination (T t) seed).map_smul a₀ w.val
    exact he.trans (hₐ t _ (hMem t))
  have hsum (t : E) :
      operatorLinearCombination (T t) seed lift.val = ∑ i, coord t i • seed i := by
    rw [hEval]
    have he := congrArg P.range.subtype (basis.sum_repr (projected t)).symm
    simpa only [map_sum, map_smul, Submodule.subtype_apply, coord, Module.Basis.equivFun_apply,
      compactProjectionSeed, seed] using he
  have hnonzero : coord z ≠ 0 := by
    intro hzero
    have hz : projected z = 0 := basis.equivFun.injective (hzero.trans (map_zero _).symm)
    obtain ⟨x, hx, hqx⟩ := hπ (specialize w) hw
    have hx₀ : x.val = 0 := hx.trans (congrArg Subtype.val hz)
    have : x = 0 := Subtype.ext hx₀
    exact hy (by simpa only [this, map_zero] using hqx.symm)
  obtain ⟨C₀, hC₀, hCne, hIdent⟩ := hAnchor lift.val coord hsum
  let curve (s : ℂ) := coord (line s)
  have hline : Differentiable ℂ line := by
    intro s
    change DifferentiableAt ℂ (fun w : ℂ => AffineMap.lineMap z t₁ w) s
    simp_rw [AffineMap.lineMap_apply_module']
    exact (differentiableAt_id.smul (differentiableAt_const (t₁ - z))).add_const _
  refine ⟨⟨lift, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w), curve, ?_, ?_, ?_⟩⟩
  · intro l
    exact ((FiniteHolomorphicSections.differentiable_apply hCoordMem l).comp hline).analyticAt _
  · simpa only [curve, line, AffineMap.lineMap_apply_zero] using hnonzero
  · intro k x
    change stableGeneralLinearEvaluation F (r + 1) (C k lift.val) x = _
    have hvalue := evaluate_freeOperatorTaylorCoefficient F (r + 1) rho hsmooth hcalc hN hrho R₀ L₀
      hG hL₀ hU hUo hOo hOU ⟨1, h1O⟩ G (fun i => hWeak (Pi.single i 1)) hGForm ⟨0, hzU⟩ k lift.val x
    change stableGeneralLinearEvaluation F (r + 1) (C k lift.val) x = _ at hvalue
    rw [hvalue]
    congr 1
    apply Filter.EventuallyEq.iteratedDeriv_eq
    apply Filter.eventually_of_mem (hUo.mem_nhds hzU)
    intro t ht
    exact normalized_seedOperatorCombination_eqOn_of_anchor F (r + 1) rho hsmooth hcalc hN hrho
      f lift.val hLocal' coord hdiff hC₀ hCne hIdent hδ R₀ L₀ M b hb hM hU₀o hU₀ball hclosure hNReg x
      (show line t ∈ Metric.ball z δ from ht)

include hG in
/-- A compact-projected simple specialization is automorphic when the
continued seed family has an injective regular member and the operator identities
hold on open anchors. The quotient retains the supplied finite action. -/
theorem exists_automorphic_subquotient_of_compact_projected_seeds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E → Operators →ₐ[ℂ] Module.End ℂ V) (z : E)
    (hHol : ∀ w : I →₀ Operators,
      (fun t => operatorLinearCombination (T t) (compactProjectionSeed P) w) ∈
        finiteHolomorphicSections E V)
    (hProjection : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S →
      ∃ b : Operators, ∀ t v, v ∈ S → T t b v = P v)
    (f : I → E → Adeles → ℂ)
    (hLocal : ∀ i z, ∃ B : TopologicalSpace.Opens E, z ∈ B ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, r + 1])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, r + 1])) ∧
        ∃ (g : B → Growth[R, L]) (D : Set B), IsMeromorphicOn 𝓘(ℂ, E) g D ∧
          ∀ t ∈ D, value[R, L] (g t) = f i t.val ∧ isAut (f i t.val))
    (hInject : ∃ t₀, t₀ ∈ regularParameterSet univ (continuedLinearCombination f) ∧
      Function.Injective (continuedLinearCombination f t₀))
    (hAnchor : ∀ (w : I →₀ Operators) (c : E → Coordinates),
      (∀ t, operatorLinearCombination (T t) (compactProjectionSeed P) w =
        ∑ i, c t i • compactProjectionSeed P i) →
      ∃ C : Set E, IsOpen C ∧ C.Nonempty ∧
        ∀ t ∈ C, scalarSeedOperatorCombination F (r + 1) f w t =
          continuedLinearCombination f t (c t))
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (a : Operators →ₐ[ℂ] Module.End ℂ W) (ha : Representation.IsIrreducible a.toMonoidHom)
    (fin : Representation ℂ (FiniteAdelicGL F (r + 1)) W)
    (hfin : ∀ g, a (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) = fin g) :
    letI := moduleOfAlgebraAction (T z)
    letI := moduleOfAlgebraAction a
    ∀ (S : Submodule Operators V) (q : S →ₗ[Operators] W), Function.Surjective q →
      ∀ y : W, y ≠ 0 →
        (∀ x : S, q x = y → ∃ x' : S, x'.val = P x.val ∧ q x' = y) →
        ∃ Q : IrreducibleOperatorSubquotient F r, Nonempty (Q.subquotient.finiteRepresentation.Equiv fin) := by
  let := moduleOfAlgebraAction (T z)
  let := moduleOfAlgebraAction a
  intro S q hq y hy hπ
  obtain ⟨U, p, hp⟩ := exists_freeOperatorQuotient_of_compact_projected_seeds P F r rho hsmooth hcalc
    hN hrho hG T z hHol hProjection f hLocal hInject hAnchor a ha S q hq y hy hπ
  exact exists_irreducibleOperatorSubquotient_of_freeModule F r a ha fin hfin U p hp

end Langlands.Global.EisensteinJet
