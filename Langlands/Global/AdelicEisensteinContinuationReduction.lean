import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicEisensteinAnalyticSystemStatement
import Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement
import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Meromorphic continuation of Eisenstein series from an analytic system

The principle of meromorphic continuation (holomorphic part,
`MeromorphicContinuationHolomorphicStatement`) and the analytic system characterizing
Eisenstein series (`EisensteinAnalyticSystemStatement`) imply the meromorphic continuation of
Eisenstein series (`EisensteinMeromorphicContinuationStatement`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set Metric
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

section Gluing

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X]
  {J : Type*} (Sp : J → Type*) [∀ j, AddCommGroup (Sp j)] [∀ j, Module ℂ (Sp j)]
  [∀ j, TopologicalSpace (Sp j)]
  (toFun : ∀ j, Sp j → Y → ℂ) (Ψ : X → Y → ℂ) (Reg A : Set X)

/-- `g` is the value at `lam` of a meromorphic continuation of `Ψ` from `Reg`: there are
linear coordinates `e`, a convex open set `B` of coordinates containing the coordinates of the
anchor `A`, and a meromorphic function `v` on `B` with values in one of the spaces `Sp j`,
holomorphic on `U`, whose underlying functions agree with `Ψ` at the points of `U` in `Reg`,
and whose underlying function at a point of `U` over `lam` is `g`. -/
def IsContinuationValue (lam : X) (g : Y → ℂ) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (B : TopologicalSpace.Opens (Fin n → ℂ)) (j : J)
    (U : Set B) (v : B → Sp j),
    Convex ℝ (B : Set (Fin n → ℂ)) ∧ e ⁻¹' A ⊆ B ∧ IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) v U ∧
    (∀ s ∈ U, e (s : Fin n → ℂ) ∈ Reg → toFun j (v s) = Ψ (e s)) ∧
    ∃ s ∈ U, e (s : Fin n → ℂ) = lam ∧ toFun j (v s) = g

open Classical in
/-- The glued continuation: the common value of all meromorphic continuations at `lam` when
there is one, and `Ψ lam` otherwise. -/
def gluedContinuation (lam : X) : Y → ℂ :=
  if h : ∃ g, IsContinuationValue Sp toFun Ψ Reg A lam g then h.choose else Ψ lam

variable {Sp toFun Ψ Reg A}

/-- Two meromorphic continuations have the same value: the identity theorem in linear
coordinates, applied pointwise on `Y` through continuous evaluation forms. -/
theorem IsContinuationValue.unique (ev : ∀ j, Y → Sp j →L[ℂ] ℂ)
    (hev : ∀ j y v, ev j y v = toFun j v y) (hAReg : A ⊆ Reg) (hAne : A.Nonempty)
    (hAo : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' A)) {lam : X} {g₁ g₂ : Y → ℂ}
    (h₁ : IsContinuationValue Sp toFun Ψ Reg A lam g₁)
    (h₂ : IsContinuationValue Sp toFun Ψ Reg A lam g₂) : g₁ = g₂ := by
  obtain ⟨n₁, e₁, B₁, j₁, U₁, v₁, hB₁, hAB₁, hv₁, hreg₁, s₁, hs₁, hes₁, hg₁⟩ := h₁
  obtain ⟨n₂, e₂, B₂, j₂, U₂, v₂, hB₂, hAB₂, hv₂, hreg₂, s₂, hs₂, hes₂, hg₂⟩ := h₂
  funext y
  rw [← hg₁, ← hg₂, ← hev, ← hev]
  exact IsMeromorphicOn.eq_of_linearCoordinates e₁ e₂ (hAo n₁ e₁) hAne hB₁ hB₂ hAB₁ hAB₂
    hv₁ hv₂ (ev j₁ y) (ev j₂ y) (fun lam => Ψ lam y)
    (fun s hs hsA => by rw [hev, hreg₁ s hs (hAReg hsA)])
    (fun s hs hsA => by rw [hev, hreg₂ s hs (hAReg hsA)]) hs₁ hs₂ (hes₁.trans hes₂.symm)

theorem gluedContinuation_eq (ev : ∀ j, Y → Sp j →L[ℂ] ℂ)
    (hev : ∀ j y v, ev j y v = toFun j v y) (hAReg : A ⊆ Reg) (hAne : A.Nonempty)
    (hAo : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' A)) {lam : X} {g : Y → ℂ}
    (h : IsContinuationValue Sp toFun Ψ Reg A lam g) :
    gluedContinuation Sp toFun Ψ Reg A lam = g := by
  have hex : ∃ g, IsContinuationValue Sp toFun Ψ Reg A lam g := ⟨g, h⟩
  have key : ∀ hh : ∃ g, IsContinuationValue Sp toFun Ψ Reg A lam g, hh.choose = g :=
    fun hh => hh.choose_spec.unique ev hev hAReg hAne hAo h
  unfold gluedContinuation
  split_ifs
  exact key _

theorem gluedContinuation_of_mem (lam : X) (hlam : lam ∈ Reg) :
    gluedContinuation Sp toFun Ψ Reg A lam = Ψ lam := by
  rw [gluedContinuation]
  split_ifs with hex
  · obtain ⟨n, e, B, j, U, v, -, -, -, hreg, s, hs, hes, hg⟩ := hex.choose_spec
    rw [← hg, hreg s hs (by rw [hes]; exact hlam), hes]
  · rfl

end Gluing

section Step

/-- A convex nonempty open set of a normed space is a connected space. -/
theorem connectedSpace_of_convex {n : ℕ} {B : TopologicalSpace.Opens (Fin n → ℂ)}
    (hB : Convex ℝ (B : Set (Fin n → ℂ))) (hne : (B : Set (Fin n → ℂ)).Nonempty) :
    ConnectedSpace B :=
  isConnected_iff_connectedSpace.mp ⟨hne, hB.isPreconnected⟩

/-- The zero function is meromorphic on a connected open set, holomorphic everywhere. -/
theorem isMeromorphicOn_zero {n : ℕ} {B : TopologicalSpace.Opens (Fin n → ℂ)}
    [ConnectedSpace B] {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (0 : B → V) univ := by
  have hhol : ∀ U : Set B, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (0 : B → V) U := by
    intro U m
    simpa using (mdifferentiableOn_const : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
      (fun _ : B => (0 : ℂ)) U)
  refine ⟨isOpen_univ, dense_univ, hhol univ, fun s₀ => ⟨univ, isOpen_univ,
    isConnected_univ, mem_univ _, fun _ => 1, 0, mdifferentiableOn_const, ⟨s₀, mem_univ _,
    one_ne_zero⟩, hhol univ, fun s _ => ?_⟩⟩
  simp

/-- The principle of meromorphic continuation on a convex open set of coordinates: if the
system has a unique solution at every point of a nonempty open set `O`, its unique solutions
form a meromorphic function on the locus where they exist. -/
theorem exists_meromorphic_unique_solution
    (hprin : MeromorphicContinuationHolomorphicStatement.{0, 0, u, u, 0})
    {n : ℕ} (B : TopologicalSpace.Opens (Fin n → ℂ)) (hBc : Convex ℝ (B : Set (Fin n → ℂ)))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [LocallyConvexSpace ℝ V] [T2Space V]
    {Idx : Type u} (eqn : Idx → B → V →L[ℂ] ℂ) (c : Idx → B → ℂ)
    (han : IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c)
    (hlft : IsLocallyFiniteType 𝓘(ℂ, Fin n → ℂ) (systemSolutions eqn c))
    {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hOB : O ⊆ B) (hOne : O.Nonempty)
    (huniq : ∀ s : B, (s : Fin n → ℂ) ∈ O → s ∈ uniqueSolutionLocus eqn c) :
    ∃ v : B → V, (∀ s ∈ uniqueSolutionLocus eqn c, systemSolutions eqn c s = {v s}) ∧
      IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) v (uniqueSolutionLocus eqn c) := by
  obtain ⟨t, ht⟩ := hOne
  have : ConnectedSpace B := connectedSpace_of_convex hBc ⟨t, hOB ht⟩
  have hint : (interior (uniqueSolutionLocus eqn c)).Nonempty :=
    ⟨⟨t, hOB ht⟩, interior_maximal (fun s hs => huniq s hs) (hO.preimage continuous_subtype_val)
      ht⟩
  obtain ⟨v, hv, -, -, hmer⟩ := hprin eqn c han hlft hint
  exact ⟨v, hv, hmer⟩

end Step

end Langlands.Analysis.Meromorphic

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Global.InfiniteAdelicGroupPoints

/-- The quotient of an algebra by its unit ideal is a finite module. -/
theorem finite_quotient_top_restrictScalars (R S : Type*) [CommRing R] [Ring S] [Algebra R S] :
    Module.Finite R (S ⧸ (⊤ : Ideal S).restrictScalars R) := by
  refine ⟨⟨∅, eq_top_iff.mpr fun x _ => ?_⟩⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [(Submodule.Quotient.mk_eq_zero _).mpr (by simp)]
  exact zero_mem _

/-- The zero function is an automorphic function on `Γ \ G(𝔸)` for every `Γ` and `Kinf`. -/
theorem zero_isAutomorphicFunctionOn (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    rfl
  · refine ⟨continuous_const, fun b => ?_, ⊤, by simp, fun _ _ _ => rfl⟩
    exact zero_mem (InfinitePlotSmoothFunctions F G)
  · have hspan : Submodule.span ℂ (Set.range fun k : Kinf =>
        fun g : AdelicGroupPoints F G => (0 : AdelicGroupPoints F G → ℂ)
          (g * AdelicGroupPoints.ofInfinite F G k)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨k, rfl⟩
      rfl
    unfold IsInfiniteSubgroupFiniteFunction
    rw [hspan]
    infer_instance
  · refine ⟨⊤, finite_quotient_top_restrictScalars ℂ _, fun z _ b h => ?_⟩
    have h0 : (⟨functionInfiniteSlice F G 0 b, h⟩ : InfinitePlotSmoothFunctions F G) = 0 :=
      Subtype.ext (funext fun x => by simp [functionInfiniteSlice])
    rw [h0]
    exact map_zero _
  · exact ⟨1, one_pos, 0, fun g => by simp⟩

section Concrete

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [NumberField F] in
/-- In linear coordinates, the set of `R₀`-regular parameters is open: it is cut out by
finitely many strict inequalities between real-linear functions. -/
theorem isOpen_setOf_isRegularParameter (hG : IsConnectedReductive G) (R₀ : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    IsOpen {t : Fin n → ℂ | r.IsRegularParameter hA hT R₀ (e t)} := by
  have : Smooth G.X.hom := hG.smooth
  have hfin : r.unipotentRoots.Finite :=
    ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image fun χ => r.data.f ≫ χ).subset
      fun α hα => by
        obtain ⟨-, χ, hχ, h⟩ := hα
        exact ⟨χ, hχ, h⟩
  have hset : {t : Fin n → ℂ | r.IsRegularParameter hA hT R₀ (e t)} =
      ⋂ α ∈ r.unipotentRoots, {t : Fin n → ℂ | R₀ <
        Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
          (realParameterRestriction (a ≫ l) (parameterRealPart F P (e t)))
          ((1 : ℝ) ⊗ₜ[ℤ] α)} := by
    ext t
    simp only [mem_iInter]
    rfl
  rw [hset]
  refine hfin.isOpen_biInter fun α _ => isOpen_lt continuous_const ?_
  let Lm : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    ((Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i).flip
      ((1 : ℝ) ⊗ₜ[ℤ] α)) ∘ₗ realParameterRestriction (a ≫ l) ∘ₗ parameterRealPart F P ∘ₗ
        (e.toLinearMap.restrictScalars ℝ)
  exact Lm.continuous_of_finiteDimensional

end Concrete

/-- **Reduction.** The holomorphic part of the principle of meromorphic continuation and the
analytic system characterizing Eisenstein series imply the meromorphic continuation of
Eisenstein series. -/
theorem eisensteinMeromorphicContinuation_of_analyticSystem
    (hprin : MeromorphicContinuationHolomorphicStatement.{0, 0, u, u, 0})
    (hS : EisensteinAnalyticSystemStatement.{u}) :
    EisensteinMeromorphicContinuationStatement.{u} := by
  intro F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hN hrho hsmooth hcalc
    φ hKmax hφ
  obtain ⟨R₀, hsys⟩ :=
    hS F G P M U A p iU l a r hA hT hG hU K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  -- Case 1: no linear coordinate system; the second clause is vacuous.
  by_cases hcoord : ∃ n : ℕ, Nonempty ((Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
  swap
  · exact ⟨hK.eisensteinSeries φ, ⟨R₀, fun _ _ => rfl⟩,
      fun n e _ => absurd ⟨n, ⟨e⟩⟩ hcoord⟩
  obtain ⟨n₀, ⟨e₀⟩⟩ := hcoord
  -- Case 2: no `R₀`-regular parameter; the zero function works.
  by_cases hreg : ∃ t₀ : Fin n₀ → ℂ, r.IsRegularParameter hA hT R₀ (e₀ t₀)
  swap
  · simp only [not_exists] at hreg
    refine ⟨0, ⟨R₀, fun lam hlam => absurd (by rwa [LinearEquiv.apply_symm_apply] :
      r.IsRegularParameter hA hT R₀ (e₀ (e₀.symm lam))) (hreg _)⟩, ?_⟩
    intro n e s₀
    let B : TopologicalSpace.Opens (Fin n → ℂ) := ⟨ball s₀ 1, isOpen_ball⟩
    have : ConnectedSpace B :=
      connectedSpace_of_convex (B := B) (convex_ball s₀ 1) ⟨s₀, mem_ball_self one_pos⟩
    refine ⟨B, mem_ball_self one_pos, 0, ⊤, by simp, 0, univ, isMeromorphicOn_zero,
      fun s _ => ⟨?_, zero_isAutomorphicFunctionOn F G hsmooth hcalc _ _ rho⟩⟩
    funext x
    rw [← UniformGrowthFrechetSpace.evalCLM_apply, Pi.zero_apply, map_zero]
    rfl
  -- Case 3: glue the continuations obtained on balls containing a fixed regular anchor.
  obtain ⟨t₀, ht₀⟩ := hreg
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_setOf_isRegularParameter r hA hT hG R₀ e₀) t₀ ht₀
  let Areg : Set (ComplexCharacterParameter F P) := {lam | r.IsRegularParameter hA hT R₀ lam}
  let Anch : Set (ComplexCharacterParameter F P) := e₀.symm ⁻¹' ball t₀ ε
  have hAReg : Anch ⊆ Areg := by
    intro lam hlam
    have h : r.IsRegularParameter hA hT R₀ (e₀ (e₀.symm lam)) := hball hlam
    rwa [LinearEquiv.apply_symm_apply] at h
  have hAne : Anch.Nonempty := ⟨e₀ t₀, by simp [Anch, hε]⟩
  have hAo : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
      IsOpen (e ⁻¹' Anch) := fun n e =>
    isOpen_ball.preimage (LinearMap.continuous_of_finiteDimensional (e.trans e₀.symm).toLinearMap)
  have hAb : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
      Bornology.IsBounded (e ⁻¹' Anch) := by
    intro n e
    let T := (e₀.trans e.symm).toLinearMap
    have hT' : Continuous T := LinearMap.continuous_of_finiteDimensional T
    refine ((isCompact_closedBall t₀ ε).image hT').isBounded.subset fun t ht => ?_
    refine ⟨e₀.symm (e t), ball_subset_closedBall ht, ?_⟩
    simp [T]
  let Sp : ℝ × Subgroup (FiniteAdelicGroupPoints F G) → Type u := fun j =>
    UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho j.1 j.2
  let toFun : ∀ j, Sp j → AdelicGroupPoints F G → ℂ := fun j =>
    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho j.1 j.2
  let ev : ∀ j, AdelicGroupPoints F G → Sp j →L[ℂ] ℂ := fun j x =>
    UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho j.1 j.2 x
  have hev : ∀ j x v, ev j x v = toFun j v x := fun j x v =>
    UniformGrowthFrechetSpace.evalCLM_apply F G rho hsmooth hcalc hN hrho j.1 j.2 x v
  let Eis : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ := fun lam =>
    hK.eisensteinSeries φ lam
  refine ⟨gluedContinuation Sp toFun Eis Areg Anch,
    ⟨R₀, fun lam hlam => gluedContinuation_of_mem lam hlam⟩, ?_⟩
  intro n e s₀
  obtain ⟨ρ, hρ⟩ := ((hAb n e).insert s₀).subset_ball 0
  let B : TopologicalSpace.Opens (Fin n → ℂ) := ⟨ball 0 ρ, isOpen_ball⟩
  have hBc : Convex ℝ (B : Set (Fin n → ℂ)) := convex_ball 0 ρ
  have hAB : e ⁻¹' Anch ⊆ B := fun t ht => hρ (mem_insert_of_mem _ ht)
  obtain ⟨R, L, hL, Idx, eqn, c, han, hlft, hunq, haut⟩ := hsys n e B isBounded_ball
  have hAne' : (e ⁻¹' Anch).Nonempty := ⟨e.symm (e₀ t₀), by simp [Anch, hε]⟩
  obtain ⟨v, hv, hmer⟩ := exists_meromorphic_unique_solution hprin B hBc eqn c han hlft
    (hAo n e) hAB hAne' fun s hs => by
      obtain ⟨w, -, hw⟩ := hunq s (hAReg hs)
      exact ⟨w, hw⟩
  have hagree : ∀ s ∈ uniqueSolutionLocus eqn c, e (s : Fin n → ℂ) ∈ Areg →
      toFun (R, L) (v s) = Eis (e s) := by
    intro s hs hsreg
    obtain ⟨w, hw, hsol⟩ := hunq s hsreg
    have hvw : v s = w := Set.singleton_eq_singleton_iff.mp ((hv s hs).symm.trans hsol)
    rw [hvw]
    exact hw
  refine ⟨B, hρ (mem_insert _ _), R, L, hL, v, uniqueSolutionLocus eqn c, hmer, fun s hs => ?_⟩
  have hval : gluedContinuation Sp toFun Eis Areg Anch (e s) = toFun (R, L) (v s) :=
    gluedContinuation_eq ev hev hAReg hAne hAo
      ⟨n, e, B, (R, L), uniqueSolutionLocus eqn c, v, hBc, hAB, hmer, hagree, s, hs, rfl, rfl⟩
  refine ⟨hval.symm, ?_⟩
  rw [hval]
  exact haut s (v s) (by rw [hv s hs]; exact mem_singleton _)

end Langlands.Global
