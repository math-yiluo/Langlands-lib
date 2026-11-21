import Langlands.Automorphic.CyclicOperatorAlgebra
import Langlands.Automorphic.ProjectedBlockSectionKernel
import Langlands.Global.Factors.CuspidalSupportStableKernel
import Langlands.Global.FiniteParametrizedSectionIntertwiner
import Langlands.Global.FiniteParametrizedSectionSupport

/-! # One selected coefficient for the finite and archimedean place comparisons -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 140000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance selectKernelRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance selectKernelContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance selectKernelSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance selectKernelFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance selectKernelStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance selectKernelRealizationGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance selectKernelOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r c : ℕ} {m : Fin c → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
  (Q : IrreducibleOperatorSubquotient F r) {W : Type u} [AddCommGroup W] [Module ℂ W]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ W)
  (q : Representation.IntertwiningMap A.toMonoidHom Q.representation)

private abbrev selectedKernelShape : BlockShape (r + 1) :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

local notation "N" => r + 1
local notation "B" => selectedKernelShape hm
local notation "κ" => A.toMonoidHom.comp (compactOperator F N)
local notation "ρ" => A.toMonoidHom.comp (finiteOperator F N)
local notation "D" => periodRealLieOperator A

private abbrev normalizedBlockFinite (T : ∀ i, CuspidalOperatorRealization F (m i)) :=
  fun i => ((normalizedCuspidalBlocks hm T) i).realization.finiteRepresentation

private theorem range_descent_subquotient {G V Y H : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup H] [Module ℂ H]
    {π : Representation ℂ G V} {σ : Representation ℂ G Y} {τ : Representation ℂ G H}
    (f : Representation.IntertwiningMap π σ) (q : Representation.IntertwiningMap π τ)
    (hker : f.toLinearMap.ker ≤ q.toLinearMap.ker) (hq : Function.Surjective q.toLinearMap) :
    Correspondence.IsSubquotientOf σ τ := by
  refine ⟨f.range, descendIntertwinerToRange f q hker, ?_⟩
  intro y
  obtain ⟨w, hw⟩ := hq y
  exact ⟨f.toLinearMap.rangeRestrict w, (descendIntertwinerToRange_apply f q hker w).trans hw⟩

section OneProjection

variable (T : ∀ i, CuspidalOperatorRealization F (m i))
  (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((T i).Space)))

local notation "ω" => fun i =>
  OperatorRealization.compactRepresentation (CuspidalOperatorRealization.realization (T i))
local notation "σ" => normalizedBlockFinite hm T

private theorem of_selectedProjection
    (hreg : HasRegularCompactOperatorAction A)
    (hK : IsBlockPeriodCompactEvaluation B κ ω ev)
    (hU : ∀ X, IsStrictUpperBlockLie F B X → ∀ w, ev (D X w) = 0)
    (hD : ∀ (i : Fin c) (X : RealLieAlgebra F (m i + 1)) w,
      ev (D (blockShapeRealLieInclusion F B i X) w) =
        tensorCoordinateEnd i ((T i).realization.lieAction X) (ev w))
    (f : Representation.IntertwiningMap ρ (induced F B σ))
    (K : Subrepresentation A.toMonoidHom)
    (hKmem : ∀ w, w ∈ K ↔ ∀ k g, compactFiniteCoefficientEvaluation A ev k g w = 0)
    (hfker : ∀ w, f.toLinearMap w = 0 ↔ w ∈ K)
    (x : Representation.asModule (AlgHom.toMonoidHom' A)) (hx : IsCompatibleCyclicProjectionKernel q K x) :
    HasRestoredCuspidalIdentityRealization Q := by
  let A₀ := cyclicAlgebraAction A x
  let j := cyclicAlgebraInclusion A x
  let ev₀ := ev.comp j.toLinearMap
  let q₀ := q.comp j
  have hq₀ : Function.Surjective q₀.toLinearMap := hx.1
  have hA (b : automorphicOperatorAlgebra F N) (w : (cyclicAlgebraSubrepresentation A x).toSubmodule) :
      j.toLinearMap (A₀ b w) = A b (j.toLinearMap w) :=
    LinearMap.congr_fun (j.isIntertwining' b) w
  let K₀ : Subrepresentation A₀.toMonoidHom :=
    ⟨K.toSubmodule.comap j.toLinearMap, fun a w hw => by
      change j.toLinearMap (A₀ a w) ∈ K
      exact (hA a w).symm ▸ K.apply_mem_toSubmodule a hw⟩
  have hker₀ w (hw : w ∈ K₀) : q₀.toLinearMap w = 0 := hx.2 w hw
  have hK₀mem w : w ∈ K₀ ↔ ∀ k g, compactFiniteCoefficientEvaluation A₀ ev₀ k g w = 0 := by
    change j.toLinearMap w ∈ K ↔ _
    rw [hKmem]
    apply forall_congr'
    intro k
    apply forall_congr'
    intro g
    change ev (A (compactOperator F N k) (A (finiteOperator F N g) (j.toLinearMap w))) = 0 ↔
      ev (j.toLinearMap (A₀ (compactOperator F N k) (A₀ (finiteOperator F N g) w))) = 0
    let a := compactOperator F N k
    let b := finiteOperator F N g
    have he := congrArg (fun z : W => ev z)
      ((hA a (A₀ b w)).trans (congrArg (fun z : W => A a z) (hA b w)))
    exact ⟨fun hz => he.trans hz, fun hz => he.symm.trans hz⟩
  let ρ₀ := A₀.toMonoidHom.comp (finiteOperator F N)
  let jF : Representation.IntertwiningMap ρ₀ ρ :=
    ⟨j.toLinearMap, fun d => j.isIntertwining' (finiteOperator F N d)⟩
  let _ : AddCommGroup (Induction.EquivariantFunctions (parabolic F B) (coefficient F B σ)) :=
    Submodule.addCommGroup _
  let _ : AddCommGroup (Sections F B σ) := Submodule.addCommGroup (Sections F B σ)
  let f₀ : Representation.IntertwiningMap ρ₀ (induced F B σ) := f.comp jF
  let qF : Representation.IntertwiningMap ρ₀ Q.subquotient.finiteRepresentation :=
    ⟨q₀.toLinearMap, fun d => q₀.isIntertwining' (finiteOperator F N d)⟩
  have hf₀ker : f₀.toLinearMap.ker ≤ qF.toLinearMap.ker := by
    intro w hw
    exact hker₀ w ((hfker (j.toLinearMap w)).mp hw)
  have hF : HasSubquotient B σ Q.subquotient.finiteRepresentation := by
    change Correspondence.IsSubquotientOf (V := Sections F B σ) (W := Q.Space)
      (induced F B σ) Q.subquotient.finiteRepresentation
    exact range_descent_subquotient f₀ qF hf₀ker hq₀
  have hreg₀ := HasRegularCompactOperatorAction.of_injective_intertwiner A₀ A j
    Subtype.val_injective hreg
  refine hasRestoredCuspidalIdentityRealization_of_stableKernel hm T Q A₀ q₀ ev₀ hq₀ hreg₀ hF
    ?_ ?_ ?_ K₀ hK₀mem hker₀
  · intro i k w
    let b := compactOperator F N (blockShapeInfiniteCompactEmbedding B F i k)
    change ev (j.toLinearMap (A₀ b w)) = _
    exact (congrArg (fun z : W => ev z) (hA b w)).trans (hK i k (j.toLinearMap w))
  · intro X hX w
    let b := differentialOperator F N (envelopingGenerator F N (complexify F N X))
    change ev (j.toLinearMap (A₀ b w)) = 0
    exact (congrArg (fun z : W => ev z) (hA b w)).trans (hU X hX (j.toLinearMap w))
  · intro i X w
    let b := differentialOperator F N (envelopingGenerator F N
      (complexify F N (blockShapeRealLieInclusion F B i X)))
    change ev (j.toLinearMap (A₀ b w)) = _
    exact (congrArg (fun z : W => ev z) (hA b w)).trans (hD i X (j.toLinearMap w))

end OneProjection

variable {J : Type*} (T : J → ∀ i, CuspidalOperatorRealization F (m i))
  (ev : ∀ j, W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((T j i).Space)))

/-- Apply the standard finite normalization equivalence to the candidate identity coefficient. -/
def normalizedSelectedLeviCoefficient (j : J) :
    W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥(((normalizedCuspidalBlocks hm (T j)) i).Space)) :=
  (normalizedCuspidalCoefficientEquiv hm (T j)).toLinearEquiv.toLinearMap.comp (ev j)

local notation "σ" => fun j => normalizedBlockFinite hm (T j)
local notation "e₁" => normalizedSelectedLeviCoefficient hm T ev

/-- Finite support of the normalized sections selects one compatible kernel.
Keep the same block tuple and section when restricting to the cyclic carrier
and forming its restored coefficient quotient. -/
theorem hasRestoredCuspidalIdentityRealization_of_sectionProjections
    (hq : Function.Surjective q) (hreg : HasRegularCompactOperatorAction A)
    (hρ : IsSmooth ρ) (v : W) (hv : FiniteVectors.orbitSpan A.toMonoidHom v = ⊤)
    (hpoint : ∀ w, {j | ev j w ≠ 0}.Finite)
    (hkill : ∀ w, (∀ j l g, compactFiniteCoefficientEvaluation A (ev j) l g w = 0) → q w = 0)
    (hpar : ∀ j (p : AdelicBlockParabolic.Finite F B) w,
      e₁ j (ρ p.val w) = finiteCoefficient F B (σ j) p (e₁ j w))
    (hK : ∀ j, IsBlockPeriodCompactEvaluation B κ (fun i => (T j i).realization.compactRepresentation) (ev j))
    (hU : ∀ j X, IsStrictUpperBlockLie F B X → ∀ w, ev j (D X w) = 0)
    (hD : ∀ j (i : Fin c) (X : RealLieAlgebra F (m i + 1)) w,
      ev j (D (blockShapeRealLieInclusion F B i X) w) =
        tensorCoordinateEnd i ((T j i).realization.lieAction X) (ev j w)) :
    HasRestoredCuspidalIdentityRealization Q := by
  have commute (d : FiniteAdelicGL F N) (k : standardInfiniteCompact F N) (w : W) :
      ρ d (κ k w) = κ k (ρ d w) :=
    LinearMap.congr_fun ((finiteOperator_compactOperator_commute d k).map A).eq w
  let E j := compactFiniteCoefficientEvaluation A (e₁ j)
  have hEpar j l (p : AdelicBlockParabolic.Finite F B) g w :
      E j l (p.val * g) w = finiteCoefficient F B (σ j) p (E j l g w) := by
    let e := e₁ j
    have hmul : ρ (p.val * g) w = ρ p.val (ρ g w) := LinearMap.congr_fun (map_mul (ρ) p.val g) w
    change e (κ l (ρ (p.val * g) w)) = finiteCoefficient F B (σ j) p (e (κ l (ρ g w)))
    calc
      _ = e (κ l (ρ p.val (ρ g w))) := congrArg (fun z : W => e (κ l z)) hmul
      _ = e (ρ p.val (κ l (ρ g w))) := congrArg (fun z : W => e z) (commute p.val l (ρ g w)).symm
      _ = _ := hpar j p (κ l (ρ g w))
  have hEtrans j l g d w : E j l g (ρ d w) = E j l (g * d) w := by
    have hmul : ρ (g * d) w = ρ g (ρ d w) := LinearMap.congr_fun (map_mul (ρ) g d) w
    exact congrArg (fun z : W => e₁ j (κ l z)) hmul.symm
  have hzero j w : e₁ j w = 0 ↔ ev j w = 0 :=
    (normalizedCuspidalCoefficientEquiv hm (T j)).toLinearEquiv.map_eq_zero_iff
  let f j := linearEvaluationIntertwiner B (σ j) hρ (E j) (hEpar j) (hEtrans j)
  let K j := projectedBlockSectionKernel A B (ev j) hreg.2.2
    (fun X w hX => hU j X hX w)
    (fun i X w hw => (hD j i X w).trans ((congrArg _ hw).trans (map_zero _)))
  have hKmem j w : w ∈ K j ↔ ∀ k g, compactFiniteCoefficientEvaluation A (ev j) k g w = 0 := Iff.rfl
  have hfker j w : (f j).toLinearMap w = 0 ↔ w ∈ K j :=
    (linearEvaluationIntertwiner_eq_zero_iff B (σ j) hρ (E j) (hEpar j) (hEtrans j) w).trans
      ((forall_congr' fun k => forall_congr' fun g => hzero j (κ k (ρ g w))).trans
        (hKmem j w).symm)
  have hEpoint g w : {j | E j 1 g w ≠ 0}.Finite :=
    (hpoint (κ 1 (ρ g w))).subset fun j hj hz => hj ((hzero j _).mpr hz)
  have hEcompact j l g w : E j l g w = E j 1 g (κ l w) := by
    have hone : κ 1 (ρ g (κ l w)) = ρ g (κ l w) :=
      LinearMap.congr_fun (map_one (κ)) (ρ g (κ l w))
    exact congrArg (fun z : W => e₁ j z) ((commute g l w).symm.trans hone.symm)
  have hcovZero j l (p : AdelicBlockParabolic.Finite F B) g w (hw : E j l g w = 0) :
      E j l (p.val * g) w = 0 :=
    (hEpar j l p g w).trans ((congrArg (fun z => finiteCoefficient F B (σ j) p z) hw).trans
      ((finiteCoefficient F B (σ j) p).map_zero))
  have hfin : {j | v ∉ K j}.Finite := by
    apply (finiteSectionEvaluationSupport B κ ρ E hEpoint hEcompact hEtrans hcovZero v
      (hreg.1 v) (hρ v)).subset
    intro j hj
    by_contra hn
    apply hj
    apply (hKmem j v).mpr
    intro k g
    apply (hzero j (κ k (ρ g v))).mp
    by_contra hp
    exact hn ⟨k, g, hp⟩
  obtain ⟨j, x, hx⟩ := exists_compatibleCyclicProjectionKernel q hq K
    (fun w hw => hkill w fun j => (hKmem j w).mp (hw j)) v hv hfin
  exact of_selectedProjection hm Q A q (T j) (ev j) hreg (hK j) (hU j) (hD j) (f j)
    (K j) (hKmem j) (hfker j) x hx

end Langlands.Global
