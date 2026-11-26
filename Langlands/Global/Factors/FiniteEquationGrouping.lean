import Langlands.Global.Factors.RelativeWeilEngine

/-! # Products and grouping of finite Euler data in a functional equation -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.Global.FunctionalEquationComparison

open Filter Topology RelativeWeilEngine

/-- Componentwise product of local factors over a finite family. -/
def localFactorsProduct {I : Type w} (A : Finset I) (f : I → LocalFactors) : LocalFactors where
  lFactor s := ∏ i ∈ A, (f i).lFactor s
  dualLFactor s := ∏ i ∈ A, (f i).dualLFactor s
  epsilonFactor s := ∏ i ∈ A, (f i).epsilonFactor s

/-- The gamma factor of a finite product is the product of its gamma factors. -/
theorem localFactorsProduct_gamma {I : Type w} (A : Finset I) (f : I → LocalFactors) (s : ℂ) :
    (localFactorsProduct A f).gamma s = ∏ i ∈ A, (f i).gamma s := by
  simp only [LocalFactors.gamma, localFactorsProduct, Finset.prod_div_distrib,
    Finset.prod_mul_distrib]

/-- The finite product of Euler data on one set of places. -/
def FiniteEulerData.product {I : Type w} {P : Type u} (A : Finset I)
    (D : I → FiniteEulerData P) : FiniteEulerData P where
  localFactors p := localFactorsProduct A fun i => (D i).localFactors p
  partialL s := ∏ i ∈ A, (D i).partialL s
  partialDualL s := ∏ i ∈ A, (D i).partialDualL s

/-- Group the local factors along a map with finite fibres. -/
def FiniteEulerData.group {P : Type u} {Q : Type v} (D : FiniteEulerData P)
    (fibres : Q → Finset P) : FiniteEulerData Q where
  localFactors q := localFactorsProduct (fibres q) D.localFactors
  partialL := D.partialL
  partialDualL := D.partialDualL

private theorem localFactorsProduct_nonzero {I : Type w} (A : Finset I) (f : I → LocalFactors)
    (h : ∀ i ∈ A, NonzeroMeromorphic (f i).lFactor ∧ NonzeroMeromorphic (f i).dualLFactor ∧
      NonzeroMeromorphic (f i).epsilonFactor) :
    NonzeroMeromorphic (localFactorsProduct A f).lFactor ∧
    NonzeroMeromorphic (localFactorsProduct A f).dualLFactor ∧
    NonzeroMeromorphic (localFactorsProduct A f).epsilonFactor :=
  ⟨NonzeroMeromorphic.finsetProd _ fun i hi => (h i hi).1,
    NonzeroMeromorphic.finsetProd _ fun i hi => (h i hi).2.1,
    NonzeroMeromorphic.finsetProd _ fun i hi => (h i hi).2.2⟩

private theorem completedL_product {I : Type w} {P : Type u} (A : Finset I)
    (D : I → FiniteEulerData P) (S : Finset P) (s : ℂ) :
    (FiniteEulerData.product A D).completedL S s = ∏ i ∈ A, (D i).completedL S s := by
  simp only [FiniteEulerData.completedL, FiniteEulerData.product, localFactorsProduct,
    Finset.prod_mul_distrib]
  rw [Finset.prod_comm (s := S) (t := A)]

private theorem completedDualL_product {I : Type w} {P : Type u} (A : Finset I)
    (D : I → FiniteEulerData P) (S : Finset P) (s : ℂ) :
    (FiniteEulerData.product A D).completedDualL S s = ∏ i ∈ A, (D i).completedDualL S s := by
  simp only [FiniteEulerData.completedDualL, FiniteEulerData.product, localFactorsProduct,
    Finset.prod_mul_distrib]
  rw [Finset.prod_comm (s := S) (t := A)]

private theorem finiteEpsilon_product {I : Type w} {P : Type u} (A : Finset I)
    (D : I → FiniteEulerData P) (S : Finset P) (s : ℂ) :
    (FiniteEulerData.product A D).finiteEpsilon S s = ∏ i ∈ A, (D i).finiteEpsilon S s := by
  simp only [FiniteEulerData.finiteEpsilon, FiniteEulerData.product, localFactorsProduct]
  rw [Finset.prod_comm (s := S) (t := A)]

/-- Finite products of functional equations on a common exceptional set. -/
theorem finiteEulerData_product_holds {I : Type w} {P : Type u} [DecidableEq P]
    (A : Finset I) (D : I → FiniteEulerData P) (S : Finset P) (σ : ℝ)
    (h : ∀ i ∈ A, Admissible (D i) S ∧ HasEulerProductsOutside (D i) S σ ∧
      FunctionalEquation (D i) S) :
    Admissible (FiniteEulerData.product A D) S ∧
    HasEulerProductsOutside (FiniteEulerData.product A D) S σ ∧
      FunctionalEquation (FiniteEulerData.product A D) S := by
  refine ⟨⟨NonzeroMeromorphic.finsetProd _ fun i hi => (h i hi).1.1,
    NonzeroMeromorphic.finsetProd _ fun i hi => (h i hi).1.2.1,
    fun p hp => localFactorsProduct_nonzero _ _ fun i hi => (h i hi).1.2.2 p hp⟩, ?_, ?_⟩
  · intro s hs
    exact ⟨hasProd_prod fun i hi => ((h i hi).2.1 s hs).1,
      hasProd_prod fun i hi => ((h i hi).2.1 s hs).2⟩
  · intro z
    have he := (Filter.eventually_all_finset A).mpr fun i hi => (h i hi).2.2 z
    filter_upwards [he] with s hs
    rw [completedL_product, completedDualL_product, finiteEpsilon_product,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hs

private theorem hasProd_outside_group {P : Type u} {Q : Type v} [DecidableEq P]
    [DecidableEq Q] (π : P → Q) (fibres : Q → Finset P)
    (hfibre : ∀ p q, p ∈ fibres q ↔ π p = q) (T : Finset P) (S : Finset Q)
    (hTS : ∀ p, p ∈ T ↔ π p ∈ S) {f : P → ℂ} {a : ℂ}
    (h : HasProd (fun p : {p // p ∉ T} => f p.1) a) :
    HasProd (fun q : {q // q ∉ S} => ∏ p ∈ fibres q.1, f p) a := by
  let π' (p : {p // p ∉ T}) : {q // q ∉ S} := ⟨π p.1, fun h => p.2 ((hTS p.1).mpr h)⟩
  let fibres' (q : {q // q ∉ S}) : Finset {p // p ∉ T} := (fibres q.1).subtype (fun p => p ∉ T)
  have hF (p : {p // p ∉ T}) (q : {q // q ∉ S}) : p ∈ fibres' q ↔ π' p = q := by
    rw [show p ∈ fibres' q ↔ p.1 ∈ fibres q.1 from Finset.mem_subtype, hfibre]
    change (π' p).1 = q.1 ↔ π' p = q
    exact Subtype.ext_iff.symm
  refine (hasProd_fiberwise π' fibres' hF h).congr_fun fun q => ?_
  symm
  exact Finset.prod_subtype_of_mem (s := fibres q.1) (p := fun p => p ∉ T) f fun p hp => by
    rw [hTS, (hfibre p q.1).mp hp]
    exact q.2

/-- Grouping the factors in a functional equation along a map with finite
fibres preserves the equation when the exceptional set is the full preimage. -/
def FiniteEquationGroupingStatement : Prop :=
  ∀ (P : Type u) (Q : Type v) [DecidableEq P] [DecidableEq Q]
    (π : P → Q) (fibres : Q → Finset P),
    (∀ p q, p ∈ fibres q ↔ π p = q) →
    ∀ (T : Finset P) (S : Finset Q), (∀ p, p ∈ T ↔ π p ∈ S) →
    ∀ (D : FiniteEulerData P) (σ : ℝ),
      Admissible D T → HasEulerProductsOutside D T σ → FunctionalEquation D T →
      Admissible (D.group fibres) S ∧ HasEulerProductsOutside (D.group fibres) S σ ∧
        FunctionalEquation (D.group fibres) S

theorem finiteEquationGrouping : FiniteEquationGroupingStatement.{u, v} := by
  intro P Q _ _ π fibres hfibre T S hTS D σ hA hP hEq
  have hf (q : Q) (hq : q ∈ S) (p : P) (hp : p ∈ fibres q) : p ∈ T :=
    (hTS p).mpr ((hfibre p q).mp hp ▸ hq)
  have hT : S.biUnion fibres = T := by
    ext p
    rw [Finset.mem_biUnion, hTS]
    exact ⟨fun ⟨q, hq, hp⟩ => (hfibre p q).mp hp ▸ hq,
      fun hp => ⟨π p, hp, (hfibre p _).mpr rfl⟩⟩
  have hdisj : (S : Set Q).PairwiseDisjoint fibres := by
    intro q _ q' _ hne
    refine Finset.disjoint_left.mpr fun p hp hp' => hne ?_
    exact ((hfibre p q).mp hp).symm.trans ((hfibre p q').mp hp')
  refine ⟨⟨hA.1, hA.2.1, fun q hq => localFactorsProduct_nonzero _ _
    fun p hp => hA.2.2 p (hf q hq p hp)⟩, ?_, ?_⟩
  · intro s hs
    exact ⟨hasProd_outside_group π fibres hfibre T S hTS (hP s hs).1,
      hasProd_outside_group π fibres hfibre T S hTS (hP s hs).2⟩
  · intro z
    filter_upwards [hEq z] with s hs
    simpa only [FiniteEulerData.completedL, FiniteEulerData.completedDualL,
      FiniteEulerData.finiteEpsilon, FiniteEulerData.group, localFactorsProduct,
      ← Finset.prod_biUnion hdisj, hT] using hs

end Langlands.Global.FunctionalEquationComparison
