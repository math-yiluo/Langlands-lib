import Langlands.GroupScheme.Quaternionic.CocharacterWeightScalarExtension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Counting actual cocharacter weights in a homogeneous extended basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

private theorem submodule_eq_span_of_projector_basis
    {k V I : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype I]
    (b : Basis I k V) (W : Submodule k V) (P : Module.End k V)
    (p : I → Prop) [DecidablePred p]
    (hb : ∀ i, p i → b i ∈ W)
    (hP : ∀ v ∈ W, P v = v)
    (hPb : ∀ i, P (b i) = if p i then b i else 0) :
    W = Submodule.span k (Set.range (fun i : {i // p i} => b i.val)) := by
  classical
  apply le_antisymm
  · intro v hv
    have he : P v = ∑ i, b.repr v i • P (b i) := by
      calc
        P v = P (∑ i, b.repr v i • b i) := congrArg P (b.sum_repr v).symm
        _ = _ := by simp only [_root_.map_sum, _root_.map_smul]
    rw [← hP v hv, he]
    apply Submodule.sum_mem
    intro i _
    rw [hPb]
    split_ifs with hi
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · simp
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i.val i.property

private def basisOfProjector
    {k V I : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype I]
    (b : Basis I k V) (W : Submodule k V) (P : Module.End k V)
    (p : I → Prop) [DecidablePred p]
    (hb : ∀ i, p i → b i ∈ W)
    (hP : ∀ v ∈ W, P v = v)
    (hPb : ∀ i, P (b i) = if p i then b i else 0) :
    Basis {i // p i} k W :=
  (Basis.span (b.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _
      (submodule_eq_span_of_projector_basis b W P p hb hP hPb).symm)

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n)
  (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)

/-- The tensor extension of a Laurent coefficient projector isolates the actual
extended weight spaces. -/
theorem cocharacterWeightProjector_baseChange_of_mem
    (L : Type u) [Field L] [Algebra K L] (c d : ℤ)
    {z : L ⊗[K] (n → D)}
    (hz : z ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) d) :
    (σ.cocharacterWeightProjector q f c).baseChange L z =
      if d = c then z else 0 := by
  classical
  let e := σ.cocharacterWeightBaseChangeEquiv q f
    (CommAlgCat.of (CommRingCat.of K) L) d
  obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
  have hx' : (e x : L ⊗[K] (n → D)) = z := congrArg Subtype.val hx
  rw [← hx']
  clear hx hx'
  induction x with
  | tmul r v =>
    rw [σ.cocharacterWeightBaseChangeEquiv_tmul]
    simp only [LinearMap.baseChange_tmul,
      σ.cocharacterWeightProjector_of_mem q f c d v.property]
    split_ifs <;> simp
  | add x y hx hy =>
    simp only [_root_.map_add, Submodule.coe_add, hx, hy]
    split_ifs <;> simp

/-- Restrict a homogeneous basis of the extended row module to one actual
all-test cocharacter weight space. -/
def cocharacterWeightBasisOver
    (L : Type u) [Field L] [Algebra K L]
    {I : Type*} [Fintype I]
    (b : Basis I L (L ⊗[K] (n → D))) (w : I → ℤ)
    (hb : ∀ i, b i ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w i)) (c : ℤ) :
    Basis {i // w i = c} L (σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) c) := by
  classical
  apply basisOfProjector b _ ((σ.cocharacterWeightProjector q f c).baseChange L)
    (fun i => w i = c)
  · intro i hi
    simpa only [← hi] using hb i
  · intro v hv
    simpa only [ite_true] using
      σ.cocharacterWeightProjector_baseChange_of_mem q f L c c hv
  · intro i
    exact σ.cocharacterWeightProjector_baseChange_of_mem q f L c (w i) (hb i)

/-- The dimension of an actual extended weight space counts the basis indices
with that integer weight. -/
theorem finrank_cocharacterWeightSpaceOver_of_basis
    (L : Type u) [Field L] [Algebra K L]
    {I : Type*} [Fintype I]
    (b : Basis I L (L ⊗[K] (n → D))) (w : I → ℤ)
    (hb : ∀ i, b i ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w i)) (c : ℤ) :
    finrank L (σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) c) = Nat.card {i // w i = c} := by
  classical
  rw [Module.finrank_eq_card_basis (σ.cocharacterWeightBasisOver q f L b w hb c)]
  exact Nat.card_eq_fintype_card.symm

/-- A homogeneous extended basis counts the original division-algebra weight
dimension in ground-field units. -/
theorem cocharacterWeightBasis_card
    (L : Type u) [Field L] [Algebra K L]
    {I : Type*} [Fintype I]
    (b : Basis I L (L ⊗[K] (n → D))) (w : I → ℤ)
    (hb : ∀ i, b i ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w i)) (c : ℤ) :
    Nat.card {i // w i = c} =
      finrank K D * finrank D (σ.cocharacterWeightSpace q f c) := by
  rw [← σ.finrank_cocharacterWeightSpaceOver_of_basis q f L b w hb c,
    σ.finrank_cocharacterWeightSpaceOver_eq_mul]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
