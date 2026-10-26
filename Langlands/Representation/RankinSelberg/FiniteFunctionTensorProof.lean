import Langlands.Representation.RankinSelberg.FiniteFunctionTensorStatement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Topology.Constructions
import Mathlib.Algebra.BigOperators.Fin

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uG uM uX

private abbrev TensorFinite {M : Type uM} [Monoid M] [TopologicalSpace M]
    (h : M → ℂ) : Prop :=
  Continuous h ∧ FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range fun b : M => fun a : M => h (b * a)))

private def tensorFiniteSubmodule (M : Type uM) [Monoid M] [TopologicalSpace M] :
    Submodule ℂ (M → ℂ) where
  carrier := {h | TensorFinite h}
  zero_mem' := by
    refine ⟨continuous_const, ?_⟩
    apply (Submodule.fg_iff_finiteDimensional _).mp
    apply (Submodule.fg_bot (R := ℂ) (M := M → ℂ)).of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    apply (Submodule.fg_iff_finiteDimensional _).mp
    apply (((Submodule.fg_iff_finiteDimensional _).mpr hf.2).sup
      ((Submodule.fg_iff_finiteDimensional _).mpr hg.2)).of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨b, rfl⟩)
  smul_mem' := by
    intro c f hf
    refine ⟨continuous_const.smul hf.1, ?_⟩
    apply (Submodule.fg_iff_finiteDimensional _).mp
    apply ((Submodule.fg_iff_finiteDimensional _).mpr hf.2).of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)

/-- Restriction of translates controls the orbit span of a slice. -/
private theorem tensorFinite_restrict {M : Type uM} {X : Type uX}
    [Monoid M] [Monoid X] [TopologicalSpace M] [TopologicalSpace X]
    {η : M → ℂ} (hη : TensorFinite η) (s q : X → M) (hs : Continuous s)
    (ht : ∀ b : X, ∃ t : M, ∀ a : X, s (b * a) = t * q a) :
    TensorFinite (fun a => η (s a)) := by
  refine ⟨hη.1.comp hs, ?_⟩
  let pull : (M → ℂ) →ₗ[ℂ] (X → ℂ) :=
    { toFun := fun v a => v (q a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply (Submodule.fg_iff_finiteDimensional _).mp
  apply (((Submodule.fg_iff_finiteDimensional _).mpr hη.2).map pull).of_le
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨b, rfl⟩
  obtain ⟨t, ht⟩ := ht b
  refine Submodule.mem_map.mpr ⟨(fun a => η (t * a)),
    Submodule.subset_span ⟨t, rfl⟩, ?_⟩
  ext a
  exact congrArg η (ht a).symm

private theorem tensorFinite_head {G : Type uG} [Monoid G] [TopologicalSpace G]
    {r : ℕ} {η : (Fin (r + 1) → G) → ℂ} (hη : TensorFinite η) (y : Fin r → G) :
    TensorFinite (fun x => η (Fin.cons x y)) := by
  apply tensorFinite_restrict hη (fun x => Fin.cons x y) (fun x => Fin.cons x 1)
    (Continuous.finCons (A := fun _ : Fin (r + 1) => G) continuous_id continuous_const)
  intro b
  refine ⟨Fin.cons b y, ?_⟩
  intro a
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem tensorFinite_tail {G : Type uG} [Monoid G] [TopologicalSpace G]
    {r : ℕ} {η : (Fin (r + 1) → G) → ℂ} (hη : TensorFinite η) (x : G) :
    TensorFinite (fun y => η (Fin.cons x y)) := by
  apply tensorFinite_restrict hη (fun y => Fin.cons x y) (fun y => Fin.cons 1 y)
    (Continuous.finCons (A := fun _ : Fin (r + 1) => G) continuous_const continuous_id)
  intro b
  refine ⟨Fin.cons x b, ?_⟩
  intro a
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- A head-coordinate split with finite functions on both sides. -/
private theorem tensorFinite_split {G : Type uG} [Monoid G] [TopologicalSpace G]
    {r : ℕ} {η : (Fin (r + 1) → G) → ℂ} (hη : TensorFinite η) :
    ∃ (n : ℕ) (f : Fin n → G → ℂ) (g : Fin n → (Fin r → G) → ℂ),
      (∀ i, TensorFinite (f i)) ∧ (∀ i, TensorFinite (g i)) ∧
      ∀ x y, η (Fin.cons x y) = ∑ i, f i x * g i y := by
  classical
  let S := Submodule.span ℂ (Set.range fun y : Fin r → G => fun x : G => η (Fin.cons x y))
  let pull : ((Fin (r + 1) → G) → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun v x => v (Fin.cons x 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdim : FiniteDimensional ℂ S := by
    apply (Submodule.fg_iff_finiteDimensional _).mp
    apply (((Submodule.fg_iff_finiteDimensional _).mpr hη.2).map pull).of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_map.mpr ⟨(fun a => η (Fin.cons 1 y * a)),
      Submodule.subset_span ⟨Fin.cons 1 y, rfl⟩, ?_⟩
    ext x
    apply congrArg η
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  let := hdim
  have hS : S ≤ tensorFiniteSubmodule G := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    exact tensorFinite_head hη y
  let slice (y : Fin r → G) : S :=
    ⟨fun x => η (Fin.cons x y), Submodule.subset_span ⟨y, rfl⟩⟩
  let ev : G → Module.Dual ℂ S := fun x => (LinearMap.proj x).comp S.subtype
  let coeff : Module.Dual ℂ S →ₗ[ℂ] ((Fin r → G) → ℂ) :=
    { toFun := fun ℓ y => ℓ (slice y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcoeff (ℓ : Module.Dual ℂ S) : TensorFinite (coeff ℓ) := by
    have hmem : ℓ ∈ Submodule.span ℂ (Set.range ev) := by
      apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
      intro v hv
      have hv0 : v = 0 := by
        apply Subtype.ext
        funext x
        exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv x)
      change ℓ v = 0
      rw [hv0, map_zero]
    have hspan : Submodule.span ℂ (Set.range ev) ≤
        (tensorFiniteSubmodule (Fin r → G)).comap coeff := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, rfl⟩
      exact tensorFinite_tail hη x
    exact hspan hmem
  let b := Module.finBasis ℂ S
  refine ⟨Module.finrank ℂ S, (fun i => (b i : G → ℂ)),
    (fun i => coeff (b.coord i)), (fun i => hS (b i).property),
    (fun i => hcoeff (b.coord i)), ?_⟩
  intro x y
  have heq := congrArg (fun v : S => (v : G → ℂ) x) (b.sum_repr (slice y))
  change η (Fin.cons x y) = ∑ i, (b i : G → ℂ) x * (b.repr (slice y)) i
  simpa only [slice, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using heq.symm

/-- Every continuous translation-finite function on a finite power of a monoid
has a finite tensor expansion by continuous translation-finite factors. -/
theorem finiteFunctionTensor : FiniteFunctionTensorStatement.{uG} := by
  classical
  intro G _ _ r
  dsimp only
  induction r with
  | zero =>
      intro η hη
      refine ⟨1, (fun _ => η (fun i => Fin.elim0 i)),
        (fun _ i => Fin.elim0 i), ?_, ?_⟩
      · intro j i
        exact Fin.elim0 i
      · intro a
        have ha : a = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
        simp [ha]
  | succ r ih =>
      intro η hη
      obtain ⟨n, f, g, hf, hg, hsplit⟩ := tensorFinite_split hη
      have hex := fun i => ih (g i) (hg i)
      choose N c F hF hsum using hex
      let I := (i : Fin n) × Fin (N i)
      let e := Fintype.equivFin I
      refine ⟨Fintype.card I, (fun j => c (e.symm j).1 (e.symm j).2),
        (fun j => Fin.cons (f (e.symm j).1) (F (e.symm j).1 (e.symm j).2)), ?_, ?_⟩
      · intro j i
        refine Fin.cases ?_ (fun k => ?_) i
        · exact hf (e.symm j).1
        · exact hF (e.symm j).1 (e.symm j).2 k
      · intro a
        let term : I → ℂ := fun z => c z.1 z.2 *
          ∏ k : Fin (r + 1), (Fin.cons (f z.1) (F z.1 z.2) : Fin (r + 1) → G → ℂ) k (a k)
        change η a = ∑ j, term (e.symm j)
        rw [e.symm.sum_comp, Fintype.sum_sigma]
        calc
          η a = ∑ i, f i (a 0) * g i (Fin.tail a) := by
            simpa only [Fin.cons_self_tail] using hsplit (a 0) (Fin.tail a)
          _ = ∑ i, ∑ j, term ⟨i, j⟩ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsum i (Fin.tail a), Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [term, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_def]
            ring

end Langlands.RankinSelberg
