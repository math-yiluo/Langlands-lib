import Langlands.LinearAlgebra.CyclicMatrixCentralizerDensity
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Cyclic operators in matrix centralizers -/

noncomputable section

open Polynomial Matrix
open scoped Function DirectSum

set_option autoImplicit false

namespace Langlands

variable {k : Type*} [Field k]

private theorem finite_evalFiber_of_natDegree_pos (p : k[X]) (hp : 0 < p.natDegree) (c : k) :
    {t : k | p.eval t = c}.Finite := by
  have h : p - Polynomial.C c ≠ 0 := by
    intro hz
    have hpc : p = Polynomial.C c := sub_eq_zero.mp hz
    rw [hpc, Polynomial.natDegree_C] at hp
    exact (lt_irrefl 0) hp
  refine (Polynomial.finite_setOfPred_isRoot h).subset fun t ht => ?_
  change (p - Polynomial.C c).eval t = 0
  rw [Polynomial.eval_sub, Polynomial.eval_C, ht, sub_self]

private theorem exists_injective_polynomialEval {ι : Type*} [Fintype ι]
    [Infinite k] (p : ι → k[X]) (hp : ∀ i, 0 < (p i).natDegree) :
    ∃ a : ι → k, Function.Injective (fun i => (p i).eval (a i)) := by
  classical
  have hs (s : Finset ι) :
      ∃ a : ι → k, Set.InjOn (fun i => (p i).eval (a i)) (s : Set ι) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨a, ha⟩ := ih
        let bad := ⋃ j ∈ (s : Set ι), {t : k | (p i).eval t = (p j).eval (a j)}
        have hbad : bad.Finite :=
          s.finite_toSet.biUnion (fun j _ => finite_evalFiber_of_natDegree_pos (p i) (hp i) _)
        obtain ⟨t, ht⟩ := hbad.exists_notMem
        let b := Function.update a i t
        have hb {j : ι} (hj : j ∈ s) : b j = a j := by
          have hne : j ≠ i := fun h => hi (by simpa only [h] using hj)
          exact Function.update_of_ne hne t a
        refine ⟨b, ?_⟩
        rw [Finset.coe_insert, Set.injOn_insert (by simpa using hi)]
        refine ⟨?_, ?_⟩
        · intro j hj l hl h
          change (p j).eval (b j) = (p l).eval (b l) at h
          exact ha hj hl (by rwa [hb hj, hb hl] at h)
        · rintro ⟨j, hj, hjt⟩
          apply ht
          refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
          change (p j).eval (b j) = (p i).eval (b i) at hjt
          have hbi : b i = t := Function.update_self i t a
          rw [hb hj, hbi] at hjt
          exact hjt.symm
  obtain ⟨a, ha⟩ := hs Finset.univ
  exact ⟨a, fun _ _ h => ha (Finset.mem_univ _) (Finset.mem_univ _) h⟩

private theorem isCoprime_taylor_of_eval_ne {p q : k[X]} (hp : Irreducible p)
    (hq : Irreducible q) (hm : p.Monic) (hn : q.Monic) {a b : k} (he : p.eval a ≠ q.eval b) :
    IsCoprime (Polynomial.taylor a p) (Polynomial.taylor b q) := by
  have hpt : Irreducible (Polynomial.taylor a p) :=
    (MulEquiv.irreducible_iff (Polynomial.taylorEquiv a)).mpr hp
  have hqt : Irreducible (Polynomial.taylor b q) :=
    (MulEquiv.irreducible_iff (Polynomial.taylorEquiv b)).mpr hq
  apply hpt.coprime_iff_not_dvd.mpr
  intro hd
  have heq := Polynomial.eq_of_monic_of_associated (hm.comp_X_add_C a) (hn.comp_X_add_C b)
    (hpt.associated_of_dvd hqt hd)
  have hc : (Polynomial.taylor a p).coeff 0 = (Polynomial.taylor b q).coeff 0 :=
    congrArg (fun f : k[X] => f.coeff 0) heq
  rw [Polynomial.taylor_coeff_zero, Polynomial.taylor_coeff_zero] at hc
  exact he hc

private theorem exists_pairwise_isCoprime_taylor {ι : Type*} [Fintype ι]
    [Infinite k] (p : ι → k[X]) (hp : ∀ i, Irreducible (p i)) :
    ∃ a : ι → k, Pairwise (fun i j =>
      IsCoprime (Polynomial.taylor (a i) (p i)) (Polynomial.taylor (a j) (p j))) := by
  classical
  have hmonic (i : ι) : ∃ q : k[X], q.Monic ∧ Associated (p i) q :=
    ⟨normalize (p i), Polynomial.monic_normalize (hp i).ne_zero, associated_normalize (p i)⟩
  choose q hm hassoc using hmonic
  have hq (i : ι) : Irreducible (q i) := (hassoc i).irreducible (hp i)
  obtain ⟨a, ha⟩ := exists_injective_polynomialEval q (fun i => (hq i).natDegree_pos)
  refine ⟨a, fun i j hij => ?_⟩
  have hn : (q i).eval (a i) ≠ (q j).eval (a j) := fun h => hij (ha h)
  have hcop : IsCoprime (Polynomial.taylor (a i) (q i)) (Polynomial.taylor (a j) (q j)) :=
    isCoprime_taylor_of_eval_ne (hq i) (hq j) (hm i) (hm j) hn
  have hd (l : ι) : Polynomial.taylor (a l) (p l) ∣ Polynomial.taylor (a l) (q l) := by
    obtain ⟨w, hw⟩ := (hassoc l).dvd
    refine ⟨Polynomial.taylor (a l) w, ?_⟩
    change Polynomial.taylorAlgHom (a l) (q l) =
      Polynomial.taylorAlgHom (a l) (p l) * Polynomial.taylorAlgHom (a l) w
    rw [hw, map_mul]
  exact (hcop.of_isCoprime_of_dvd_left (hd i)).of_isCoprime_of_dvd_right (hd j)

section ShiftedProduct

variable {ι : Type*} [Fintype ι] (p : ι → k[X]) (e : ι → ℕ) (a : ι → k)

local notation "J" i => Ideal.span ({p i ^ e i} : Set k[X])
local notation "Q" i => k[X] ⧸ J i

/-- Evaluate a polynomial after a translation of the variable in one cyclic quotient. -/
def shiftedCyclicResidue (i : ι) : k[X] →ₐ[k] Q i :=
  (Ideal.Quotient.mkₐ k (J i)).comp (Polynomial.taylorAlgHom (-(a i)))

private theorem surjective_shiftedCyclicResidues (h : Pairwise (fun i j =>
    IsCoprime (Polynomial.taylor (a i) (p i)) (Polynomial.taylor (a j) (p j)))) :
    Function.Surjective (AlgHom.pi (shiftedCyclicResidue p e a)) := by
  let L := fun i => Ideal.span ({(Polynomial.taylor (a i) (p i)) ^ e i} : Set k[X])
  have hL : Pairwise (IsCoprime on L) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (h hij).pow
  let t (i : ι) := shiftedCyclicResidue p e a i
  have hker (i : ι) : L i ≤ RingHom.ker (t i).toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change Ideal.Quotient.mk (J i)
      (Polynomial.taylorAlgHom (-(a i)) ((Polynomial.taylor (a i) (p i)) ^ e i)) = 0
    rw [map_pow]
    have he : Polynomial.taylorAlgHom (-(a i)) (Polynomial.taylor (a i) (p i)) = p i := by
      change Polynomial.taylor (-(a i)) (Polynomial.taylor (a i) (p i)) = p i
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let emb (i : ι) : (k[X] ⧸ L i) →+* Q i :=
    Ideal.Quotient.lift (L i) (t i).toRingHom (fun _ hx => hker i hx)
  intro y
  choose r hr using fun i => Ideal.Quotient.mk_surjective (y i)
  obtain ⟨w, hw⟩ := Ideal.pi_quotient_surjective hL
    (fun i => Ideal.Quotient.mk (L i) (Polynomial.taylor (a i) (r i)))
  refine ⟨w, funext fun i => ?_⟩
  have he := congrArg (emb i) (hw i)
  change t i w = t i (Polynomial.taylor (a i) (r i)) at he
  change t i w = y i
  rw [he]
  change Ideal.Quotient.mk (J i) (Polynomial.taylor (-(a i)) (Polynomial.taylor (a i) (r i))) = y i
  rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero, hr]

/-- The blockwise linear operator obtained by multiplying by the shifted variable
in each cyclic quotient. -/
def shiftedCyclicOperator : Module.End k (∀ i, Q i) :=
  Algebra.lmul k _ ((AlgHom.pi (shiftedCyclicResidue p e a)) Polynomial.X)

omit [Fintype ι] in
private theorem shiftedCyclicOperator_aeval_one (f : k[X]) :
    aeval (shiftedCyclicOperator p e a) f 1 = (AlgHom.pi (shiftedCyclicResidue p e a)) f := by
  have he : aeval (shiftedCyclicOperator p e a) =
      (Algebra.lmul k _).comp (AlgHom.pi (shiftedCyclicResidue p e a)) :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X]; rfl)
  rw [he]
  change (AlgHom.pi (shiftedCyclicResidue p e a)) f * 1 =
    (AlgHom.pi (shiftedCyclicResidue p e a)) f
  exact mul_one _

end ShiftedProduct

private theorem exists_commuting_cyclic_end [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (f : Module.End k V) :
    ∃ B : Module.End k V, Commute f B ∧
      ∃ v : V, Function.Surjective (fun p : k[X] => aeval B p v) := by
  classical
  have hT : Module.IsTorsion k[X] (Module.AEval' f) := by
    intro u
    refine ⟨⟨f.charpoly, mem_nonZeroDivisors_of_ne_zero f.charpoly_monic.ne_zero⟩, ?_⟩
    change (aeval f f.charpoly) ((Module.AEval'.of f).symm u) = 0
    rw [f.aeval_self_charpoly]
    rfl
  obtain ⟨ι, inst, p, hp, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion hT
  let Q := fun i : ι => k[X] ⧸ Ideal.span ({p i ^ e i} : Set k[X])
  let P := ∀ i, Q i
  let Fp : Module.AEval' f ≃ₗ[k[X]] P :=
    E.trans (DFinsupp.linearEquivFunOnFintype (R := k[X]))
  let F : V ≃ₗ[k] P := (Module.AEval'.of f).trans (Fp.restrictScalars k)
  let G := F.conjAlgEquiv k
  let x : P := fun i => Ideal.Quotient.mk _ X
  have hf : G f = Algebra.lmul k P x := by
    apply LinearMap.ext
    intro y
    funext i
    change Fp (Module.AEval'.of f (f (F.symm y))) i = (x * y) i
    rw [← Module.AEval'.X_smul_of, Fp.map_smul]
    change (X • F (F.symm y)) i = (x * y) i
    rw [F.apply_symm_apply]
    rfl
  obtain ⟨a, ha⟩ := exists_pairwise_isCoprime_taylor p hp
  let D : Module.End k P := shiftedCyclicOperator p e a
  let B := G.symm D
  have hB : G B = D := G.apply_symm_apply D
  refine ⟨B, ?_, F.symm 1, ?_⟩
  · change f * B = B * f
    apply G.injective
    rw [map_mul, map_mul, hf, hB]
    exact (Commute.all x _).map (Algebra.lmul k P)
  · intro w
    obtain ⟨q, hq⟩ := surjective_shiftedCyclicResidues p e a ha (F w)
    refine ⟨q, F.injective ?_⟩
    have he : G (aeval B q) = aeval D q := by rw [← Polynomial.aeval_algHom_apply, hB]
    have h := LinearMap.congr_fun he (1 : P)
    change F (aeval B q (F.symm 1)) = aeval D q 1 at h
    rw [h, shiftedCyclicOperator_aeval_one]
    exact hq

private theorem hasCyclicMatrixVector_of_surjective_aeval_mulVec {n : ℕ}
    (T : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hv : Function.Surjective (fun p : k[X] => aeval T p *ᵥ v)) : HasCyclicMatrixVector T := by
  refine ⟨v, isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp
    (mulVec_surjective_iff_isUnit.mp ?_))⟩
  intro w
  obtain ⟨p, hp⟩ := hv w
  let r := p %ₘ T.charpoly
  have hd : r.degree < n := by
    simpa only [T.charpoly_degree_eq_dim, Fintype.card_fin] using
      degree_modByMonic_lt p T.charpoly_monic
  have hr : (∑ j : Fin n, monomial (j : ℕ) (r.coeff j)) = r := by
    rw [Polynomial.sum_fin (fun j c => monomial j c) (fun j => monomial_zero_right j) hd,
      Polynomial.sum_monomial_eq]
  refine ⟨fun j => r.coeff j, ?_⟩
  have he := T.aeval_eq_aeval_mod_charpoly p
  change aeval T p = aeval T r at he
  change aeval T p *ᵥ v = w at hp
  rw [he, ← hr] at hp
  rw [← hp]
  simp only [map_sum, aeval_monomial, ← Algebra.smul_def, sum_mulVec, smul_mulVec]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, cyclicVectorMatrix, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Over an infinite field every square matrix commutes with a matrix having a cyclic vector. -/
theorem exists_cyclicMatrixVector_commute [Infinite k] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) k) :
    ∃ B, Commute C B ∧ HasCyclicMatrixVector B := by
  let L : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k) := Matrix.toLinAlgEquiv'
  obtain ⟨D, hD, v, hv⟩ := exists_commuting_cyclic_end (L C)
  refine ⟨L.symm D, ?_, hasCyclicMatrixVector_of_surjective_aeval_mulVec _ v ?_⟩
  · simpa only [L.symm_apply_apply] using hD.map L.symm
  · intro w
    obtain ⟨p, hp⟩ := hv w
    refine ⟨p, ?_⟩
    change (aeval D p) v = w at hp
    change L (aeval (L.symm D) p) v = w
    rw [← Polynomial.aeval_algHom_apply, L.apply_symm_apply, hp]

section RealCentralizer

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- In a real matrix centralizer, a commuting matrix and its adjusted transpose are
a limit of pairs of matrices conjugate by units in that centralizer. -/
theorem mem_closure_centralizerConjugacy_of_adjustedTranspose
    {C A : Mat} {q : Matˣ} (hq : q.val * C * q.inv = Cᵀ) (hA : Commute C A) :
    (A, q.inv * Aᵀ * q.val) ∈ closure {p : Mat × Mat | Commute C p.1 ∧
      ∃ b : Matˣ, Commute (b : Mat) C ∧ b.val * p.1 * b.inv = p.2} := by
  obtain ⟨B, hB, hcyc⟩ := exists_cyclicMatrixVector_commute C
  let D := B - (A + C)
  have hD : Commute C D := hB.sub_right (hA.add_right (Commute.refl C))
  have hshift : A + C + D = B := add_sub_cancel _ _
  have hline (t : ℝ) : A + t • D ∈ {X | Commute C X} :=
    hA.add_right (hD.smul_right t)
  exact mem_closure_centralizerConjugacy_adjustedTranspose hq hA hD
    (hshift.symm ▸ hcyc) hline

end RealCentralizer

end Langlands
