import Langlands.Algebra.OrderedPBWBasis
import Langlands.Representation.Archimedean.Kostant.OrderedMonomials
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Polynomial symbols of a finite-dimensional Lie algebra -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean.Kostant MvPolynomial Finsupp

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  {r : ℕ} (b : Module.Basis (Fin r) k L)

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "P" => MvPolynomial (Fin r) k
local notation "indices" => List.ofFn (id : Fin r → Fin r)

private theorem nodup_indices : (indices).Nodup :=
  List.nodup_ofFn.mpr Function.injective_id

private theorem mem_indices (i : Fin r) : i ∈ indices :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

/-- The ordered PBW basis, indexed by the same exponent vectors as multivariate monomials. -/
def pbwMonomialBasis : Module.Basis (Fin r →₀ ℕ) k U :=
  let h := orderedPBWBasis k L r b
  (Module.Basis.mk h.1 h.2.ge).reindex (Finsupp.equivFunOnFinite.symm)

theorem pbwMonomialBasis_apply (a : Fin r →₀ ℕ) :
    pbwMonomialBasis b a = orderedMonomial k L b indices a := by
  rw [pbwMonomialBasis, Module.Basis.reindex_apply, Module.Basis.mk_apply,
    ← exponentWord_product]
  simp only [orderedMonomial, word, List.map_map, exponentWord, expand, List.flatMap,
    List.map_ofFn, Function.comp_def, id_eq, Equiv.symm_symm, Finsupp.equivFunOnFinite_apply]

/-- The polynomial corresponding to an element's PBW terms of degree `d`. -/
def pbwSymbol (d : ℕ) : U →ₗ[k] P :=
  (pbwMonomialBasis b).constr k fun a => if a.degree = d then monomial a 1 else 0

theorem pbwSymbol_orderedMonomial (d : ℕ) (a : Fin r →₀ ℕ) :
    pbwSymbol b d (orderedMonomial k L b indices a) =
      if a.degree = d then monomial a 1 else 0 := by
  rw [← pbwMonomialBasis_apply, pbwSymbol, Module.Basis.constr_basis]

theorem pbwSymbol_coeff (d : ℕ) (u : U) (a : Fin r →₀ ℕ) :
    (pbwSymbol b d u).coeff a =
      if a.degree = d then (pbwMonomialBasis b).repr u a else 0 := by
  classical
  have hLinear : (lcoeff k a).comp (pbwSymbol b d) =
      if a.degree = d then (pbwMonomialBasis b).coord a else 0 := by
    apply (pbwMonomialBasis b).ext
    intro c
    by_cases h : c = a
    · subst c
      by_cases hDegree : a.degree = d <;> simp [pbwSymbol, Module.Basis.constr_basis,
        Module.Basis.coord_apply, Module.Basis.repr_self, hDegree]
    · by_cases hDegree : a.degree = d <;> by_cases hc : c.degree = d <;>
        simp [pbwSymbol, Module.Basis.constr_basis, Module.Basis.coord_apply,
          Module.Basis.repr_self, h, Ne.symm h, hDegree, hc]
  have h := LinearMap.congr_fun hLinear u
  by_cases hDegree : a.degree = d <;> simpa [hDegree, Module.Basis.coord_apply] using h

theorem pbwSymbol_eq_zero_of_lt {d e : ℕ} (h : e < d) {u : U}
    (hu : u ∈ degreeFiltration k L e) : pbwSymbol b d u = 0 := by
  have hSpan := degreeFiltration_le_orderedSpan k L b nodup_indices mem_indices e hu
  clear hu
  induction hSpan using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    rw [pbwSymbol_orderedMonomial, ite_eq_right (ne_of_lt (lt_of_le_of_lt ha h))]
  | zero => exact map_zero _
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul c u _ hu => rw [map_smul, hu, smul_zero]

/-- The symbol of a generator, as a linear polynomial. -/
def pbwLinearPolynomial : L →ₗ[k] P := b.constr k X

@[simp] theorem pbwLinearPolynomial_basis (i : Fin r) :
    pbwLinearPolynomial b (b i) = X i :=
  b.constr_basis k X i

private theorem symbol_basisWord (l : List (Fin r)) :
    pbwSymbol b l.length (word k L (l.map b)) = (l.map (X : Fin r → P)).prod := by
  let a := Multiset.toFinsupp (l : Multiset (Fin r))
  have hDegree : a.degree = l.length := degree_toFinsupp l
  have hPerm := ((perm_expand nodup_indices mem_indices l).map b)
  have hDiff : pbwSymbol b l.length
      (word k L (l.map b) - orderedMonomial k L b indices a) = 0 := by
    cases l with
    | nil =>
      have he : expand indices a = [] := List.flatMap_eq_nil_iff.mpr (by simp [a])
      simp [orderedMonomial, he]
    | cons i l =>
      have h := word_sub_word_mem_of_perm k L hPerm
      rw [List.length_map] at h
      exact pbwSymbol_eq_zero_of_lt b (by simp) h
  rw [map_sub, sub_eq_zero, pbwSymbol_orderedMonomial, hDegree, ite_eq_left rfl] at hDiff
  rw [hDiff, list_prod_map_X]

theorem pbwSymbol_word (l : List L) :
    pbwSymbol b l.length (word k L l) = (l.map (pbwLinearPolynomial b)).prod := by
  have h : (pbwSymbol b l.length).compMultilinearMap
      ((MultilinearMap.mkPiAlgebraFin k l.length U).compLinearMap
        (fun _ => (UniversalEnvelopingAlgebra.ι k (L := L)).toLinearMap)) =
      (MultilinearMap.mkPiAlgebraFin k l.length P).compLinearMap
        (fun _ => pbwLinearPolynomial b) := by
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro a
    simpa [MultilinearMap.compMultilinearMap_apply, word,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
      List.map_ofFn, Function.comp_def] using
        symbol_basisWord b (List.ofFn a)
  have hEval := congrArg (fun f : MultilinearMap k (fun _ : Fin l.length => L) P =>
    f l.get) h
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply] at hEval
  change pbwSymbol b l.length
    ((List.ofFn (UniversalEnvelopingAlgebra.ι k ∘ l.get)).prod) =
      (List.ofFn (pbwLinearPolynomial b ∘ l.get)).prod at hEval
  rw [← List.map_ofFn, ← List.map_ofFn, List.ofFn_get] at hEval
  exact hEval

/-- The derivation on the polynomial algebra induced by the Lie bracket with `x`. -/
def pbwCoadjointDerivation (x : L) : Derivation k P P :=
  mkDerivation k (fun i => pbwLinearPolynomial b ⁅x, b i⁆)

@[simp] theorem pbwCoadjointDerivation_X (x : L) (i : Fin r) :
    pbwCoadjointDerivation b x (X i) = pbwLinearPolynomial b ⁅x, b i⁆ :=
  mkDerivation_X k _ _

theorem pbwCoadjointDerivation_linear (x y : L) :
    pbwCoadjointDerivation b x (pbwLinearPolynomial b y) =
      pbwLinearPolynomial b ⁅x, y⁆ := by
  let ad : L →ₗ[k] L :=
    { toFun := fun z => ⁅x, z⁆
      map_add' := fun z t => lie_add x z t
      map_smul' := fun a z => lie_smul a x z }
  have h : (pbwCoadjointDerivation b x).toLinearMap.comp (pbwLinearPolynomial b) =
      (pbwLinearPolynomial b).comp ad := by
    apply b.ext
    intro i
    change pbwCoadjointDerivation b x (pbwLinearPolynomial b (b i)) =
      pbwLinearPolynomial b ⁅x, b i⁆
    rw [pbwLinearPolynomial_basis, pbwCoadjointDerivation_X]
  exact LinearMap.congr_fun h y

private theorem word_append_eq (l v : List L) :
    word k L (l ++ v) = word k L l * word k L v := by
  simp [word, List.map_append, List.prod_append]

private theorem pbwSymbol_prefixed_commutator_word (x : L) (l head : List L) :
    pbwSymbol b (head.length + l.length)
      (word k L head * (UniversalEnvelopingAlgebra.ι k x * word k L l -
        word k L l * UniversalEnvelopingAlgebra.ι k x)) =
      (head.map (pbwLinearPolynomial b)).prod *
        pbwCoadjointDerivation b x ((l.map (pbwLinearPolynomial b)).prod) := by
  induction l generalizing head with
  | nil => simp
  | cons y l ih =>
    have hxy : UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ =
        UniversalEnvelopingAlgebra.ι k x * UniversalEnvelopingAlgebra.ι k y -
        UniversalEnvelopingAlgebra.ι k y * UniversalEnvelopingAlgebra.ι k x :=
      (UniversalEnvelopingAlgebra.ι k).map_lie x y
    have hSplit :
        word k L head * (UniversalEnvelopingAlgebra.ι k x * word k L (y :: l) -
            word k L (y :: l) * UniversalEnvelopingAlgebra.ι k x) =
          word k L (head ++ ⁅x, y⁆ :: l) +
            word k L (head ++ [y]) *
              (UniversalEnvelopingAlgebra.ι k x * word k L l -
                word k L l * UniversalEnvelopingAlgebra.ι k x) := by
      simp only [word_append_eq, word_cons, word_nil, mul_one, hxy]
      noncomm_ring
    have hPrefixLen : (head ++ [y]).length + l.length =
        head.length + (y :: l).length := by simp; omega
    have hWordLen : (head ++ ⁅x, y⁆ :: l).length =
        head.length + (y :: l).length := by simp
    have hS := pbwSymbol_word b (head ++ ⁅x, y⁆ :: l)
    rw [hWordLen] at hS
    have hR := ih (head ++ [y])
    rw [hPrefixLen] at hR
    rw [hSplit, map_add, hS, hR]
    simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.map_nil,
      List.prod_nil, mul_one, Derivation.leibniz, smul_eq_mul, pbwCoadjointDerivation_linear]
    ring

/-- On elements of degree at most `d`, the symbol carries the commutator with a generator to
the corresponding derivation of the polynomial ring. -/
theorem pbwSymbol_commutator (x : L) {d : ℕ} {u : U} (hu : u ∈ degreeFiltration k L d) :
    pbwSymbol b d (UniversalEnvelopingAlgebra.ι k x * u - u * UniversalEnvelopingAlgebra.ι k x) =
      pbwCoadjointDerivation b x (pbwSymbol b d u) := by
  have hu' := degreeFiltration_le_wordSpan k L d hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    rcases lt_or_eq_of_le hl with hlt | heq
    · rw [pbwSymbol_eq_zero_of_lt b hlt (word_mem_degreeFiltration k L l), map_zero]
      apply pbwSymbol_eq_zero_of_lt b hlt
      exact commutator_degreeOne_mem k L (generator_mem_degreeOne k L x)
        (word_mem_degreeFiltration k L l)
    · subst d
      simpa only [word_nil, one_mul, List.length_nil, zero_add, List.map_nil, List.prod_nil,
        pbwSymbol_word] using pbwSymbol_prefixed_commutator_word b x l []
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add, add_mul, add_sub_add_comm, map_add, hu, hv, map_add, map_add]
  | smul c u _ hu =>
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul, hu, map_smul, Derivation.map_smul]

end Langlands.Algebra.UniversalEnveloping
