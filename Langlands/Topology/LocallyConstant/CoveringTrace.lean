import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! # Actual finite-fiber trace of locally constant functions -/

noncomputable section

universe u v w t r

namespace Langlands.LocallyConstantCovering

open Topology
open scoped BigOperators

variable {X : Type u} {Y : Type v} {Z : Type t} {V : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [AddCommGroup V]

/-- The sum over the entire actual fiber, including an empty fiber. -/
def fiberSum (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (f : X → V) (y : Y) : V :=
  letI := Fintype.ofFinite (q ⁻¹' {y})
  ∑ x : q ⁻¹' {y}, f x.val

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Reindex the actual fiber sum by any finite type equivalent to that fiber. -/
theorem fiberSum_eq_sum (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (f : X → V) (y : Y) {I : Type*} [Fintype I] (e : I ≃ q ⁻¹' {y}) :
    fiberSum q f y = ∑ i, f (e i).val := by
  let := Fintype.ofFinite (q ⁻¹' {y})
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Equality of original maps identifies their literal fiber sums. -/
theorem fiberSum_congr {q p : X → Y} [∀ y, Finite (q ⁻¹' {y})]
    [∀ y, Finite (p ⁻¹' {y})] (h : q = p) (f : X → V) (y : Y) :
    fiberSum q f y = fiberSum p f y := by
  subst p
  rfl

/-- The fiber of a composite is the disjoint union of the original fibers
over the actual intermediate fiber. -/
def compFiberEquiv (q : X → Y) (p : Y → Z) (z : Z) :
    (Σ y : p ⁻¹' {z}, q ⁻¹' {y.val}) ≃ (p ∘ q) ⁻¹' {z} where
  toFun x := ⟨x.2.val, (congrArg p x.2.property).trans x.1.property⟩
  invFun x := ⟨⟨q x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    change q x = y at hx
    subst y
    rfl
  right_inv x := rfl

omit [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] in
/-- Finite actual fibers are preserved by composition. -/
theorem finite_comp_fiber (q : X → Y) (p : Y → Z)
    [∀ y, Finite (q ⁻¹' {y})] [∀ z, Finite (p ⁻¹' {z})] (z : Z) :
    Finite ((p ∘ q) ⁻¹' {z}) :=
  Finite.of_equiv (Σ y : p ⁻¹' {z}, q ⁻¹' {y.val}) (compFiberEquiv q p z)

omit [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] in
/-- Literal finite-fiber sums compose by partitioning the composite fiber. -/
theorem fiberSum_comp (q : X → Y) (p : Y → Z)
    [∀ y, Finite (q ⁻¹' {y})] [∀ z, Finite (p ⁻¹' {z})]
    [∀ z, Finite ((p ∘ q) ⁻¹' {z})] (f : X → V) (z : Z) :
    fiberSum (p ∘ q) f z = fiberSum p (fiberSum q f) z := by
  classical
  let := Fintype.ofFinite (p ⁻¹' {z})
  let (y : p ⁻¹' {z}) := Fintype.ofFinite (q ⁻¹' {y.val})
  rw [fiberSum_eq_sum (p ∘ q) f z (compFiberEquiv q p z), Fintype.sum_sigma]
  rfl

/-- The identity fiber has exactly its original point. -/
def idFiberEquiv (x : X) : Unit ≃ (id : X → X) ⁻¹' {x} where
  toFun _ := ⟨x, rfl⟩
  invFun _ := Unit.unit
  left_inv _ := rfl
  right_inv y := Subtype.ext y.property.symm

omit [TopologicalSpace X] in
theorem finite_id_fiber (x : X) : Finite ((id : X → X) ⁻¹' {x}) :=
  Finite.of_equiv Unit (idFiberEquiv x)

/-- The identity admits its actual one-sheeted covering chart. -/
theorem isCoveringMap_id : IsCoveringMap (id : X → X) := by
  intro x
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
  exact ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_univ,
    (Homeomorph.prodUnique (Set.univ : Set X) Unit).symm, fun _ => rfl⟩

omit [TopologicalSpace X] in
@[simp]
theorem fiberSum_id [∀ x : X, Finite ((id : X → X) ⁻¹' {x})]
    (f : X → V) (x : X) : fiberSum id f x = f x := by
  rw [fiberSum_eq_sum id f x (idFiberEquiv x)]
  simp [idFiberEquiv]

section Action

variable {G : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- An equivariant map transports actual fibers by the original group action. -/
def smulFiberEquiv (q : X → Y) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (g : G) (y : Y) : q ⁻¹' {g⁻¹ • y} ≃ q ⁻¹' {y} where
  toFun x := ⟨g • x.val, by
    change q (g • x.val) = y
    rw [heq, show q x.val = g⁻¹ • y from x.property]
    simp⟩
  invFun x := ⟨g⁻¹ • x.val, by
    change q (g⁻¹ • x.val) = g⁻¹ • y
    rw [heq, show q x.val = y from x.property]⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Equivariant spatial translation commutes with the actual fiber sum. -/
theorem fiberSum_translate (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (g : G) (f : X → V) (y : Y) :
    fiberSum q (fun x => f (g⁻¹ • x)) y = fiberSum q f (g⁻¹ • y) := by
  classical
  let := Fintype.ofFinite (q ⁻¹' {g⁻¹ • y})
  rw [fiberSum_eq_sum q _ y (smulFiberEquiv q heq g y)]
  simp [smulFiberEquiv, fiberSum]

end Action

/-- A genuine evenly covered chart identifies each of its fibers with its
original discrete index, even when that index is empty. -/
def chartFiberEquiv {q : X → Y} {U : Set Y} {I : Type*} [TopologicalSpace I]
    (H : q ⁻¹' U ≃ₜ U × I) (hH : ∀ x, (H x).1.val = q x.val) (y : U) :
    I ≃ q ⁻¹' {y.val} where
  toFun i := ⟨(H.symm (y, i)).val, by
    change q (H.symm (y, i)).val = y.val
    simpa using (hH (H.symm (y, i))).symm⟩
  invFun x := (H ⟨x.val, by
    change q x.val ∈ U
    rw [show q x.val = y.val from x.property]
    exact y.property⟩).2
  left_inv i := by simp
  right_inv x := by
    let x' : q ⁻¹' U := ⟨x.val, by
      change q x.val ∈ U
      rw [show q x.val = y.val from x.property]
      exact y.property⟩
    have hfirst : (H x').1 = y := Subtype.ext ((hH x').trans x.property)
    have heq : (y, (H x').2) = H x' := Prod.ext hfirst.symm rfl
    apply Subtype.ext
    change (H.symm (y, (H x').2)).val = x.val
    rw [heq, H.symm_apply_apply]

/-- Covering charts prove local constancy of the literal finite-fiber sum.
There is no topology on the coefficients. -/
theorem isLocallyConstant_fiberSum (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (f : LocallyConstant X V) :
    IsLocallyConstant (fiberSum q f) := by
  classical
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro y
  obtain ⟨_, U, hyU, hU, _, H, hH⟩ := hq y
  let := Fintype.ofFinite (q ⁻¹' {y})
  let branch (i : q ⁻¹' {y}) : LocallyConstant U V :=
    ⟨fun z => f (H.symm (z, i)).val,
      f.isLocallyConstant.comp_continuous (by fun_prop)⟩
  let s : LocallyConstant U V := ∑ i, branch i
  have hs (z : U) : fiberSum q f z.val = s z := by
    rw [fiberSum_eq_sum q f z.val (chartFiberEquiv H hH z)]
    exact (map_sum (LocallyConstant.evalAddMonoidHom z) branch Finset.univ).symm
  obtain ⟨W, hW, hyW, hconst⟩ := s.isLocallyConstant.exists_open ⟨y, hyU⟩
  refine ⟨Subtype.val '' W, hU.isOpenMap_subtype_val _ hW, ⟨⟨y, hyU⟩, hyW, rfl⟩, ?_⟩
  rintro z ⟨z', hz', rfl⟩
  exact (hs z').trans ((hconst z' hz').trans (hs ⟨y, hyU⟩).symm)

/-- The covering trace is the locally constant function with that fiber sum. -/
def trace (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (f : LocallyConstant X V) : LocallyConstant Y V :=
  ⟨fiberSum q f, isLocallyConstant_fiberSum q hq f⟩

@[simp]
theorem trace_apply (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (f : LocallyConstant X V) (y : Y) :
    trace q hq f y = fiberSum q f y := rfl

/-- Trace composition agrees with the original composite covering map. -/
theorem trace_comp (q : X → Y) (p : Y → Z)
    [∀ y, Finite (q ⁻¹' {y})] [∀ z, Finite (p ⁻¹' {z})]
    [∀ z, Finite ((p ∘ q) ⁻¹' {z})]
    (hq : IsCoveringMap q) (hp : IsCoveringMap p) (hpq : IsCoveringMap (p ∘ q))
    (f : LocallyConstant X V) :
    trace (p ∘ q) hpq f = trace p hp (trace q hq f) := by
  ext z
  exact fiberSum_comp q p f z

@[simp]
theorem trace_id [∀ x : X, Finite ((id : X → X) ⁻¹' {x})]
    (h : IsCoveringMap (id : X → X)) (f : LocallyConstant X V) :
    trace id h f = f := by
  ext x
  exact fiberSum_id f x

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Nonzero trace can occur only in the image of the original nonzero support. -/
theorem support_fiberSum_subset (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (f : X → V) : Function.support (fiberSum q f) ⊆ q '' Function.support f := by
  classical
  intro y hy
  by_contra h
  apply hy
  dsimp [fiberSum]
  apply Finset.sum_eq_zero
  intro x _
  by_contra hx
  exact h ⟨x.val, hx, x.property⟩

/-- Local constancy closes the ordinary nonzero support, without separation
or a coefficient topology. -/
theorem tsupport_eq_support (f : LocallyConstant X V) :
    tsupport f = Function.support f := by
  apply IsClosed.closure_eq
  exact (f.isLocallyConstant.isOpen_fiber 0).isClosed_compl

/-- The trace's topological support lies in the actual image of the original
topological support. -/
theorem tsupport_trace_subset (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (f : LocallyConstant X V) :
    tsupport (trace q hq f) ⊆ q '' tsupport f := by
  rw [tsupport_eq_support, tsupport_eq_support]
  exact support_fiberSum_subset q f

/-- Continuous compact image and closed trace support prove compact support;
properness, Hausdorffness and compactness of the whole spaces are unnecessary. -/
theorem hasCompactSupport_trace (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (f : LocallyConstant X V) (hf : HasCompactSupport f) :
    HasCompactSupport (trace q hq f) :=
  (hf.image hq.continuous).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_trace_subset q hq f)

variable (R : Type r) [CommRing R] [Module R V]

/-- The unnormalized covering trace is linear for arbitrary module coefficients. -/
def traceLinearMap (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q) :
    LocallyConstant X V →ₗ[R] LocallyConstant Y V where
  toFun := trace q hq
  map_add' f g := by
    ext y
    simp [trace, fiberSum, Finset.sum_add_distrib]
  map_smul' a f := by
    ext y
    simp [trace, fiberSum, Finset.smul_sum]

variable {R}

/-- Original pointwise coefficient maps commute with the actual fiber sum. -/
theorem trace_map {W : Type*} [AddCommGroup W] [Module R W]
    (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (a : V →ₗ[R] W) (f : LocallyConstant X V) :
    trace q hq (LocallyConstant.mapₗ R a f) =
      LocallyConstant.mapₗ R a (trace q hq f) := by
  ext y
  simp [trace, fiberSum, map_sum]

end Langlands.LocallyConstantCovering
