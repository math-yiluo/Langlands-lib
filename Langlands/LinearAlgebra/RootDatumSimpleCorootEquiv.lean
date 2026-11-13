import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# Root data with spanning coroots are determined by the Cartan pairings of a base

For a finite reduced root datum whose coroots span the whole coweight lattice, the simple
coroots of a base form a `ℤ`-basis of that lattice. Two such root data whose bases are
identified by a bijection preserving all Cartan pairings are therefore isomorphic: the
coweight map is the basis equivalence of simple coroots, the weight map is its transpose,
and every root and coroot is reached from the simple ones by simple reflections.
-/

noncomputable section

open Set Function Module Submodule

namespace Langlands.RootDatumSimpleCorootEquiv

variable {ι ι₂ X Y X₂ Y₂ : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
  {P : RootDatum ι X Y} {Q : RootDatum ι₂ X₂ Y₂}

/-- Adjoint maps carrying the simple roots and coroots of a base to roots and coroots
with common indices carry every root and coroot to a root and coroot with a common index. -/
theorem exists_root_coroot_image [Finite ι] [P.IsReduced]
    (f : X →ₗ[ℤ] X₂) (g : Y →ₗ[ℤ] Y₂)
    (hfg : ∀ x y, Q.toLinearMap (f x) (g y) = P.toLinearMap x y)
    (b : P.Base)
    (hb : ∀ i ∈ b.support, ∃ k, f (P.root i) = Q.root k ∧ g (P.coroot i) = Q.coroot k)
    (i : ι) : ∃ k, f (P.root i) = Q.root k ∧ g (P.coroot i) = Q.coroot k := by
  refine b.induction_reflect i ?_ hb ?_
  · rintro i ⟨k, hk, hk'⟩
    refine ⟨Q.reflectionPerm k k, ?_, ?_⟩
    · rw [P.root_reflectionPerm, P.reflection_apply_self, map_neg, hk,
        Q.root_reflectionPerm, Q.reflection_apply_self]
    · rw [P.coroot_reflectionPerm, P.coreflection_apply_self, map_neg, hk',
        Q.coroot_reflectionPerm, Q.coreflection_apply_self]
  · rintro i j ⟨k, hk, hk'⟩ hj
    obtain ⟨l, hl, hl'⟩ := hb j hj
    have h1 : P.pairing i j = Q.pairing k l := by
      rw [← P.root_coroot_eq_pairing, ← hfg, hk, hl', Q.root_coroot_eq_pairing]
    have h2 : P.pairing j i = Q.pairing l k := by
      rw [← P.root_coroot_eq_pairing, ← hfg, hl, hk', Q.root_coroot_eq_pairing]
    refine ⟨Q.reflectionPerm l k, ?_, ?_⟩
    · rw [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_zsmul, hk, hl, h1,
        Q.root_reflectionPerm, Q.reflection_apply_root]
    · rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, map_sub, map_zsmul, hk', hl',
        h2, Q.coroot_reflectionPerm, Q.coreflection_apply_coroot]

/-- The simple coroots of a base form a `ℤ`-basis when the coroots span the coweight
lattice. -/
def simpleCorootBasis (b : P.Base) (hP : P.corootSpan ℤ = ⊤) : Basis b.support ℤ Y :=
  Basis.mk b.linearIndepOn_coroot <| by
    change ⊤ ≤ span ℤ (range <| P.coroot ∘ ((↑) : b.support → ι))
    rw [range_comp, Subtype.range_coe_subtype, Finset.setOfPred_mem, b.span_int_coroot_support]
    exact hP.ge

@[simp] lemma simpleCorootBasis_apply (b : P.Base) (hP : P.corootSpan ℤ = ⊤) (i : b.support) :
    simpleCorootBasis b hP i = P.coroot i := by
  simp [simpleCorootBasis]

/-- Elements of the weight lattice are separated by their pairings with simple coroots. -/
lemma eq_of_pairing_simpleCoroot (b : P.Base) (hP : P.corootSpan ℤ = ⊤) {z z' : X}
    (h : ∀ j : b.support, P.toLinearMap z (P.coroot j) = P.toLinearMap z' (P.coroot j)) :
    z = z' := by
  apply P.toPerfPair.injective
  apply (simpleCorootBasis b hP).ext
  intro j
  simpa using h j

section Equiv

variable (b : P.Base) (c : Q.Base) (hP : P.corootSpan ℤ = ⊤) (hQ : Q.corootSpan ℤ = ⊤)
  (e : b.support ≃ c.support)

/-- The coweight map: the linear equivalence carrying each simple coroot of `b` to the
simple coroot of `c` indexed by `e`. -/
def corootEquiv : Y ≃ₗ[ℤ] Y₂ :=
  (simpleCorootBasis b hP).equiv (simpleCorootBasis c hQ) e

lemma corootEquiv_coroot (i : b.support) :
    corootEquiv b c hP hQ e (P.coroot i) = Q.coroot (e i) := by
  rw [← simpleCorootBasis_apply b hP, corootEquiv, Basis.equiv_apply, simpleCorootBasis_apply]

lemma corootEquiv_symm_coroot (j : c.support) :
    (corootEquiv b c hP hQ e).symm (Q.coroot j) = P.coroot (e.symm j) := by
  rw [LinearEquiv.symm_apply_eq, corootEquiv_coroot, Equiv.apply_symm_apply]

/-- The weight map: the transpose of the inverse of `corootEquiv`, transported through the
perfect pairings of `P` and `Q`. -/
def rootEquiv : X ≃ₗ[ℤ] X₂ :=
  P.toPerfPair.trans ((corootEquiv b c hP hQ e).symm.dualMap.trans Q.toPerfPair.symm)

lemma toLinearMap_rootEquiv (x : X) (y : Y₂) :
    Q.toLinearMap (rootEquiv b c hP hQ e x) y =
      P.toLinearMap x ((corootEquiv b c hP hQ e).symm y) := by
  simp [rootEquiv]

lemma toLinearMap_rootEquiv_corootEquiv (x : X) (y : Y) :
    Q.toLinearMap (rootEquiv b c hP hQ e x) (corootEquiv b c hP hQ e y) =
      P.toLinearMap x y := by
  rw [toLinearMap_rootEquiv, LinearEquiv.symm_apply_apply]

variable (he : ∀ i j : b.support, Q.pairing (e i) (e j) = P.pairing i j)
include hP hQ he

lemma rootEquiv_root (i : b.support) :
    rootEquiv b c hP hQ e (P.root i) = Q.root (e i) := by
  apply eq_of_pairing_simpleCoroot c hQ
  intro j
  rw [toLinearMap_rootEquiv, corootEquiv_symm_coroot, P.root_coroot_eq_pairing,
    Q.root_coroot_eq_pairing, ← he, Equiv.apply_symm_apply]

/-- Two finite reduced root data with spanning coroots, with bases related by a bijection
preserving the Cartan pairings, are isomorphic by an equivalence extending that bijection. -/
theorem exists_equiv_indexEquiv [Finite ι] [Finite ι₂] [P.IsReduced] [Q.IsReduced] :
    ∃ f : RootPairing.Equiv P Q, ∀ i : b.support, f.indexEquiv i = e i := by
  set f := rootEquiv b c hP hQ e
  set g := corootEquiv b c hP hQ e
  have hfg : ∀ x y, Q.toLinearMap (f x) (g y) = P.toLinearMap x y :=
    toLinearMap_rootEquiv_corootEquiv b c hP hQ e
  have hfg' : ∀ x y, P.toLinearMap (f.symm x) (g.symm y) = Q.toLinearMap x y := by
    intro x y
    rw [← hfg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hb : ∀ i ∈ b.support, ∃ k, f (P.root i) = Q.root k ∧ g (P.coroot i) = Q.coroot k :=
    fun i hi ↦ ⟨e ⟨i, hi⟩, rootEquiv_root b c hP hQ e he ⟨i, hi⟩,
      corootEquiv_coroot b c hP hQ e ⟨i, hi⟩⟩
  have hc : ∀ j ∈ c.support, ∃ k, f.symm (Q.root j) = P.root k ∧
      g.symm (Q.coroot j) = P.coroot k := by
    intro j hj
    refine ⟨e.symm ⟨j, hj⟩, ?_, corootEquiv_symm_coroot b c hP hQ e ⟨j, hj⟩⟩
    rw [LinearEquiv.symm_apply_eq, rootEquiv_root b c hP hQ e he, Equiv.apply_symm_apply]
  choose σ hσ hσ' using exists_root_coroot_image (P := P) (Q := Q) f.toLinearMap g.toLinearMap
    hfg b hb
  choose τ hτ hτ' using exists_root_coroot_image (P := Q) (Q := P) f.symm.toLinearMap
    g.symm.toLinearMap hfg' c hc
  have hτσ : ∀ i, τ (σ i) = i := by
    intro i
    apply P.root.injective
    rw [← hτ, LinearEquiv.coe_coe, ← hσ, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hστ : ∀ j, σ (τ j) = j := by
    intro j
    apply Q.root.injective
    rw [← hσ, LinearEquiv.coe_coe, ← hτ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  let φ : ι ≃ ι₂ := ⟨σ, τ, hτσ, hστ⟩
  refine ⟨{ weightMap := f.toLinearMap
            coweightMap := g.symm.toLinearMap
            indexEquiv := φ
            weight_coweight_transpose := ?_
            root_weightMap := ?_
            coroot_coweightMap := ?_
            bijective_weightMap := f.bijective
            bijective_coweightMap := g.symm.bijective }, ?_⟩
  · ext y x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.dualMap_apply,
      LinearEquiv.coe_coe]
    have h := hfg x (g.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    simpa [RootPairing.flip] using h
  · funext i
    exact hσ i
  · funext j
    exact hτ' j
  · intro i
    apply Q.root.injective
    change Q.root (σ i) = Q.root (e i)
    rw [← hσ, LinearEquiv.coe_coe, rootEquiv_root b c hP hQ e he]

end Equiv

end Langlands.RootDatumSimpleCorootEquiv
