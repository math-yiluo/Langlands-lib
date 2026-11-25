/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.NumberTheory.Padics.FiniteSumLattice
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Continuous functions into a finite sum of lattices

Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum).

The sheaf assertions are stated by their sections and restriction maps: the
submodule sum is equal sectionwise, the rank-r trivialization commutes with
restriction, and the scalar-extension comparison is specified on pure tensors.
Thus the tensor comparison is the one induced by the actual lattice inclusion.
-/

@[expose] public section

universe u v w z

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

set_option autoImplicit false

/-- The actual inclusion of continuous lattice-valued functions into vector-valued functions.
Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum). -/
def continuousLatticeInclusion {E : Type v} [NormedField E] (A : Subring E)
    {r : ℕ} (L : Submodule A (Fin r → E)) (Z : Type z) [TopologicalSpace Z] :
    C(Z, L) →ₗ[C(Z, A)] C(Z, Fin r → E) where
  toFun f := ⟨fun x ↦ (f x : Fin r → E), continuous_subtype_val.comp f.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem lattice_coordinates_coe {E : Type v} [CommRing E]
    (A : Subring E) {r : ℕ} (N : Submodule A (Fin r → E))
    (b : Module.Basis (Fin r) A N) (c : Module.Basis (Fin r) E (Fin r → E))
    (hbc : ∀ i, (b i : Fin r → E) = c i) (x : N) :
    c.equivFun (x : Fin r → E) = fun i ↦ (b.equivFun x i : E) := by
  have h (a : Fin r → A) :
      (b.equivFun.symm a : Fin r → E) =
        c.equivFun.symm (fun i ↦ (a i : E)) := by
    simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hbc i]; rfl
  have hx := h (b.equivFun x)
  rw [LinearEquiv.symm_apply_apply] at hx
  rw [hx, LinearEquiv.apply_symm_apply]

private theorem lattice_coordinates_continuous {E : Type v} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    (A : Subring E) {r : ℕ} (N : Submodule A (Fin r → E))
    (b : Module.Basis (Fin r) A N) (c : Module.Basis (Fin r) E (Fin r → E))
    (hbc : ∀ i, (b i : Fin r → E) = c i) : Continuous b.equivFun := by
  apply continuous_pi
  intro i
  apply continuous_induced_rng.mpr
  have h := (continuous_apply i).comp
    (c.equivFun.toLinearMap.continuous_on_pi.comp
      (continuous_subtype_val : Continuous (fun x : N ↦ (x : Fin r → E))))
  change Continuous (fun x : N ↦ (b.equivFun x i : E))
  change Continuous (fun x : N ↦ c.equivFun (x : Fin r → E) i) at h
  simpa only [lattice_coordinates_coe A N b c hbc] using h

private noncomputable def functionCoordinates
    {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (hb : Continuous b.equivFun)
    (Z : Type z) [TopologicalSpace Z] :
    (ι → C(Z, R)) ≃ₗ[C(Z, R)] C(Z, M) where
  toFun x := ⟨fun z ↦ b.equivFun.symm (fun i ↦ x i z),
    b.equivFun.symm.toLinearMap.continuous_on_pi.comp
      (continuous_pi fun i ↦ (x i).continuous)⟩
  invFun f := fun i ↦ ⟨fun z ↦ b.equivFun (f z) i,
    (continuous_apply i).comp (hb.comp f.continuous)⟩
  left_inv x := by
    ext i z
    exact congrFun (b.equivFun.apply_symm_apply (fun j ↦ x j z)) i
  right_inv f := by
    ext z
    exact b.equivFun.symm_apply_apply (f z)
  map_add' x y := by
    ext z
    exact b.equivFun.symm.map_add _ _
  map_smul' a x := by
    ext z
    exact b.equivFun.symm.map_smul (a z) (fun i ↦ x i z)

private theorem functionCoordinates_apply
    {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (hb : Continuous b.equivFun)
    (Z : Type z) [TopologicalSpace Z] (g : ι → C(Z, R)) (x : Z) :
    functionCoordinates b hb Z g x = b.equivFun.symm (fun i ↦ g i x) := rfl

private theorem functionCoordinates_symm_apply
    {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (hb : Continuous b.equivFun)
    (Z : Type z) [TopologicalSpace Z] (f : C(Z, M)) (i : ι) (x : Z) :
    (functionCoordinates b hb Z).symm f i x = b.equivFun (f x) i := rfl

attribute [local irreducible] functionCoordinates

private noncomputable def tensorCoordinates
    {R B M N ι : Type*} [CommRing R] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Fintype ι] [DecidableEq ι]
    (d : M ≃ₗ[R] (ι → R)) (e : (ι → B) ≃+ N) : (B ⊗[R] M) ≃+ N :=
  (d.lTensor B).toAddEquiv.trans
    ((TensorProduct.piScalarRight R R B ι).toAddEquiv.trans e)

private theorem tensorCoordinates_tmul
    {R B M N ι : Type*} [CommRing R] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Fintype ι] [DecidableEq ι]
    (d : M ≃ₗ[R] (ι → R)) (e : (ι → B) ≃+ N) (a : B) (f : M) :
    tensorCoordinates d e (a ⊗ₜ f) = e (fun i ↦ d f i • a) := by
  change e (TensorProduct.piScalarRight R R B ι (d.lTensor B (a ⊗ₜ f))) = _
  rw [LinearEquiv.lTensor_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

attribute [local irreducible] tensorCoordinates

private noncomputable def functionTensorCoordinates
    {E : Type v} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (A : Subring E) {r : ℕ}
    (N : Submodule A (Fin r → E)) (b : Module.Basis (Fin r) A N)
    (c : Module.Basis (Fin r) E (Fin r → E))
    (hb : Continuous b.equivFun) (hc : Continuous c.equivFun)
    (Z : Type z) [TopologicalSpace Z] :
    (C(Z, E) ⊗[C(Z, A)] C(Z, N)) ≃+ C(Z, Fin r → E) :=
  tensorCoordinates (functionCoordinates b hb Z).symm
    (functionCoordinates c hc Z).toAddEquiv

private theorem functionTensorCoordinates_tmul
    {E : Type v} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (A : Subring E) {r : ℕ}
    (N : Submodule A (Fin r → E)) (b : Module.Basis (Fin r) A N)
    (c : Module.Basis (Fin r) E (Fin r → E))
    (hbc : ∀ i, (b i : Fin r → E) = c i)
    (hb : Continuous b.equivFun) (hc : Continuous c.equivFun)
    (Z : Type z) [TopologicalSpace Z] (a : C(Z, E)) (f : C(Z, N)) (x : Z) :
    functionTensorCoordinates A N b c hb hc Z (a ⊗ₜ f) x =
      a x • (f x : Fin r → E) := by
  change tensorCoordinates (functionCoordinates b hb Z).symm
    (functionCoordinates c hc Z).toAddEquiv (a ⊗ₜ f) x = _
  rw [tensorCoordinates_tmul]
  change functionCoordinates c hc Z
    (fun i ↦ (functionCoordinates b hb Z).symm f i • a) x = _
  rw [functionCoordinates_apply]
  simp only [ContinuousMap.smul_apply', functionCoordinates_symm_apply]
  apply c.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, map_smul, lattice_coordinates_coe A N b c hbc]
  ext i
  change (b.equivFun (f x) i : E) * a x = a x * (b.equivFun (f x) i : E)
  exact mul_comm _ _

attribute [local irreducible] functionTensorCoordinates

private theorem lattice_sum_lifts {E : Type v} [CommRing E]
    (A : Subring E) {r : ℕ} {J : Type w} [Fintype J]
    (L : J → Submodule A (Fin r → E)) (x : ↥(⨆ j, L j)) :
    ∃ y : ∀ j, L j, ∑ j, (y j : Fin r → E) = (x : Fin r → E) := by
  classical
  have hx : (x : Fin r → E) ∈ ⨆ j ∈ (Finset.univ : Finset J), L j := by
    simp
  obtain ⟨y, hy⟩ := (Submodule.mem_iSup_finset_iff_exists_sum L _).mp hx
  exact ⟨y, by simpa using hy⟩

-- Keep the valuation-ring construction folded during scalar instance inference.
attribute [local irreducible] Padic.coefficientExtensionIntegers

/-- A finite sum of full lattices has a continuous linear section; continuous
functions preserve this sum, and on every small pro-etale site the resulting
module sheaf is free of rank r and its actual inclusion rationalizes to an isomorphism.

Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum).

Proof plan:
1. Apply lem-sfb-finite-sum-lattice to obtain an integral basis of the sum
   that is also a field basis. Restrict the continuous field coordinate map
   to obtain continuity of integral coordinates in the actual subspace topology.
2. Lift each basis vector to the finite product of the input lattices. Extend
   these lifts A-linearly using the coordinate homeomorphism. Coordinatewise
   finite sums and scalar multiplication show continuity and q composed with s is identity.
3. Postcompose any continuous function with the components of s. The resulting
   continuous functions sum to the given function, for every space Z.
4. Continuous functions into each lattice and the sum satisfy the sheaf condition:
   use lem-cbc-continuous-functions-fpqc-sheaf and restrict to the pro-etale site.
   Postcomposition with the basis homeomorphism gives the displayed rank-r
   trivializations. They commute with restriction, which is precomposition.
5. Step 3 identifies the sectionwise submodule sum with the sum-lattice sheaf.
   Since this is already a sheaf, it is also the sum as submodule sheaves.
6. Under the trivialization, the actual inclusion is the constant matrix whose
   columns are the basis vectors. Tensor the integral coordinate equivalence,
   distribute the tensor over the finite power, and reconstruct using the field
   basis. The pure-tensor formula specifies this actual comparison. These are
   exactly the sectionwise tensor assertions of the existing statement.
   All formulas also hold for r = 0.
-/
theorem continuous_lattice_sum
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (r : ℕ) (J : Type w) [Fintype J] [Nonempty J]
    (L : J → Submodule (Padic.coefficientExtensionIntegers ℓ E) (Fin r → E))
    (hL : ∀ j, ∃ b : Module.Basis (Fin r) (Padic.coefficientExtensionIntegers ℓ E) (L j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) :
    (∃ s : ↥(⨆ j, L j) →L[Padic.coefficientExtensionIntegers ℓ E] (∀ j, L j),
      ∀ x, (∑ j, ((s x j : L j) : Fin r → E)) = (x : Fin r → E)) ∧
    (∀ (Z : Type z) [TopologicalSpace Z] (f : C(Z, ↥(⨆ j, L j))),
      ∃ g : ∀ j, C(Z, L j), ∀ x,
        (∑ j, ((g j x : L j) : Fin r → E)) = (f x : Fin r → E)) ∧
    (∀ S : Scheme.{u},
      (∀ j, Presheaf.IsSheaf (Scheme.ProEt.topology S)
        ((Scheme.ProEt.forget S ⋙ Over.forget S).op ⋙ continuousMapPresheafAb (L j))) ∧
      Presheaf.IsSheaf (Scheme.ProEt.topology S)
        ((Scheme.ProEt.forget S ⋙ Over.forget S).op ⋙
          continuousMapPresheafAb ↥(⨆ j, L j)) ∧
      (∀ U : S.ProEt,
        (⨆ j, (continuousLatticeInclusion (Padic.coefficientExtensionIntegers ℓ E)
          (L j) U.left).range) =
        (continuousLatticeInclusion (Padic.coefficientExtensionIntegers ℓ E)
          (⨆ j, L j) U.left).range) ∧
      (∃ e : ∀ U : S.ProEt,
          (Fin r → C(U.left, Padic.coefficientExtensionIntegers ℓ E)) ≃ₗ[
            C(U.left, Padic.coefficientExtensionIntegers ℓ E)] C(U.left, ↥(⨆ j, L j)),
        ∀ (U V : S.ProEt) (a : V ⟶ U)
          (x : Fin r → C(U.left, Padic.coefficientExtensionIntegers ℓ E)),
          e V (fun i ↦ (x i).comp a.left.base.hom) = (e U x).comp a.left.base.hom) ∧
      (∀ U : S.ProEt,
        ∃ e : (C(U.left, E) ⊗[C(U.left, Padic.coefficientExtensionIntegers ℓ E)]
            C(U.left, ↥(⨆ j, L j))) ≃+ C(U.left, Fin r → E),
          ∀ (a : C(U.left, E)) (f : C(U.left, ↥(⨆ j, L j))) (x : U.left),
            e (a ⊗ₜ f) x = a x • (f x : Fin r → E))) := by
  classical
  let A := Padic.coefficientExtensionIntegers ℓ E
  let N : Submodule A (Fin r → E) := ⨆ j, L j
  obtain ⟨b, c, hbc⟩ := (Padic.finite_sum_lattice ℓ E r J L hL).1
  have hb : Continuous b.equivFun := lattice_coordinates_continuous A N b c hbc
  let y : Fin r → ∀ j, L j := fun i ↦ (lattice_sum_lifts A L (b i)).choose
  have hy (i : Fin r) : ∑ j, (y i j : Fin r → E) = (b i : Fin r → E) :=
    (lattice_sum_lifts A L (b i)).choose_spec
  let q : (∀ j, L j) →ₗ[A] (Fin r → E) :=
    ∑ j, (L j).subtype.comp (LinearMap.proj j)
  have hq (x : ∀ j, L j) : q x = ∑ j, (x j : Fin r → E) := by
    simp [q]
  let s₀ : N →ₗ[A] (∀ j, L j) := b.constr A y
  have hqs : q.comp s₀ = N.subtype := by
    apply b.ext
    intro i
    change q (s₀ (b i)) = (b i : Fin r → E)
    rw [show s₀ (b i) = y i from b.constr_basis A y i, hq]
    exact hy i
  have hs₀ : Continuous s₀ := by
    have ht := (s₀.comp b.equivFun.symm.toLinearMap).continuous_on_pi
    have heq : (s₀ : N → ∀ j, L j) =
        (s₀.comp b.equivFun.symm.toLinearMap) ∘ b.equivFun := by
      funext x
      exact (congrArg s₀ (b.equivFun.symm_apply_apply x)).symm
    rw [heq]
    exact ht.comp hb
  let s : N →L[A] (∀ j, L j) := ⟨s₀, hs₀⟩
  have hs (x : N) : ∑ j, (s x j : Fin r → E) = (x : Fin r → E) := by
    rw [← hq]
    exact LinearMap.congr_fun hqs x
  have hfunctions (Z : Type z) [TopologicalSpace Z] (f : C(Z, N)) :
      ∃ g : ∀ j, C(Z, L j), ∀ x,
        (∑ j, (g j x : Fin r → E)) = (f x : Fin r → E) := by
    refine ⟨fun j ↦ ⟨fun x ↦ s (f x) j,
      (continuous_apply j).comp (s.continuous.comp f.continuous)⟩, ?_⟩
    exact fun x ↦ hs (f x)
  refine ⟨⟨s, hs⟩, hfunctions, ?_⟩
  intro S
  have hsheaf (M : Type v) [TopologicalSpace M] [AddCommGroup M]
      [IsTopologicalAddGroup M] :
      Presheaf.IsSheaf (Scheme.ProEt.topology S)
        ((Scheme.ProEt.forget S ⋙ Over.forget S).op ⋙ continuousMapPresheafAb M) := by
    apply Functor.op_comp_isSheaf_of_isSheaf _ _ Scheme.proetaleTopology
    exact Presheaf.IsSheaf.of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb M)
  refine ⟨fun j ↦ hsheaf (L j), hsheaf N, ?_, ?_, ?_⟩
  · intro U
    apply le_antisymm
    · apply iSup_le
      intro j f hf
      obtain ⟨g, rfl⟩ := hf
      let g' : C(U.left, N) :=
        ⟨fun x ↦ ⟨(g x : Fin r → E), le_iSup L j (g x).property⟩,
          (continuous_subtype_val.comp g.continuous).subtype_mk _⟩
      exact ⟨g', rfl⟩
    · intro f hf
      obtain ⟨g, rfl⟩ := hf
      let gs : ∀ j, C(U.left, L j) := fun j ↦
        ⟨fun x ↦ s (g x) j,
          (continuous_apply j).comp (s.continuous.comp g.continuous)⟩
      have hgs (x : U.left) : ∑ j, (gs j x : Fin r → E) = (g x : Fin r → E) :=
        hs (g x)
      have heq : continuousLatticeInclusion A N U.left g =
          ∑ j, continuousLatticeInclusion A (L j) U.left (gs j) := by
        apply ContinuousMap.ext
        intro x
        rw [ContinuousMap.sum_apply]
        exact (hgs x).symm
      rw [heq]
      apply Submodule.sum_mem
      intro j _
      exact le_iSup (fun j ↦ (continuousLatticeInclusion A (L j) U.left).range) j
        ⟨gs j, rfl⟩
  · refine ⟨fun U ↦ functionCoordinates b hb U.left, ?_⟩
    intro U V a x
    apply ContinuousMap.ext
    intro z
    simp only [functionCoordinates_apply, ContinuousMap.comp_apply]
  · intro U
    have hc : Continuous c.equivFun := c.equivFun.toLinearMap.continuous_on_pi
    exact ⟨functionTensorCoordinates A N b c hb hc U.left,
      functionTensorCoordinates_tmul A N b c hbc hb hc U.left⟩

end AlgebraicGeometry.ProEtale
