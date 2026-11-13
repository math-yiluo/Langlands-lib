# Tensor evaluation for a generator with elementwise kernels

Module `Langlands.CategoryTheory.Renard.GeneratorTensorEvaluation`.
Namespace `Langlands.Renard`. Universe parameters `w v u`.
Worker 143 wrote this helper module for Task 5607, the proof of
`Langlands.CuspidalSupport.RationalSummandTensorQuasiInverseStatement`
(Renard VI.4.1, the quasi-inverse (VI.4.1.4)).

The module is abstract and elementary. It contains no statement definition and
makes no claim about smooth representations.

## Setting

- `C` is a preadditive category (`[Category.{v} C] [Preadditive C]`).
- `V : C → Type w` assigns an abelian group `V X` to every object.
- `u : (X ⟶ Y) → V X →+ V Y` assigns an additive map to every morphism.

The theorems use three compatibility hypotheses, each passed as an explicit
argument:

- `hid : u (𝟙 X) x = x`;
- `hcomp : u (f ≫ g) x = u g (u f x)`;
- `hadd : u (f + g) x = u f x + u g x`.

From these, `u 0 = 0` follows inside the proof.

The intended instance is a full subcategory of smooth representations, with `V X`
the carrier of `X` and `u f` the underlying map of `f`. The module
`Langlands.Representation.Category.GeneratorTensorEvaluation` supplies it.

## Declarations

- `tensorEvaluationBalancing V u P Y`: the `ℤ`-submodule of `(P ⟶ Y) ⊗[ℤ] V P`
  spanned by the balancing elements `(r ≫ α) ⊗ₜ w - α ⊗ₜ u r w`, where
  `r : End P`, `α : P ⟶ Y` and `w : V P`.
- `tensorEvaluationPairing hadd P Y`: the `ℤ`-bilinear map `(α, w) ↦ u α w`.
  Additivity in `α` is `hadd`, additivity in `w` is additivity of `u α`, and
  compatibility with `ℤ`-scalars follows from these.
- `tensorEvaluation hadd P Y : (P ⟶ Y) ⊗[ℤ] V P →ₗ[ℤ] V Y`: the map
  `TensorProduct.lift` of the pairing. Its simp lemma `tensorEvaluation_tmul`
  says `α ⊗ₜ w ↦ u α w`.
- `tensorEvaluationBalancing_le_ker`: the balancing span lies in the kernel of
  the evaluation (uses `hcomp`).
- `map_mem_of_generator`: let `Φ : V K →+ M` be additive and `S` an additive
  subgroup of `M`. Suppose every element of `V K` lies in the additive closure of
  the elements `u β w` with `β : P ⟶ K`. If `Φ (u β w) ∈ S` for all such `β, w`,
  then `Φ x ∈ S` for every `x`.
- `tensorEvaluation_surjective_and_ker [HasFiniteBiproducts C] P Y hgen hker`:
  the main theorem. Its two hypotheses are:
  - `hgen`: for every object `X`, every element of `V X` lies in
    `AddSubgroup.closure {u α w | α : P ⟶ X, w : V P}`, so `P` generates
    elementwise;
  - `hker`: for every `f : X ⟶ Z` and every `x : V X` with `u f x = 0`, there
    are an object `K`, a morphism `ι : K ⟶ X` and an element `k : V K` with
    `u ι k = x` and `ι ≫ f = 0`, so kernels exist elementwise.

  The conclusion is that `tensorEvaluation hadd P Y` is surjective and that its
  kernel equals `tensorEvaluationBalancing V u P Y`.
- `exists_tensorEvaluation`: the same result in the existential form of the
  target statement. Under the same hypotheses there is a `ℤ`-linear
  `ev : (P ⟶ Y) ⊗[ℤ] V P → V Y` with `ev (α ⊗ₜ w) = u α w`, which is surjective
  and whose kernel is the `ℤ`-span of `(p.1 ≫ p.2.1) ⊗ₜ p.2.2 - p.2.1 ⊗ₜ u p.1 p.2.2`
  over `p : End P × (P ⟶ Y) × V P`.

## Proof

**Surjectivity.** The range of the evaluation is an additive subgroup containing
every `u α w = ev (α ⊗ₜ w)`. By `hgen` it therefore contains `V Y`.

**Balancing ⊆ kernel.** This follows from
`ev ((r ≫ α) ⊗ₜ w) = u (r ≫ α) w = u α (u r w) = ev (α ⊗ₜ u r w)`.

**Kernel ⊆ balancing.** Take `x` in the kernel.

1. By `TensorProduct.exists_finset`, `x` is a finite sum of pure tensors. Using
   `Finset.equivFin`, it is written as `x = ∑_{s : Fin n} α_s ⊗ₜ w_s`. The
   index lives in `Type`, as `biproduct.desc_eq` requires.
2. Let `B = ⨁_{s : Fin n} P` and `φ = biproduct.desc α : B ⟶ Y`. Put
   `y = ∑_s u (ι_s) w_s ∈ V B`. Then
   `u φ y = ∑_s u α_s w_s = ev x = 0`, using `hcomp` and `ι_s ≫ φ = α_s`.
3. By `hker` there are `K`, `ι : K ⟶ B` and `k ∈ V K` with `u ι k = y` and
   `ι ≫ φ = 0`.
4. Define the additive map `Φ : V K → (P ⟶ Y) ⊗[ℤ] V P`,
   `Φ k' = ∑_s α_s ⊗ₜ u (ι ≫ π_s) k'`. Then `Φ k = x`, because
   `u (ι ≫ π_s) k = u π_s y = w_s`. This uses `ι_t ≫ π_s = δ_{ts}`, `hid`, and
   `u 0 = 0`; the last follows from `hadd`.
5. It remains to show that `Φ` maps into the balancing span. By
   `map_mem_of_generator` and `hgen K`, it suffices to treat `k' = u β w'` with
   `β : P ⟶ K`. Put `r_s = β ≫ ι ≫ π_s : End P`. Since
   `∑_s r_s ≫ α_s = β ≫ ι ≫ φ = 0` (by `biproduct.desc_eq` and
   `Preadditive.comp_sum`), we get
   `Φ (u β w') = ∑_s α_s ⊗ₜ u r_s w' = -∑_s ((r_s ≫ α_s) ⊗ₜ w' - α_s ⊗ₜ u r_s w')`.
   This is a negated sum of balancing generators.

## Provenance

This is an internal helper. It records the elementary algebra behind Renard's
claim that `ev_E : Hom_G(Π, τ) ⊗_R V_Π → E` is an isomorphism (VI.4.1, proof
of the Theorem, printed pp.150–151 / PDF pp.156–157 of
`renard-2026-representations-groupes-reductifs-padiques`). The route differs
from Renard's. He presents `E` as a cokernel of direct sums of copies of `V_Π`
and applies the five lemma to (VI.4.1.5). Here only finitely many copies of `P`
are used, together with elementwise generation and elementwise kernels. No
infinite direct sums and no right exactness of the tensor product are needed.

## Imports

| Module | Used for |
| --- | --- |
| `Mathlib.CategoryTheory.Preadditive.Biproducts` | finite biproducts, `biproduct.desc_eq`, `biproduct.ι_π_self`, `biproduct.ι_π_ne` |
| `Mathlib.LinearAlgebra.TensorProduct.Finiteness` | `TensorProduct.exists_finset` |
