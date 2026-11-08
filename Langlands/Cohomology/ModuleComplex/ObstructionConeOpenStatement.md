# Openness of first-cohomology vanishing for an obstruction cone

Module `Langlands.Cohomology.ModuleComplex.ObstructionConeOpenStatement`, namespace
`Langlands.Cohomology.ModuleComplex.ObstructionCone`. Written by Worker 967 and
Worker 207 for task `14dfbe95-4d4a-46fd-933a-182df994126c` (openness of versality for actual
Picard families). This is the commutative-algebra interface of that proof. The geometric
part only uses `HOneVanishes` and the proved `OpenStatement`. This file contains definitions
only.

## `HOneVanishes C d δ θ z M`

Data: a commutative ring `A`, an `ℕ`-indexed family of `A`-modules `C i` with
`A`-linear maps `d i : C i → C (i + 1)`, `A`-modules `F` and `Q`, an `A`-linear
map `δ : Q → F`, an element `θ : C 1 ⊗[A] F` and an element `z : C 2 ⊗[A] Q`.
For an `A`-module `M` the proposition says the following. For every
`c : C 1 ⊗[A] M` and every `A`-linear `φ : Q → M` with

```text
(d 1 ⊗ M) c + (C 2 ⊗ φ) z = 0   in C 2 ⊗[A] M,
```

there are `b : C 0 ⊗[A] M` and an `A`-linear `D : F → M` with

```text
c = (d 0 ⊗ M) b + (C 1 ⊗ D) θ   and   φ + D ∘ δ = 0.
```

Lean writes `(d i ⊗ M)` as `(d i).rTensor M` and `(C i ⊗ φ)` as
`φ.lTensor (C i)`.

Interpretation (not part of the Lean statement). Assume `d θ = δ_* z` and
`d z = 0`, `F` is finite projective and `G₁ → G₀ → Q → 0` is a free
presentation. Then `HOneVanishes … M` is the vanishing of `H¹` of
`cone(α) ⊗ M`. Here `α : [F^∨ → G₀^∨ → G₁^∨ → ⋯] → C` is the chain map whose
degree-one part is `D ↦ D_* θ` and whose degree-two part is a lift `z₀` of `z`.
The cone has differential `(c, a) ↦ (d c + α a, -d a)`. In the application,
`C` is the Čech complex of the structure sheaf of `X_{A₀}` for a finite affine
cover. `Q = J/J²` comes from a presentation `A₀ = P/J`. `F = A₀ ⊗ Ω_{(P/J²)/R}`.
`z` is the obstruction cocycle of lifted transition functions of the line bundle,
and `θ` is its Kodaira–Spencer cochain.

## `OpenStatement`

For every noetherian ring `A` and every complex `(C, d)` of flat `A`-modules
with `d (i+1) ∘ d i = 0`, all `C i` trivial for `i > n`, and finitely
generated `ker (d 0)` and `ker (d (i+1)) / range (d i)`, take the following.
Let `F` be finite projective and `Q` finite. Take `δ : Q → F`, `θ` and `z`
with `(d 1 ⊗ F) θ = (C 2 ⊗ δ) z` and `(d 2 ⊗ Q) z = 0`. Let `k` be a field
with an `A`-algebra structure such that `HOneVanishes C d δ θ z k` holds.
Then there is `g : A` with `algebraMap A k g ≠ 0` such that, for every
`A`-algebra `S` in which `g` is a unit and every `S`-module `M` (with
compatible `A`-action), `HOneVanishes C d δ θ z M` holds.

The finiteness hypotheses use the same form as the Library's
`Langlands.Cohomology.ModuleComplex.BoundedFlatComplexProjectiveStatement`.

## Proof

The proposition is proved by `Langlands.Cohomology.ModuleComplex.ObstructionCone.openStatement`
in `Langlands.Cohomology.ModuleComplex.ObstructionConeOpenProof`. The proof replaces `C` by a
finite projective model, transports `θ` and `z` to it, and expresses `HOneVanishes` as middle
exactness of an explicit three-term complex of finite projective modules. It then spreads that
exactness by a determinant and splitting argument. That module's Markdown describes the steps.

## Provenance

This is internal. It is a linear-algebra form of the openness step in The Stacks
Project, Artin's Axioms, Lemma 98.23.4 (Tag 07YN) and More on Algebra,
Lemma 78.4. It is specialised to a cone over a Čech-type complex, as suggested in
the task context.
