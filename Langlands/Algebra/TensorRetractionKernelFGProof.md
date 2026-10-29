# Proof of finite generation of the canonical tensor retraction kernel

`Langlands.Algebra.tensorRetractionKernelFG.{u, v, w}` proves the Library
proposition `Langlands.Algebra.TensorRetractionKernelFGStatement.{u, v, w}`,
imported from `Langlands.Algebra.TensorRetractionKernelFGStatement`. Its type
is exactly that closed proposition, with the three independent universe levels
`u` (for `R`), `v` (for `S`) and `w` (for `T`). The statement pair and its
imports are unchanged. The module also imports Mathlib's
`Mathlib.RingTheory.Ideal.Quotient.Operations` for the quotient-ring API.

## Statement proved

Let `R : Type u`, `S : Type v` and `T : Type w` be commutative rings with the
given algebra structures `Algebra R S`, `Algebra S T` and `Algebra R T`, and
with `IsScalarTower R S T`. Assume `Algebra.EssFiniteType R S`. Let

```lean
μ := (AlgHom.liftEquiv R S T T) (AlgHom.id R T) : S ⊗[R] T →ₐ[S] T
```

be the canonical map with `μ (s ⊗ₜ t) = s • t = algebraMap S T s * t`. Then
`RingHom.ker μ` is a finitely generated ideal of `S ⊗[R] T` (`Ideal.FG`).
No hypothesis beyond those of the statement is added: nothing is assumed
about `T` beyond the tower, nor any finite presentation, Noetherianity,
flatness or nontriviality. The proof uses the given `Algebra S T` structure
throughout; it chooses no other one.

## Proof

The proof introduces all the data of the statement. The hypothesis
`Algebra.EssFiniteType R S` is introduced as a local instance. It works
`classical`ly, for the `Finset.image` below.

1. **The finite generating set.** Let `σ := Algebra.EssFiniteType.finset R S`,
   Mathlib's chosen finite set witnessing essential finite type. Define the
   finset `gens` of `S ⊗[R] T` as the image of `σ` under
   `s ↦ s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] algebraMap S T s`. The proof supplies `gens` as
   the witness of `Ideal.FG`, so it remains to show
   `Ideal.span gens = RingHom.ker μ`. This is done by `le_antisymm`.

2. **`span gens ≤ ker μ`.** By `Finset.coe_image` and `Ideal.span_le` it
   suffices that each generator lies in the kernel. By `liftEquiv_tmul` (a simp
   lemma), `μ` sends `s ⊗ₜ 1` to `s • 1` and `1 ⊗ₜ algebraMap S T s` to
   `1 • algebraMap S T s`. Both equal `algebraMap S T s` (`Algebra.smul_def`,
   `one_smul`), so the difference maps to `0`. `simp` with `RingHom.mem_ker`
   and `Algebra.smul_def` closes this goal.

3. **The quotient map.** For the reverse inclusion, let `J := Ideal.span gens`.
   Let `q : S ⊗[R] T →ₐ[R] (S ⊗[R] T) ⧸ J` be
   `IsScalarTower.toAlgHom R (S ⊗[R] T) _`. This is the quotient map
   `Ideal.Quotient.mk J`, viewed as an `R`-algebra map
   (`Ideal.Quotient.algebraMap_eq`).

4. **Two `R`-algebra maps out of `S` agree (`key`).** Consider the
   `R`-algebra maps `S → (S ⊗[R] T) ⧸ J` given by
   - `q.comp Algebra.TensorProduct.includeLeft`, that is, `s ↦ q (s ⊗ₜ 1)`, and
   - `(q.comp Algebra.TensorProduct.includeRight).comp (IsScalarTower.toAlgHom R S T)`,
     that is, `s ↦ q (1 ⊗ₜ algebraMap S T s)`. The map
     `IsScalarTower.toAlgHom R S T` is `algebraMap S T` as an `R`-algebra
     map; this is where `IsScalarTower R S T` is used.

   By `Algebra.EssFiniteType.algHom_ext`, two `R`-algebra maps out of `S` are
   equal once they agree on `σ`. For `a ∈ σ`, after `simp only` unfolds the
   compositions, `Ideal.Quotient.mk_eq_mk_iff_sub_mem` reduces agreement to
   `a ⊗ₜ 1 - 1 ⊗ₜ algebraMap S T a ∈ J`. This holds by `Ideal.subset_span`,
   because that element is the image of `a` in `gens`. This is the same
   argument as in Mathlib's `KaehlerDifferential.ideal_fg`, which treats the
   case `T = S`.

5. **`q y = q (1 ⊗ₜ μ y)` for all `y` (`hall`).** The proof uses the default
   induction principle on `S ⊗[R] T` (`TensorProduct.inductionOn`), with a
   pure-tensor case and an addition case.
   - *Pure tensors.* Evaluating `key` at `s` gives
     `q (s ⊗ₜ 1) = q (1 ⊗ₜ algebraMap S T s)` (`AlgHom.congr_fun`, then
     `simpa`). Then a `calc` chain proves:

     ```text
     q (s ⊗ₜ t) = q (s ⊗ₜ 1) * q (1 ⊗ₜ t)
                = q (1 ⊗ₜ algebraMap S T s) * q (1 ⊗ₜ t)
                = q (1 ⊗ₜ μ (s ⊗ₜ t)).
     ```

     The first and last steps rewrite with multiplicativity of `q` (`map_mul`)
     and `Algebra.TensorProduct.tmul_mul_tmul`. The last step also uses
     `μ (s ⊗ₜ t) = algebraMap S T s * t` (`liftEquiv_tmul`,
     `Algebra.smul_def`).
   - *Sums.* If the identity holds for `a` and `b`, it holds for `a + b`.
     The proof rewrites with additivity of `q` and of `μ` (`map_add`) and with
     `TensorProduct.tmul_add`.

6. **Conclusion.** Let `x ∈ ker μ`, so `μ x = 0` (`RingHom.mem_ker`). Then
   `hall x` becomes `q x = q (1 ⊗ₜ 0) = 0` (`TensorProduct.tmul_zero`,
   `map_zero`). By `Ideal.Quotient.eq_zero_iff_mem`, `x ∈ J`. Hence
   `ker μ ≤ span gens`.

Together, steps 2 and 6 give `Ideal.span gens = RingHom.ker μ`, so the kernel
is spanned by a finite set.

## Provenance and checks

This is the proof of an internal supporting statement. Its route is the one
proposed in the statement's Markdown and adapts the proof of Mathlib's
`KaehlerDifferential.ideal_fg` in `Mathlib/RingTheory/Kaehler/Basic.lean`
from `S ⊗[R] S` to `S ⊗[R] T`. It uses no essential finite presentation
result and no Library theorem other than the statement definition.

The development check reported only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The unapplied constant
`@Langlands.Algebra.tensorRetractionKernelFG.{u, v, w}` was assigned directly to
`Langlands.Algebra.TensorRetractionKernelFGStatement.{u, v, w}` and to its
expanded `∀ (R : Type u) (S : Type v) (T : Type w) …` telescope. Both
assignments elaborated.
