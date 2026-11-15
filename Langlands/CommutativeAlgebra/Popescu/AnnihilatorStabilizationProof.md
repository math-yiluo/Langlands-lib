# Proof: Ogoma's lemma on annihilators after localization

This module proves `Langlands.CommutativeAlgebra.Popescu.AnnihilatorStabilizationStatement.{u}`
as the theorem `Langlands.CommutativeAlgebra.Popescu.annihilatorStabilization`, for every
universe `u`.

The setting is as in the statement. `A : Type u` is a Noetherian commutative ring, and
`M : Type u` is a finitely generated `A`-module. `S` is a submonoid of `A`, and `π ∈ A`.
The hypothesis is: for every `m ∈ M`, if `(r π²) • m = 0` for some `r ∈ S`, then
`(r' π) • m = 0` for some `r' ∈ S`. The conclusion is that some `s ∈ S` satisfies
`(t s π)² • m = 0 → (t s π) • m = 0` for every `t ∈ S` and `m ∈ M`.

## Auxiliary lemma

`Langlands.CommutativeAlgebra.Popescu.exists_mem_submonoid_mul_smul_eq_zero_of_finset`: let
`A` be a commutative ring, `M` an `A`-module, `S` a submonoid of `A`, `x ∈ A` and `G` a finite
subset of `M`. Suppose each `g ∈ G` has some `r ∈ S` with `(r x) • g = 0`. Then a single
`s ∈ S` has `(s x) • g = 0` for every `g ∈ G`.

The proof is by induction on `G` (`Finset.induction_on`). For `G = ∅` take `s = 1`. For
`insert a G`, the induction hypothesis gives `s` for `G`, and the hypothesis on `a` gives `r`
with `(r x) • a = 0`. Then `r s ∈ S` works:
`(r s x) • a = s • (r x) • a = 0` and `(r s x) • g = r • (s x) • g = 0` for `g ∈ G`.

## Proof of the main theorem

1. **The submodule `K'`.** Let `K'` be the set of `m ∈ M` with `(r π²) • m = 0` for some
   `r ∈ S`. These are the elements whose image under `π²` vanishes in `S⁻¹M`, as in the source
   proof. `K'` is an `A`-submodule of `M`. It contains `0` (witness `1`). If `r` works for `a`
   and `r'` works for `b`, then `r r'` works for `a + b`. If `r` works for `m`, it also works
   for `c • m`, because scalars commute in a commutative ring.
2. **`K'` is finitely generated.** `M` is a Noetherian module: Mathlib's instance
   `isNoetherian_of_isNoetherianRing_of_finite` applies because `A` is Noetherian and `M` is
   finite. So `IsNoetherian.noetherian K'` gives a finite set `G` with `span A G = K'`.
3. **One `s` for all generators.** Each `g ∈ G` lies in `K'` (`Submodule.subset_span`). So the
   hypothesis gives `r ∈ S` with `(r π) • g = 0`. The auxiliary lemma with `x = π` gives one
   `s ∈ S` with `(s π) • g = 0` for every `g ∈ G`.
4. **`s π` kills `K'`.** The kernel of `LinearMap.lsmul A M (s π)`, multiplication by `s π`,
   is a submodule containing `G`. By `Submodule.span_le`, it contains `span A G = K'`.
5. **Conclusion.** Let `t ∈ S` and `m ∈ M` with `(t s π)² • m = 0`. Since
   `(t s)² π² = (t s π)²` and `(t s)² ∈ S`, `m` lies in `K'`. By step 4, `(s π) • m = 0`. Hence
   `(t s π) • m = t • (s π) • m = 0`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

The statement is Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in literature
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 10.1 (Ogoma, Tag 07FC, printed p. 24).
The source proof sets `K = Ker(π : M → M)` and `Q = K'/K`. It notes that `S⁻¹Q = 0` and `Q` is
finite, picks `s ∈ S` with `s Q = 0`, and says "Then s works."

The Lean proof follows the same route without forming the quotient `Q`. Steps 2–4 give
`s ∈ S` with `s K' ⊆ K`, which is the statement `s Q = 0`. Step 5 expands "Then s works" for
the multipliers `t s` with `t ∈ S`, as the statement's Markdown describes. The source states
the conclusion only for `t = sⁿ⁻¹`.

## Provenance

Worker 134 wrote this proof and its Markdown in Task 6525
(`3e8945af-2fbf-4708-9366-8d01bcb7effd`). The statement was published from Task 5698.
