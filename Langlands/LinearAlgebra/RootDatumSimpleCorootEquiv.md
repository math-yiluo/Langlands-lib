# Root data with spanning coroots are determined by the Cartan pairings of a base

Helper module for the proof of
`Langlands.LinearAlgebra.CorootSpanCartanEquivStatement`
(module `Langlands.LinearAlgebra.CorootSpanCartanEquivStatement`). Author: Worker 61
(Task 5703). It uses only Mathlib (`Mathlib.LinearAlgebra.RootSystem.Base` and
`Mathlib.LinearAlgebra.RootSystem.Hom`). All declarations are in namespace
`Langlands.RootDatumSimpleCorootEquiv`.

Throughout, `P : RootDatum ι X Y` and `Q : RootDatum ι₂ X₂ Y₂` are root data over `ℤ`.
Here `X`, `X₂` are the weight lattices and `Y`, `Y₂` the coweight lattices.

## Declarations

- `exists_root_coroot_image`: let `P` be finite and reduced, with a base `b`. Let
  `f : X →ₗ[ℤ] X₂` and `g : Y →ₗ[ℤ] Y₂` be adjoint for the two pairings, i.e.
  `Q.toLinearMap (f x) (g y) = P.toLinearMap x y`. Suppose that for every simple index
  `i ∈ b.support` there is `k` with `f (P.root i) = Q.root k` and
  `g (P.coroot i) = Q.coroot k`. Then the same holds for every index `i`.
  The proof is Mathlib's induction principle `RootPairing.Base.induction_reflect`.
  Every root is reached from a simple root by reflections in simple roots, up to sign.
  - For the sign step, if `(f, g)` carries the pair at `i` to the pair at `k`, it
    carries the pair at `P.reflectionPerm i i` (the negative root) to the pair at
    `Q.reflectionPerm k k`.
  - For the reflection step, take `i ↦ k` and a simple `j ↦ l`. Adjointness gives
    `P.pairing i j = Q.pairing k l` and `P.pairing j i = Q.pairing l k`. The
    reflection formulas `reflection_apply_root` and `coreflection_apply_coroot` then
    show that the pair at `P.reflectionPerm j i` goes to the pair at
    `Q.reflectionPerm l k`.
- `simpleCorootBasis b hP : Basis b.support ℤ Y`: if `P.corootSpan ℤ = ⊤`, the simple
  coroots form a `ℤ`-basis of `Y`. Linear independence is
  `RootPairing.Base.linearIndepOn_coroot`. Spanning combines
  `RootPairing.Base.span_int_coroot_support` (simple coroots span the same `ℤ`-module
  as all coroots) with `hP`. `simpleCorootBasis_apply` evaluates the basis.
- `eq_of_pairing_simpleCoroot`: under `P.corootSpan ℤ = ⊤`, two weights with the same
  pairings against all simple coroots are equal. The proof uses injectivity of the
  perfect pairing `P.toPerfPair` and `Basis.ext` for `simpleCorootBasis`.
- Section `Equiv`, with bases `b`, `c`, hypotheses `hP : P.corootSpan ℤ = ⊤`,
  `hQ : Q.corootSpan ℤ = ⊤`, and a bijection `e : b.support ≃ c.support`:
  - `corootEquiv : Y ≃ₗ[ℤ] Y₂` is `Basis.equiv` of the two simple coroot bases along
    `e`. Lemmas: `corootEquiv_coroot` (simple coroot `i` goes to simple coroot `e i`)
    and `corootEquiv_symm_coroot`.
  - `rootEquiv : X ≃ₗ[ℤ] X₂` is
    `P.toPerfPair.trans ((corootEquiv ..).symm.dualMap.trans Q.toPerfPair.symm)`, the
    transpose of the inverse of `corootEquiv`. `toLinearMap_rootEquiv` and
    `toLinearMap_rootEquiv_corootEquiv` state adjointness:
    `Q.toLinearMap (rootEquiv x) (corootEquiv y) = P.toLinearMap x y`.
  - `rootEquiv_root`: if `e` preserves the simple pairings
    (`he : ∀ i j, Q.pairing (e i) (e j) = P.pairing i j`), then `rootEquiv` carries
    the simple root `i` to the simple root `e i`. By `eq_of_pairing_simpleCoroot` for
    `Q`, it suffices to compare pairings with the simple coroots `j` of `c`. Both sides
    give `P.pairing i (e.symm j)`.
  - `exists_equiv_indexEquiv`: for finite reduced `P`, `Q`, there is
    `f : RootPairing.Equiv P Q` with `f.indexEquiv i = e i` for all `i : b.support`.
    `exists_root_coroot_image` applied to `(rootEquiv, corootEquiv, b)` gives an index
    map `σ : ι → ι₂`. Applied to the inverses `(rootEquiv.symm, corootEquiv.symm, c)`,
    whose simple hypothesis follows from `rootEquiv_root`, it gives `τ : ι₂ → ι`.
    Injectivity of the root embeddings shows that `σ` and `τ` are inverse. The
    equivalence has weight map `rootEquiv`, coweight map `corootEquiv.symm`, and index
    map `σ`. The transpose condition is adjointness. `σ` agrees with `e` on the base
    because both are detected by `rootEquiv_root` and injectivity of `Q.root`.

## Provenance

This is a standard argument: a based root datum whose coroots span the coweight lattice
is determined by its Cartan matrix. The simple coroots form a basis, and every root is
obtained from a simple root by simple reflections. The module is derived for this
project and does not follow a particular printed proof.
