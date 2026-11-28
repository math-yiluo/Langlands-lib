# The local–global principle for embeddings of maximal subfields: proof

Module: `Langlands.Algebra.CentralSimple.NumberFieldLocalGlobalEmbeddingProof`.

`Langlands.CentralSimple.numberFieldLocalGlobalEmbedding` proves
`Langlands.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement.{u}` in every universe `u`,
with exactly the hypotheses of the statement: `F` a number field, `E/F` finite, `B` a
finite-dimensional central simple `E`-algebra with `[B : E] = [P : E]²`, `P/E` a finite field
extension, and at every place `v` of `F` an injective `F_v`-algebra homomorphism
`F_v ⊗[F] P → F_v ⊗[F] B` that is the identity on `E`. The conclusion is an `E`-algebra
homomorphism `P → B`. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Notation

The number fields have characteristic zero, so `E/F` and `P/E` are separable.
`Field.powerBasisOfFiniteOfSeparable E P` gives a generator `θ` of `P/E`; its minimal polynomial
`f` is separable of degree `n = [P : E]`, and `[B : E] = n²` makes `n` the reduced degree of `B`.
A primitive element `α` of `E/F` (`LocalGlobalEmbedding.prim`) has minimal polynomial `g`.

## Local splitting

`LocalGlobalEmbedding.isSplit_of_local` is the local step. Let `K` be a field over `F` with an
injective `K`-algebra map `φ : K ⊗[F] P → K ⊗[F] B` that is the identity on `E`, and let `M` be a
field over `K` and over `E` whose two `F`-structures agree and that contains a root `r` of `f`.
Then `M ⊗[E] B` is split. The proof has three parts.

1. *Scalar extension* (`exists_baseChange_embedding`). The algebra isomorphisms
   `M ⊗[K] (K ⊗[F] Y) ≅ M ⊗[F] Y` for `Y = P, B` carry `id_M ⊗ φ` to an `M`-algebra map
   `φ_M : M ⊗[F] P → M ⊗[F] B`. It is injective because `M` is flat over the field `K`
   (`Module.Flat.lTensor_preserves_injective_linearMap`), and it is still the identity on `E`.

2. *Passage from `⊗[F]` to `⊗[E]`* (sections `Descend`, `Idempotent`, `Section`). Over `M` the
   polynomial `g` has the root `α_M`, and `g = (X - α_M) h` (`cofactor`) with `h(α_M) ≠ 0` by
   separability (`cofactor_eval_ne_zero`). The element `ε = h(1 ⊗ α) / h(α_M)` of
   `M ⊗[F] E` (`idem`) satisfies `ε (1 ⊗ α - α_M ⊗ 1) = 0` (`idem_mul_sub`), hence
   `ε (1 ⊗ e) = ε (e ⊗ 1)` for all `e ∈ E` (`idem_mul_tmul`), because every `e` is a polynomial in
   `α` and `1 ⊗ α - α_M ⊗ 1` divides the corresponding difference of polynomial values in the
   commutative ring `M ⊗[F] E`. Every `M`-algebra map that sends `1 ⊗ α` to `α_M` sends `ε` to `1`
   (`idem_map_eq_one`). For `Y = P, B`, `descend` is the natural map
   `M ⊗[F] Y → M ⊗[E] Y`, and the image `ε_Y` of `ε` in `M ⊗[F] Y` (`incl`) makes
   `l ⊗ y ↦ ε_Y (l ⊗ y)` a well-defined additive map `cut : M ⊗[E] Y → M ⊗[F] Y` with
   `cut (descend z) = ε_Y z` (`cut_descend`). Thus `ε_Y` kills the kernel of `descend`.

3. *The reduced characteristic polynomial* (`isSplit_of_embedding`). Put
   `a = descend (φ_M (1 ⊗ θ)) ∈ M ⊗[E] B`. Since `φ_M` is the identity on `E`, it maps `ε_P` to
   `ε_B`. If `q ∈ M[X]` and `q(a) = 0`, then `ε_B φ_M(q(1 ⊗ θ)) = cut(q(a)) = 0`, so
   `ε_P q(1 ⊗ θ) = 0` by injectivity, and applying `descend` (which sends `ε_P` to `1`) gives
   `q(1 ⊗ θ) = 0` in `M ⊗[E] P`. The elements `1 ⊗ θ^i`, `i < n`, form an `M`-basis of
   `M ⊗[E] P` (`tensorPowerBasis`), so the minimal polynomial of `a` over `M` has degree at least
   `n`. The composite `P → M ⊗[F] P → M ⊗[F] B → M ⊗[E] B` is an `E`-algebra map sending `θ` to
   `a`, so `f(a) = 0`. The reduced characteristic polynomial of `a` is monic of degree
   `n` and vanishes at `a` (`aeval_reducedCharpoly`), and so is the image `f_M` of `f`. Both are
   divisible by the minimal polynomial of `a`, whose degree is at least `n`, so both are equal to
   it. Hence the reduced characteristic polynomial of
   `a` is the separable polynomial `f_M`, and `r` is a simple root of it. Then
   `isSplit_of_simple_root` (module `Langlands.Algebra.ReducedCharpolyRootSplitting`) gives the
   splitting of `M ⊗[E] B`.

## Global step

`LocalGlobalEmbedding.isSplit_adjoinRoot` shows that for every irreducible factor `p` of
`f`, the number field `L = E[X]/(p)` splits `B`. It applies
`Langlands.Brauer.numberFieldBrauerSplitting` to `L ⊗[E] B` over `L`.

- At a finite place `w` of `L` it takes the place
  `v = Langlands.ClassFieldTheory.Global.placeBelow F w` of `F`. The completion map
  `F_v → L_w` (`Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap`) makes `L_w`
  a field over `F_v`.
- At an infinite place `w` it takes `v = w.comap (algebraMap F L)` and Mathlib's completion map
  `NumberField.LiesOver.completionMap`.

In both cases `L_w` is an `E`-algebra through `L`, and the image of the root of `p` is a root of
`f`. The two `F`-structures agree (`completionMap_coe`). The local hypothesis at the place `v` of
`F` and `isSplit_of_local` with `K = F_v`, `M = L_w` give the splitting of `L_w ⊗[E] B`.
`Langlands.Brauer.baseChangeTowerEquiv` identifies this algebra with `L_w ⊗[L] (L ⊗[E] B)`.

Finally `exists_reducedCharpoly_eq_of_split_factors` (module
`Langlands.Algebra.ReducedCharpolyFromSplitFactors`) gives `b ∈ B` with reduced characteristic
polynomial `f`. By reduced Cayley–Hamilton `f(b) = 0`, and `PowerBasis.lift` gives the
`E`-algebra homomorphism `P → B` with `θ ↦ b`.

## Sources

- G. Prasad and A. S. Rapinchuk, *Local-global principles for embedding of fields with
  involution into simple algebras with involution*, Comment. Math. Helv. 85 (2010), arXiv
  0806.0596v5 (source `prasad-rapinchuk-2010-embedding-fields-involution`): Propositions 2.6
  and 2.7, p. 9, and the first paragraph of the proof of Theorem 4.1, p. 13. The source
  derives Proposition 2.7 from the factor-field criterion of Proposition 2.6 and the injectivity
  of `Br(L) → ⊕_w Br(L_w)`, and passes from places of the subfield to places of the centre by
  decomposing `F_v ⊗[F] E` into completions. The Lean proof makes the passage with the idempotent
  `ε` instead of that decomposition. It proves local splitting by the reduced characteristic
  polynomial of a single element instead of Proposition 2.6, and uses the splitting form of
  Brauer–Hasse–Noether over each factor field.
- Martin Kneser, *Lectures on Galois Cohomology of Classical Groups*, TIFR Lectures on
  Mathematics 47 (1969), §5.4, Lemma b, printed p. 68 (source
  `kneser-1969-galois-cohomology-classical-groups`): a monic separable polynomial of the reduced
  degree is a reduced characteristic polynomial if and only if each of its factor fields splits
  the algebra. The proof uses both directions. The local step uses the splitting direction in
  the form of `isSplit_of_simple_root`: a simple root of the reduced characteristic polynomial in
  the ground field splits the algebra. The global step uses the converse,
  `exists_reducedCharpoly_eq_of_split_factors`, for the monic minimal polynomial `f`.
