# Local-global principle for norms of regular elliptic elements of `GL_n` (statement)

The module `Langlands.TraceFormula.GeneralLinearLocalGlobalNormStatement` defines one
proposition and proves nothing:

- `Langlands.TraceFormula.GeneralLinearLocalGlobalNormStatement.{u} : Prop`.

Let `L/K` be a cyclic extension of number fields of degree `l` whose Galois group is generated
by `σ`. The proposition says that an element `γ ∈ GL_n(K)` with separable irreducible
characteristic polynomial is a norm from `GL_n(L)` if it is a norm from `GL_n(K_i ⊗_K L)` at
every place `i` of `K`, the infinite places included. This is the regular elliptic case of
Arthur–Clozel, Chapter 1, Lemma 1.2; see "Sources and derivation" below.

## Notation from the Library

The module imports `Langlands.TraceFormula.GeneralLinearBaseChangeLocal` and defines nothing
besides the proposition.

- `K`, `L : Type u` are number fields with `[Algebra K L] [FiniteDimensional K L]`,
  `σ : L ≃ₐ[K] L` and `l : ℕ`. The hypothesis `IsCyclicAlgebra σ l`
  (`Langlands.BaseChange.IsCyclicAlgebra`, module `Langlands.BaseChange.Norm`) says that `L` is
  a finite reduced `K`-algebra of dimension `l`, that `σ` has order `l` and that the elements of
  `L` fixed by `σ` are those of `K`. For the field `L` this means that `L/K` is cyclic of degree
  `l` and that `σ` generates its Galois group.
- `GeneralLinear n R` (`Langlands.GeneralLinear`, module `Langlands.Group.GL.Basic`) is
  `Matrix.GeneralLinearGroup (Fin n) R`, the group `GL_n(R)` of units of the matrix ring.
- `IsRegularElliptic γ` (`Langlands.JacquetLanglands.IsRegularElliptic`) says that the
  characteristic polynomial of `γ` is separable and irreducible over `K`.
- For `F` a commutative ring, `E` a commutative `F`-algebra and `τ : E ≃ₐ[F] E`, the module
  `Langlands.BaseChange.Norm` defines the norm `cyclicNorm τ l δ = δ δ^τ ⋯ δ^{τ^{l-1}}` of
  `δ ∈ GL_n(E)`, where `τ` acts on each entry and the product is taken in this order. The
  predicate `IsNorm τ l γ` for `γ ∈ GL_n(F)` means: there are `δ, g ∈ GL_n(E)` with
  `g⁻¹ · cyclicNorm τ l δ · g = baseChange F E n γ`, the image of `γ` under `algebraMap F E`
  (`IsNorm` is `∃ δ, IsNormAssociated τ l δ γ`). So `γ` is conjugate in `GL_n(E)` to a norm.
- `Place K = InfinitePlace K ⊕ FinitePlace K` (`Langlands.Global.Place`) is the set of all
  places of `K`. The completion at a place `i` is `K_i = placeCompletion K i`, the completion
  `w.Completion` at an infinite place `w` and the adic completion at a finite place.
- `LocalBaseChangeAlgebra K L i` is `E_i = K_i ⊗_K L`, and
  `localGalois K L σ i : E_i ≃ₐ[K_i] E_i` is `σ_i = id ⊗ σ`. In general `E_i` is not a field: it
  is isomorphic to the product of the completions of `L` at the places above `i`, and `σ_i`
  permutes the factors. By `isCyclicAlgebra_localGalois`, `E_i` is a cyclic `K_i`-algebra of
  degree `l` with automorphism `σ_i`.
- The module opens the scoped instance `Langlands.TraceFormula.PlaceCompletion.field`, the field
  structure `placeCompletionField K i` on `K_i`. Nothing in the statement requires a field
  structure on `K_i`: elaborated without this instance, the same text gives a definitionally
  equal proposition (checked by `Iff.rfl` in the pinned environment). `K_i` carries the ring
  structure of the commutative `K`-algebra `placeCompletion K i`.

## Statement

For all number fields `K`, `L : Type u` with `[Algebra K L] [FiniteDimensional K L]`, all
`σ : L ≃ₐ[K] L` and `l : ℕ` with `IsCyclicAlgebra σ l`, all `n : ℕ` and all
`γ : GeneralLinear n K` with `IsRegularElliptic γ`: if, for every place `i : Place K`,

`IsNorm (localGalois K L σ i) l (Matrix.GeneralLinearGroup.map (algebraMap K (placeCompletion K i)) γ)`,

then `IsNorm σ l γ`. Spelled out: there are `δ, g ∈ GL_n(L)` with
`g⁻¹ · (δ δ^σ ⋯ δ^{σ^{l-1}}) · g = γ` in `GL_n(L)`.

The hypothesis is the condition at every place, archimedean and nonarchimedean, split, inert or
ramified in `L`. Since a characteristic polynomial of degree `0` is the unit `1` and so not
irreducible, `IsRegularElliptic γ` forces `n ≥ 1`.

## Sources and derivation

J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989 (source ID
`arthur-clozel-1989-base-change`; PDF page = printed page + 14 in Chapter 1).

- Chapter 1, §1 (printed p. 3) works with a cyclic extension `E/F` of degree `l` of fields of
  characteristic `0` with generator `σ`, `G = GL(n)`, and the norm `Nx = x x^σ ⋯ x^{σ^{l-1}}` of
  `x ∈ G(E)`. By Lemma 1.1 (printed p. 3), `Nx` is conjugate in `G(E)` to an element of `G(F)`,
  unique up to conjugation in `G(F)`, and `Nx` also denotes this conjugacy class of `G(F)`. So
  "`u = Nx`" for `u ∈ G(F)` says that `u` is conjugate in `G(E)` to the matrix `Nx`. This is the
  Library's `IsNorm σ l u`.
- On printed p. 4, for a global field `F`, the norm is extended to the places `v` of `F` that are
  not inert in `E`, with `E_v = E ⊗_F F_v` and the Galois group `Σ` of `E/F` acting on it. At a
  split place
  `E_v = F_v ⊕ ⋯ ⊕ F_v` with `Σ` permuting the factors cyclically. This is the Library's
  `cyclicNorm (localGalois K L σ i) l` on `GL_n(E_i)`.
- Lemma 1.2 (printed p. 4): for a global field `F` and `u ∈ G(F)`, `u = Nx` has a solution in
  `G(E)` if and only if it has a solution in `G(E_v)` for every place `v` of `F`.
- Its proof first treats semisimple `u` (printed pp. 4–6). On printed p. 6, `u` is a block
  diagonal matrix of `k` copies of `u₁`, where `u₁` generates a field `F₁` of degree `m` over
  `F`. From `u = N x_v` and `u = u^σ = x_v⁻¹ u x_v`, the element `x_v` commutes with `u`. So it
  lies in the centralizer `M_k(F₁ ⊗ E_v)`, and the problem becomes the case already treated (on
  printed p. 5, for `u` scalar) for `M_k(F₁)` and the cyclic étale `F₁`-algebra `E ⊗_F F₁`. For
  `k = 1` that case is the statement "in `F₁^×`, an element which is a local norm everywhere is
  a global norm" (printed p. 5), the Hasse norm theorem.

The statement here is the case `k = 1`, `m = n` of the semisimple part, that is, `u = γ` with
separable irreducible characteristic polynomial, over a number field (a global field of
characteristic `0`, the setting of Arthur–Clozel's Chapter 1).

Derived content: the statement is Lemma 1.2 restricted to these `u`, in the "if" direction,
written with the Library's `IsNorm`, `localGalois` and `placeCompletion`. Arthur–Clozel use this
lemma in the comparison of the trace formulas (Chapter 1, §4, printed p. 44: "an element of
`G(k)` is a global norm if and only if it is a local norm everywhere (Lemma 1.2)"). The Markdown
of `Langlands.TraceFormula.GeneralLinearBaseChangeGlobalMatchingStatement` uses it in the same
way, in step 7 ("Vanishing off norms") of its explanation.

### Why the statement is true (not formalized)

This follows Arthur–Clozel's argument for `k = 1`. Write `K₁ = K[γ] ⊂ M_n(K)`. Because the
characteristic polynomial `χ_γ` is irreducible, it is the minimal polynomial of `γ`, and `K₁`
is a field of degree `n` over `K`.

1. Normalizing. If `g⁻¹ N(δ) g = γ`, then `δ' = g⁻¹ δ g^σ` has
   `N(δ') = g⁻¹ N(δ) g^{σ^l} = γ`, since `σ^l = 1` (`cyclicNorm_twistedConj`,
   `IsCyclicAlgebra.pow_eq_one`). The identity `N(δ')^σ = δ'⁻¹ N(δ') δ'^{σ^l}`
   (`entrywiseAut_cyclicNorm`) and `γ^σ = γ` give `γ = δ'⁻¹ γ δ'`. So `δ'` commutes with `γ`.
   The same argument works over `E_i` with `σ_i`, which also satisfies `σ_i^l = 1`.
2. Centralizers. Since `χ_γ` is separable, its centralizer in `M_n(R)`, for `R = L` or
   `R = E_i` (finite products of fields containing `K`), is `R[γ] ≅ R ⊗_K K₁`. On it the
   entrywise action of `σ` (or `σ_i`) is `σ ⊗ id`. Hence `γ` is a norm from `GL_n(L)` if and
   only if `γ ∈ K₁` is a norm from the cyclic étale `K₁`-algebra `L ⊗_K K₁`. Likewise, `γ` is a
   norm from `GL_n(E_i)` if and only if, at every place `w` of `K₁` above `i`, it is a norm from
   `L ⊗_K K_{1,w}`, since `E_i ⊗_{K_i} (K_i ⊗_K K₁) ≅ ∏_{w | i} L ⊗_K K_{1,w}`.
3. Hasse norm theorem. For some `d` dividing `l`, the `K₁`-algebra `L ⊗_K K₁` is a product of
   `d` copies of a cyclic field extension `L'/K₁` of degree `l/d`, permuted transitively by
   `σ ⊗ id`, and its norms to `K₁` are the norms from `L'`. Likewise, at each place `w` of
   `K₁`, the norms from `L ⊗_K K_{1,w}` to `K_{1,w}` are the norms from `L'_{w'}` for a place
   `w'` of `L'` above `w`. So the hypothesis says that `γ ∈ K₁^×` is a local norm from `L'` at
   every place of `K₁`. The Hasse norm theorem for the cyclic extension `L'/K₁` then makes `γ`
   a norm from `L'^×`, and by step 2 `γ` is a norm from `GL_n(L)`.

## Relation to other results of the Library

- `Langlands.TraceFormula.localize_normAssociated` (module
  `Langlands.TraceFormula.RationalLocalGeneralLinear`) proves the converse direction for an
  explicit `δ`: if `IsNormAssociated σ l δ γ`, then the image of `δ` in `GL_n(E_i)` is associated
  with the image of `γ` in `GL_n(K_i)` at every place `i`. So a global norm is a local norm at
  every place. `Langlands.TraceFormula.rationalLocalNormAssociation` gives the same localization
  for rational points of `Res_{L/K} GL_n` and `GL_n`.
- `Langlands.ClassFieldTheory.Global.cyclicHasseNorm : CyclicHasseNormStatement` (idelic form)
  and `Langlands.Global.cyclicNumberFieldHasseNorm : CyclicNumberFieldHasseNormStatement`
  (module `Langlands.Global.Arithmetic.CyclicHasseNorm`, with local norm hypotheses at every
  pair of places) prove the Hasse norm theorem for cyclic Galois extensions of number fields,
  the arithmetic input of step 3.
- `Langlands.BaseChange.cyclicNormLemma : CyclicNormLemmaStatement` proves the norm lemma of
  Henniart–Lemaire (2011), I.2.2, Lemme, for a cyclic `F`-algebra `E` over a field `F`: every
  `δ ∈ GL_n(E)` is associated with some `γ ∈ GL_n(F)`, unique up to conjugation in `GL_n(F)`,
  and `δ` is determined up to σ-conjugation by the conjugacy class of `N(δ)` (the analogue of
  Arthur–Clozel, Lemma 1.1).

## What this module does not claim

It does not prove the statement. It does not state Lemma 1.2 for elements that are not regular
elliptic (non-semisimple elements, or semisimple elements whose characteristic polynomial is
reducible or inseparable), and it does not state the "only if" direction. It does not say that
the hypothesis at fewer places would suffice. It says nothing about the σ-conjugacy class of `δ`
(Arthur–Clozel, Lemma 1.1(ii)) or about global fields of positive characteristic.
