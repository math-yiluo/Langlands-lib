# Proof: stalk dimension at a quasi-finite point

`Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension.{u}` proves exactly
the published proposition
`Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionStatement.{u}`, for an
arbitrary universe `u`:

```lean
∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
  LocallyOfFiniteType f → ∀ (x : X), f.QuasiFiniteAt x →
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (Y.presheaf.stalk (f x))
```

For a locally finite type morphism of arbitrary schemes that is quasi-finite at
`x`, the Krull dimension of the stalk `𝒪_{X,x}` is at most that of
`𝒪_{Y,f(x)}`, in the order of `WithBot ℕ∞`. The schemes may be non-Noetherian.
The module imports only the statement module, so its dependencies are pinned
Mathlib and the published statement pair.

## Algebraic lemma

`Langlands.AlgebraicGeometry.ringKrullDim_le_of_quasiFinite` states: for
commutative rings `R` and `S` in arbitrary universes and an `R`-algebra `S` with
`[Algebra.QuasiFinite R S]`,

```lean
ringKrullDim S ≤ ringKrullDim R
```

There is no finite-type, Noetherian or locality hypothesis. Mathlib's
`Algebra.QuasiFinite R S` says that for every prime `P` of `R` the fibre ring
`P.Fiber S = κ(P) ⊗[R] S` is a finite-dimensional `κ(P)`-vector space.

The Lean proof applies the order-theoretic bound
`Order.krullDim_le_of_krullDim_preimage_le'` with `m = 0`. The map is
`PrimeSpectrum.comap (algebraMap R S) : PrimeSpectrum S → PrimeSpectrum R`, the
contraction of primes. It is monotone by `Ideal.comap_mono`. The bound then
reads `krullDim (PrimeSpectrum S) ≤ (0 + 1) * krullDim (PrimeSpectrum R) + 0`
once each preimage of a point has Krull dimension at most `0`.

For a point `p` of `PrimeSpectrum R`, Mathlib's order isomorphism
`PrimeSpectrum.preimageOrderIsoFiber R S p` identifies the preimage of `{p}`
with `PrimeSpectrum (p.asIdeal.Fiber S)`. `Order.krullDim_eq_of_orderIso`
therefore turns the preimage's dimension into `ringKrullDim (p.asIdeal.Fiber S)`.
By `Ring.krullDimLE_iff`, the bound `≤ 0` is the class
`Ring.KrullDimLE 0 (p.asIdeal.Fiber S)`. Instance search finds it. The
quasi-finiteness instance makes the fibre Artinian
(`Algebra.QuasiFinite`'s `IsArtinianRing (P.Fiber S)` instance), and Artinian
rings have Krull dimension at most zero. Finally `simpa [ringKrullDim]`
simplifies `(0 + 1) * d + 0` to `d` and folds the two `Order.krullDim` terms
back into `ringKrullDim`.

In words: two primes `𝔮 ⊆ 𝔮'` of `S` with the same contraction lie in one fibre,
whose spectrum is that of a zero-dimensional ring, so `𝔮 = 𝔮'`. Contraction
therefore sends every strict chain of primes of `S` to a strict chain of primes
of `R` of the same length.

## The scheme theorem

The main theorem introduces `X`, `Y`, `f`, the finite-type hypothesis, `x` and
`hx : f.QuasiFiniteAt x`. By its Mathlib definition,
`Scheme.Hom.QuasiFiniteAt f x` is `(f.stalkMap x).hom.QuasiFinite`, where
`f.stalkMap x : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x` is the stalk map.
`RingHom.QuasiFinite g` is by definition `Algebra.QuasiFinite` for the algebra
structure `g.toAlgebra`. The proof installs
`(f.stalkMap x).hom.toAlgebra` as the algebra structure of the source stalk over
the target stalk. It then reads `hx` definitionally as
`Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)`. The
algebraic lemma, with `R = 𝒪_{Y,f(x)}` and `S = 𝒪_{X,x}`, gives the stated
inequality directly.

The hypothesis `LocallyOfFiniteType f` is part of the published proposition and
the theorem's type keeps it. The proof does not use it. The proof also uses no
affine neighbourhoods and no stalk localization. Mathlib's pointwise predicate
is quasi-finiteness of the whole stalk map, so it controls every fibre of
`𝒪_{Y,f(x)} → 𝒪_{X,x}`, including those over primes other than the maximal
ideal. That is all the chain argument needs.

## Relation to the cited source

The statement's source is the Stacks Project, Lemma 10.125.4
([Tag 00QF](https://stacks.math.columbia.edu/tag/00QF)), registered snapshot
`stacks-quasifinite-local-dimension-2026-10-29`. There `R → S` is of finite
type and "quasi-finite at `𝔮`" restricts only the fibre over `𝔭`. The source
proof handles the general case with Zariski's Main Theorem 10.123.12 and the
integral closure of `R_𝔭` in `S_𝔭`. The Lean proof does not follow that route. It
starts from Mathlib's pointwise hypothesis, which constrains every fibre of the
stalk map, as described above. So it needs neither Zariski's Main Theorem nor
the finite-type hypothesis. The statement Markdown's affine-neighbourhood plan,
via `Scheme.Hom.QuasiFiniteAt.quasiFiniteAt` and
`IsAffineOpen.isLocalization_stalk`, was a navigation hint and is not used.

## Dependencies

All dependencies are pinned Mathlib declarations:

- `Order.krullDim_le_of_krullDim_preimage_le'` and
  `Order.krullDim_eq_of_orderIso` (order-theoretic Krull dimension);
- `PrimeSpectrum.comap`, `Ideal.comap_mono` and
  `PrimeSpectrum.preimageOrderIsoFiber` (primes in a fibre);
- `Ring.krullDimLE_iff`, the `IsArtinianRing` instance for fibres of a
  quasi-finite algebra, and the `Ring.KrullDimLE 0` instance for Artinian rings;
- `Scheme.Hom.QuasiFiniteAt`, `Scheme.Hom.stalkMap`, `RingHom.QuasiFinite` and
  `RingHom.toAlgebra`.

The proof uses no project result other than the published statement it
proves. It does not depend on any of the consumer proofs that will use this
theorem. It introduces no axioms. A kernel inspection of the main theorem
reports only `propext`, `Classical.choice` and `Quot.sound`.
