# Density of conjugators onto ground-field maximal tori

Worker 1523. This module states one proposition,
`RationalMaximalTorusConjugateDensityStatement.{u}`. It is not proved here.

## Statement

Fix an infinite field `k : Type u` and a group scheme `G` over `Spec k` that is
smooth and affine, with connected underlying space. Let `j₀ : T₀ ⟶ G` be a
maximal torus (`IsMaximalTorus j₀`), let `K = AlgebraicClosure k`, and let
`G_K = (GroupScheme.baseChange (toAlgebraicClosure k)).obj G`.

Call a `K`-point `g : Over.mk (𝟙 (Spec K)) ⟶ G_K.X` *good* when there are a
commutative group scheme `T` over `Spec k` and a homomorphism `j : T ⟶ G` such
that

- `T` is a torus (`IsTorus T.toGrp`) and `j` is a closed subgroup
  (`IsClosedSubgroup j`), and
- the subgroup functors `SubgroupFunctor.range ((GroupScheme.baseChange
  (toAlgebraicClosure k)).map j₀ ≫ (G_K.innerIso g).hom)` and
  `SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)`
  of `G_K` are equal.

In words, conjugation by `g` carries `(T₀)_K` onto `T_K`: `g (T₀)_K g⁻¹ = T_K`.
The equality of ranges is an equality of subgroup functors, so it holds on every
test scheme over `K`, reduced or not. The statement asserts that the union of the
images `Set.range g.left` over all good `g` is dense in the underlying
topological space of `G_K`. Each such image is a single closed point, so the
assertion is that the good `K`-points are Zariski-dense in `G_K`.

The torus `T` is not required to be maximal. Its base change is the conjugate of
a maximal torus of `G_K`, but nothing in the statement depends on that.

## Source and derivation

The statement is derived from Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), proof of Proposition A.2.11, printed pp.477–478 (one-based
PDF pp.503–504), registered as `conrad-gabber-prasad-2015-pseudo-reductive`. The
source is about a smooth connected affine group `G` over a field `k`, with a
maximal `k`-torus `T₀`. It introduces the variety of maximal tori
`Tor_G = G/N_G(T₀)`. It notes that for every field `L/k`, the fibres of the
universal torus over the points `x ∈ Tor_G(L)` run, without repetition, through
the maximal `L`-tori of `G_L`. It then quotes the Chevalley–Grothendieck theorem
(SGA3 XIV, Theorem 6.1; Borel–Springer 7.1(i), 7.3, 7.9): `Tor_G` is unirational
over `k`, and "in particular, `Tor_G(k)` is Zariski-dense in `Tor_G` when `k` is
infinite."

The source states this density on `Tor_G` itself. The statement here moves it to
`G_K`, which avoids constructing `Tor_G` in Lean. The derivation is standard and
not spelled out in the source:

1. Let `π : G → Tor_G` be the quotient map. On `L`-points it sends `g` to the
   torus `g T₀ g⁻¹`.
2. `Tor_G(k)` is still Zariski-dense in the base change `(Tor_G)_K`. A regular
   function `Σ cᵢ ⊗ fᵢ` vanishing on `Tor_G(k)`, with the `cᵢ ∈ K` linearly
   independent over `k`, forces every `fᵢ` to vanish on `Tor_G(k)`, hence on
   `Tor_G`.
3. The quotient map `π_K` is faithfully flat of finite type, hence open. A
   nonempty open `U ⊆ G_K` therefore has nonempty open image, which contains a
   point `x ∈ Tor_G(k)`. The fibre of `π_K` over `x` meets `U` in a nonempty
   open subset of a `K`-variety, so `U` contains a `K`-point `g` with
   `π(g) = x`.
4. If `T` is the maximal `k`-torus corresponding to `x`, then
   `g (T₀)_K g⁻¹ = T_K`, so `g` is good.

So the good `K`-points meet every nonempty open subset of `G_K`. The Lean set of
good points may be larger than the set obtained this way, because it allows any
closed `k`-torus `T`. A larger set is still dense, so the source's density
implies the Lean statement.

The hypotheses (smooth, affine, connected over a field) are those of
Proposition A.2.11. `Infinite k` is the source's condition for density.
`IsMaximalTorus j₀` makes `T₀` a maximal `k`-torus, as in the source's
construction of `Tor_G`.

## Intended use

Combined with `MaximalTorusBaseChangeStatement` (maximality survives field
extension) and `MaximalTorusConjugacyStatement` (maximal tori are conjugate over
an algebraically closed field), this density gives the infinite-field case of the
compatibility of the closed torus envelope with algebraic closure,
`TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement`. This follows the
source's own argument on printed p.478. That deduction is a separate reduction
module and is not part of this statement.
