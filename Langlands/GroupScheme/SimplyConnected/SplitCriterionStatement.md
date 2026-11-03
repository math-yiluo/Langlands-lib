# Coroot generation of the cocharacter lattice implies simple connectedness

Author: Worker 1414.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.SplitCorootSpanSimplyConnectedStatement`. The Lean
file only defines the proposition. It contains no proof of it, and it adds no
other definitions, theorems or axioms.

This is the sufficiency half of the coroot criterion for simple connectedness
of split semisimple groups. The converse ("simply connected implies the
coroots span") is not stated here.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`. The field may be imperfect, of positive
  characteristic, and need not be separably closed;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of k))` and a proof
  `hG : IsSemisimple G`. This published predicate from
  [`Reductive.Semisimple`](../Reductive/Semisimple.md) says that `G` is
  connected reductive and has finite centre;
- a commutative group scheme `T` with `IsSplitTorus T.toGrp`, that is, `T` is
  isomorphic to the split torus `𝔾_m^I` for a finite index type `I`
  ([`Torus.Split`](../Torus/Split.md));
- a homomorphism `i : T.toGrp ⟶ G` with `IsMaximalTorus i`
  ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `i` is a closed
  subgroup, and `i` factors through no strictly larger closed torus of `G`;
- a root index type `J : Type u` and a Mathlib integral root datum
  `P : RootDatum J (characterLattice T) (cocharacterLattice T)` on the actual
  lattices `X^*(T) = Hom(T, 𝔾_m)` and `X_*(T) = Hom(𝔾_m, T)` of `T`, with
  `IsRootDatumOf i P`. This published predicate from
  [`Reductive.RootDatum`](../Reductive/RootDatum.md) says that the pairing
  of `P` is the actual `latticePairing T`, that the range of `P.root` is the
  set `roots i` of nonzero characters with a nonzero weight space in the
  adjoint representation, and that each reflection of `P` is induced by a
  `k`-point of `G` normalizing `i`.

The predicate `IsRootDatumOf` requires `IsAffineHom G.X.hom`. The statement
supplies it as `hG.isConnectedReductive.isAffineHom` by `haveI`, so no extra
instance argument is introduced.

The only hypothesis on the root datum is

- `P.corootSpan ℤ = ⊤`: the `ℤ`-span of the coroots of `P` is the whole
  cocharacter lattice `X_*(T)`. Mathlib's `RootPairing.corootSpan` is the
  span of `Set.range P.coroot`.

## Conclusion

`IsSimplyConnected G`, the published predicate from
[`SimplyConnected.Basic`](Basic.md): `G` is semisimple, and every central
isogeny `f : H ⟶ G` from a semisimple group `H` over `k` is an isomorphism.

## Choices in the formulation

**A supplied root datum.** The statement quantifies over every root datum `P`
of `i` rather than asserting that one exists. The existence of the root
datum of a split maximal torus is the separate Library statement
`RootDatumExistenceStatement` in
[`Reductive.RootDatumStatement`](../Reductive/RootDatumStatement.md), which is
not proved. Quantifying over `P` keeps this criterion independent of it.

**No finiteness or reducedness of `J`.** No `[Finite J]` instance and no
reducedness hypothesis is assumed, so the statement covers more instances than
a version with them. Mathematically nothing is lost: `P.root` is an
embedding of `J` with range `roots i`, and the roots of a reductive group
form a finite reduced root system. Lean does not use these facts here.

**The torus must be split.** Without `IsSplitTorus T.toGrp` the statement
would be false. Take `k = ℝ`, `G = PGL₂`, and `T` an anisotropic maximal
torus, the image of `SO(2)`. Then `X^*(T) = Hom(T, 𝔾_m) = 0` over `ℝ`, so
`roots i` is empty. The root datum with empty index type on the zero
lattices satisfies `IsRootDatumOf i P`, and its coroot span is the whole
zero lattice. But `SL₂ → PGL₂` is a central isogeny between semisimple
groups that is not an isomorphism, so `PGL₂` is not simply connected. The
splitness hypothesis is what makes the actual lattices of `T` the lattices
of the geometric root datum.

**Integral coroots, not rational ones.** The hypothesis is about the
`ℤ`-span. Its rational span is all of `ℚ ⊗ X_*(T)` for every semisimple `G`,
so a rational version would assert simple connectedness of every split
semisimple group, which is false.

## Sources and provenance

The statement is derived from published results; the Lean form is not
verbatim.

**Milne.** J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`. Proposition 23.29, printed p.493 (PDF p.509):
"Let `(G, T)` be a split semisimple group with diagram `(V, Φ, X)`. If
`X = P(Φ)`, then `G` is simply connected." Proposition 23.59, printed p.502
(PDF p.518), adds the converse. Here `X = X^*(T)` is the character lattice
and `P(Φ)` is the weight lattice.

Milne's condition is equivalent to the coroot condition used here. By C.26,
printed p.613 (PDF p.629), `P(Φ) = {v ∈ V | ⟨v, α^∨⟩ ∈ ℤ for all α ∈ Φ}`,
and `P(Φ)` is the unique lattice in `V` such that the pairing restricts to a
perfect pairing `P(Φ) × Q(Φ^∨) → ℤ`, where `Q(Φ^∨)` is the `ℤ`-span of the
coroots. Since `G` is semisimple, `V = ℚ ⊗ X`, and `Q(Φ^∨)` is a full-rank
sublattice of `X_*(T)`. The pairing `X × X_*(T) → ℤ` is perfect. So
`X = P(Φ)` holds exactly when `X` is the dual lattice of `Q(Φ^∨)`. Taking
duals, this holds exactly when `X_*(T) = Q(Φ^∨)`. This reformulation is
derived here; it is not quoted.

Milne's Definition 18.5, printed p.388 (PDF p.404), calls a connected group
variety simply connected when every multiplicative isogeny from a connected
group variety is an isomorphism. The Library predicate uses central
isogenies from semisimple groups, matching the definition recalled by
Conrad–Gabber–Prasad below.

**Conrad–Gabber–Prasad.** B. Conrad, O. Gabber and G. Prasad,
*Pseudo-reductive groups*, second edition (2015), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`, printed p.500 (PDF p.526).
Before Corollary A.4.11 they recall that a connected semisimple group over a
field `k` is simply connected if "any central `k`-isogeny `G′ → G` from a
connected semisimple `k`-group is an isomorphism". In the proof of A.4.11
they state: "By Theorem A.4.10, a connected semisimple group is simply
connected if and only if the coroots generate `X^∨`." Theorem A.4.10 is the
Isogeny Theorem over a general field, printed p.499 (PDF p.525). That
sentence is the direct source of the coroot form of the hypothesis.

**Errata.** The project snapshot of Milne's errata
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for printed
pp.493, 502 or 613. Its entry for p.388 corrects the last sentence of
Remark 18.4 ("G should be reductive"), not Definition 18.5. No errata note
for Conrad–Gabber–Prasad was found.

## Role in the Library

The statement is an internal step towards
`IsSimplyConnectedFieldExtensionStatement` in
[`SimplyConnected.FieldExtensionStatement`](FieldExtensionStatement.md).
After base change to a field over which `G` splits, it lets simple
connectedness be read off from the coroots, which do not change under
further field extension. This module proves none of those steps. A proof of
this statement must not use the existence of simply connected covers,
because the cover-existence work depends on this criterion.
