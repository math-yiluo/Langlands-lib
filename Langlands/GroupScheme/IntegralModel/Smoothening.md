# Smoothening of affine integral group models

This module, `Langlands.GroupScheme.IntegralModel.Smoothening`, supplies a
foundational interface for the Chapter 8 construction of Kaletha–Prasad
integral models:

- the property `IntegralModel.IsSmoothening M N π`;
- two elementary theorems identifying literal integral-point subgroups;
- the Prop-valued existence target `IntegralModel.SmootheningStatement.{u}`.

It contains **no existence proof**. `SmootheningStatement` is a proposition
whose proof is left to a separate proof task.

## The property `IsSmoothening`

Fix a domain `R` with fraction field `K`, a group scheme
`G : GroupScheme (Spec K)`, existing models `M N : IntegralModel R K G`, and
`π : N.Hom M (𝟙 G)`. The existing `IntegralModel` structure makes `M.group`
and `N.group` actual group schemes over `Spec R`. Their structure morphisms are
affine, flat and locally of finite type, hence of finite type, and each model
carries a chosen isomorphism `genericIso` from its actual generic fibre to `G`.
The existing `Hom` structure supplies a group-scheme homomorphism
`π.hom : N.group ⟶ M.group` with the field `generic_comm`:

```
(baseChange (Spec.algebraMap R K)).map π.hom ≫ M.genericIso.hom
  = N.genericIso.hom ≫ 𝟙 G.
```

So `π` is the identity on generic fibres, read through the two chosen
identifications with `G`. The generic-fibre compatibility is part of the data
`π`. It is a statement about the generic fibres as group schemes, not only about
their rational points, and `IsSmoothening` does not restate it.

`IsSmoothening M N π` is the conjunction of exactly three clauses:

1. `N.IsSmooth`, that is, `Smooth N.group.X.hom`: the actual structure morphism
   of `N.group` is smooth in Mathlib's sense (locally of finite presentation and
   formally smooth).
2. `Function.Bijective (rationalPoints.map π.hom)`: the map from the group of
   sections `Spec R ⟶ N.group` over `Spec R` to the group of sections of
   `M.group`, given by composition with `π.hom`, is bijective. These are the
   actual `R`-sections, `N.integralSections` and `M.integralSections`.
3. For every `H : GroupScheme (Spec R)` with `Smooth H.X.hom` and every
   homomorphism `f : H ⟶ M.group`, there is a unique homomorphism
   `f' : H ⟶ N.group` with `f' ≫ π.hom = f`.

The definition puts no hypothesis on `R` beyond the ambient domain and
fraction-field instances. The existence statement below restricts the base.

Clause 2 is stated, not derived. Clause 3 concerns homomorphisms from smooth
group schemes. An `R`-section of `M.group` is not such a homomorphism, so
clause 3 does not directly lift sections. The source also states the bijection
on points separately (see below).

Once some smoothening satisfying clause 2 is known to exist, the uniqueness
remark under Provenance shows that every `N` satisfying clauses 1 and 3 also
satisfies clause 2. The definition keeps clause 2 explicit so that consumers can
use it without that existence theorem.

## The existence target `SmootheningStatement.{u}`

`SmootheningStatement.{u}` is the proposition:

> for every `R : Type u` with `[CommRing R] [IsDomain R]
> [IsDiscreteValuationRing R] [HenselianLocalRing R]
> [IsAlgClosed (IsLocalRing.ResidueField R)]`, every `K : Type u` with
> `[Field K] [Algebra R K] [IsFractionRing R K]`, every
> `G : GroupScheme (Spec K)` with `[IsAffineHom G.X.hom]` and
> `Smooth G.X.hom`, and every `M : IntegralModel R K G`, there exist
> `N : IntegralModel R K G` and `π : N.Hom M (𝟙 G)` with
> `IsSmoothening M N π`.

In words: over a Henselian discrete valuation ring with algebraically closed
residue field, every affine, flat, finite-type integral model of a smooth affine
generic group has a smoothening. There is no completeness, excellence,
characteristic or perfectness hypothesis beyond these. An algebraically closed
residue field is in particular perfect and separably closed. Together with
Henselianity, this makes `R` strictly Henselian.

## Original source and the specialization

Source: Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, content SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Page numbers are printed / PDF. The PDF page is the printed page plus 31.

### What the source states

- The Appendix A convention (p.593 / PDF p.624): `k` is a nontrivially
  discretely valued Henselian field with valuation ring `o` and residue field
  `f`. As in §2.1 (p.70 / PDF p.101), `K` is the maximal unramified extension of
  `k` and `O` is its ring of integers.
- The opening of §A.6 (p.645 / PDF p.676): for an affine finite-type
  `o`-scheme `X` with smooth generic fibre there is a smooth affine finite-type
  `X∞ → X` that is an isomorphism on generic fibres and induces a bijection
  `X∞(O) → X(O)`. The source cites [BLR90, Theorem 3.1.3, Corollary 3.1.4]
  for this, then reviews the case of an affine flat finite-type group scheme. It
  adds that `X∞` is uniquely determined by Corollary 2.10.11.
- Construction A.6.1 (p.645 / PDF p.676): set `X(0) = X`. `Y(i)` is the Zariski
  closure, in the special fibre, of the image of the reduction map from `X(i)(O)`
  to the points of `X(i)` over the residue field of `O`. The source notes that
  `Y(i)` is a smooth group scheme. `X(i+1)` is the dilatation of `Y(i)` in
  `X(i)` (Definition A.5.1). It is a group-scheme integral model by
  Proposition A.5.3 and Lemma A.5.7, and `X(i+1)(O) → X(i)(O)` is bijective.
- Theorem A.6.2 (pp.645–646 / PDF pp.676–677): some `X(i)` is smooth. The source
  gives a sketch through a Néron defect of smoothness and refers to
  [BLR90, §3.3, Proposition 5] for the decrease of the defect. After that,
  Lemma 8.1.3 shows that the sequence stabilizes.
- Definition A.6.3 (p.646 / PDF p.677): the smoothening `X∞` is `X(n)` for
  `n ≫ 0`.
- Lemma A.6.4 (p.646 / PDF p.677): for every smooth group scheme `Z` and
  homomorphism `f : Z → X` there is a unique homomorphism `f∞ : Z → X∞` with
  `f = i∞ ∘ f∞`. Moreover, if `f` is a closed immersion, then so is `f∞`.
- Corollary A.6.5 (p.646 / PDF p.677): a bounded open subgroup `U` of `X(K)`
  is schematic if and only if `U = X(O)` for some integral model `X`, not
  necessarily smooth. The proof is "`X∞(O) = U`".
- Proposition 8.3.1 (pp.295–296 / PDF pp.326–327) uses Corollary A.6.6 and then,
  for a vertex, takes the schematic closure of `ρ(G)` in `GL(L)` and applies
  Corollary A.6.5.

### How the Lean statement specializes it

`R` plays the role of `o`, `K` the role of `k`, `G` the role of the generic
fibre `X`, and `M.group` the role of `X`.

Since `R` is Henselian with algebraically closed residue field, `K` has no
nontrivial unramified extension. A finite unramified extension of a Henselian
discretely valued field corresponds to a finite separable extension of the
residue field, and here there is none. So the source's `K` is `K` itself and
`O = R`. Then the source's `X(O)` is literally `rationalPoints M.group`
(= `M.integralSections`), and the source's bijection `X∞(O) → X(O)` is clause 2
on actual `R`-sections. The residue field of `O` is the residue field of `R`, so
the reduction map in Construction A.6.1 is the reduction of `R`-sections to
points over that algebraically closed field.

This is the base on which the source applies smoothening in Chapter 8. §8.3
(p.295 / PDF p.326) says "we will exclusively work over `K`" and constructs
smooth affine `O`-models. §A.7 (p.647 / PDF p.678) recalls that `O` is
strictly Henselian. The authors' corrections (below, PDF p.37) assume from §8.3
onward that `f` is perfect, so the residue field of `K`, which is that of `O`,
is an algebraic closure of `f`. `O` is again a Henselian discrete valuation ring
with algebraically closed residue field, so its fraction field has no nontrivial
unramified extension. Applying §A.6 with `o := O` therefore gives exactly the
case stated here.

Over the algebraically closed residue field, `Y(i)` is the Zariski closure of a
subgroup of rational points. It is a reduced closed subgroup, hence smooth, which
matches the source's remark that `Y(i)` is smooth.

**Not asserted.**
- No claim is made over a base whose residue field is not algebraically
  closed, for example a finite residue field. There the source's bijection is on
  points over the larger ring `O`, not on `R`-sections.
- Strictly Henselian bases with separably closed but imperfect residue field
  are also not covered. §8.3 assumes a perfect residue field anyway.

### Scope of the universal property

Clause 3 quantifies over every group scheme `H` over `Spec R` whose structure
morphism is smooth in Mathlib's sense. `H` need not be affine, quasi-compact or
separated. This matches Lemma A.6.4, which says "a smooth group scheme" with no
affineness hypothesis, and its proof works in this generality:

- Lemma 8.1.3 (p.284 / PDF p.315) applies to every smooth `o`-scheme, with no
  affineness hypothesis. Here `o = O = R`, so it makes the reduction map from
  the `R`-sections of `H` onto the points of `H` over the residue field
  surjective.
- Fact A.5.5 (p.633 / PDF p.664) holds for any flat `o`-scheme `Z`. Smooth
  implies flat.
- Over the algebraically closed residue field, the special fibre of a smooth
  `H` is smooth, hence reduced, and its rational points are dense. So the
  surjectivity above puts the special fibre of `f` inside the reduced closed
  subscheme `Y(i)`, as the proof of Lemma A.6.4 requires.

The source's additional closed-immersion conclusion of Lemma A.6.4 is
**omitted**. Uniqueness in clause 3 is among homomorphisms `H ⟶ N.group`, as in
Lemma A.6.4.

### Provenance

The Lean defines a **characterizing property**, not the source's construction
`X(n)` (Construction A.6.1, Definition A.6.3). The three clauses collect the
properties the source proves or states for `X∞`:

- smoothness (Theorem A.6.2);
- the bijection on points (the opening of §A.6 and Construction A.6.1);
- the universal property (Lemma A.6.4, without its closed-immersion part).

The isomorphism on generic fibres comes from `IntegralModel.Hom`.

The source asserts uniqueness through Corollary 2.10.11. In the present
formulation, uniqueness up to unique isomorphism over `M` follows informally
from clauses 1 and 3 by the usual Yoneda argument, and the induced isomorphism
respects the generic identifications. That uniqueness is a remark only: it is
**not** stated or proved in Lean.

[BLR90] (Bosch–Lütkebohmert–Raynaud, *Néron Models*) is cited by the source for
the general smoothening and the termination step. It is not in the central
library and was not consulted.

### Corrections

The authors' *Corrections and additions* (1 November 2024), literature ID
`kaletha-prasad-2024-corrections`, content SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:

- PDF p.37 replaces the first sentence of §8.3. It assumes that the residue
  field `f` of `k` is perfect "in this and the subsequent paragraphs", so the
  residue field of `K` is an algebraic closure of `f`. The present
  residue-field hypothesis meets that restriction.
- PDF pp.49–50 correct the residue-field assumption of Appendix A.4.
- The corrections list nothing for §A.5 or §A.6.

## Implemented elementary consequences

`integralPoints_eq_of_surjective_sections M N π hπ` assumes only that
`rationalPoints.map π.hom` is surjective. It proves the equality of literal
subgroups `N.integralPoints = M.integralPoints` of `rationalPoints G`, the
generic rational points of the given group `G`. This is an equality of the
actual subgroups, not an abstract isomorphism. The proof uses extensionality on
an element `g`:

- (⊆) If `g ∈ N.integralPoints`, the existing
  `IntegralModel.Hom.map_mem_integralPoints` applied to `π` gives
  `rationalPoints.map (𝟙 G) g ∈ M.integralPoints`. `simp` with
  `rationalPoints.map_apply`, `Grp.id_hom_hom` and `Category.comp_id` rewrites
  `rationalPoints.map (𝟙 G) g` to `g`.
- (⊇) If `g = M.integralPointMap x`, surjectivity gives `y` with
  `rationalPoints.map π.hom y = x`. The existing
  `IntegralModel.Hom.integralPointMap_naturality` gives
  `N.integralPointMap y = rationalPoints.map (𝟙 G) (M.integralPointMap x)`, and
  the same `simp` set removes `𝟙 G`. So `y` witnesses
  `g ∈ N.integralPoints`.

Injectivity of the section map is not used.

`IsSmoothening.integralPoints_eq` applies this to the surjectivity component
`hπ.2.1.2` of clause 2. So a smoothening has the same literal integral-point
subgroup of `rationalPoints G` as the model it smoothens. Over the present base
this is the source's `X∞(O) = X(O)` in the proof of Corollary A.6.5.

These two theorems are elementary consequences of the interface. They are not
existence results.

## Remaining obligations for a proof of `SmootheningStatement`

A proof needs the actual construction and its termination, or another valid
argument:

- the dilatation of a closed subgroup of the special fibre as an affine flat
  finite-type group scheme over `Spec R`, with its functor of points
  (Definition A.5.1, Proposition A.5.3, Lemma A.5.7). The Library's
  `Langlands.GroupScheme.Dilatation.CoordinateAlgebra` implements the algebra
  `A[I/π]` and its spectrum, but not the group structure, the universal property
  or smoothness;
- the universal property of the dilatation for flat schemes (Fact A.5.5);
- the closed subgroup `Y(i)`, the Zariski closure of the reduced sections, and
  its smoothness over the algebraically closed residue field;
- the bijection of `R`-sections at each step;
- Hensel lifting for smooth schemes (Lemma 8.1.3);
- termination (Theorem A.6.2, whose details the source delegates to
  [BLR90, §3.3, Proposition 5]) and stabilization.

Outside this statement, and not constructed here, are schematic closure in
`GL(L)`, intersections of schematic subgroups (Corollary A.6.6), finite-index
gluing (§A.7), unramified descent, relative identity components, torus clauses
and special-fibre root and quotient geometry. In particular, this statement
alone does not prove `IntegralModelAxiomsStatement`.
