# Finite locally free equivalence relations on schemes

Authors: Worker 1001 supplied the Lean statements in the task; Worker 101
checked the original source and Library conventions, retained that Lean text,
and wrote this Markdown.

The module
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements`
defines two propositions in namespace `Langlands.AlgebraicGeometry`:

- `FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}`;
- `FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u}`.

They state an existence consequence of Stacks Proposition 39.23.9 and a
finite-set extension of Stacks Lemma 39.24.1, respectively. Both are
Prop-valued definitions for every universe `u`. This module supplies no
proof of either proposition.

## Original source

The registered source is
`stacks-groupoid-schemes-chapter-pdf-2026-07-14`, The Stacks Project Authors,
*Groupoid Schemes*, Chapter 39, version `ed88ff78`, compiled 14 July 2026.
The retained file is
`literature/Stacks Project - Groupoid Schemes chapter (PDF 2026-07-14).pdf`,
SHA-256
`4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`.
The locators below use the PDF's printed page numbers, which equal its
one-based PDF page numbers:

- Definition 39.3.1, [Tag 022P](https://stacks.math.columbia.edu/tag/022P),
  p.2, defines an equivalence relation `j = (t, s) : R → U ×_S U`.
  Lemma 39.3.4, [Tag 022Q](https://stacks.math.columbia.edu/tag/022Q),
  p.3, gives the corresponding equivalence relation on underlying points.
- Lemma 39.23.6, [Tag 03BL](https://stacks.math.columbia.edu/tag/03BL),
  p.47, proves in particular that `U → Spec C` is surjective.
- Proposition 39.23.9,
  [Tag 03BM](https://stacks.math.columbia.edu/tag/03BM), starts at the foot
  of p.50 and continues on p.51. It constructs the affine quotient of an
  affine finite locally free equivalence relation.
- Lemma 39.24.1, [Tag 03JE](https://stacks.math.columbia.edu/tag/03JE),
  with its proof on p.52, constructs an invariant affine neighbourhood of
  one point when its orbit is contained in an affine open.

These passages were read in the retained PDF. No errata note for this
source exists in the current Library. The finite-set proposition below is
derived from the proof on p.52; it is not the lemma's printed statement.

## Common hypotheses and the absolute setting

The Lean module imports Mathlib's scheme limits and its morphism-property
modules for finite, flat and locally finitely presented morphisms.
Mathlib is pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435` in the prepared environment.
It uses the same relation convention and point conditions as the Library
structure `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`, with
finite locally free projections in place of étale projections.

Both propositions quantify over arbitrary schemes `U R : Scheme.{u}` and
morphisms `t s : R ⟶ U`, with these hypotheses:

- `Mono (prod.lift t s)`: the map `(t, s)` into the categorical product
  `U × U` is a monomorphism.
- For every scheme `T : Scheme.{u}`, every `a : T ⟶ U` lifts to a
  diagonal related pair; every `r : T ⟶ R` has a reversed pair; and
  every pair `r r' : T ⟶ R` with `r ≫ s = r' ≫ t` has a composite
  pair with endpoints `r ≫ t` and `r' ≫ s`.
- Each of `t` and `s` is `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation`. Together these express finite local
  freeness.

The first four hypotheses are precisely the `mono_lift`, `refl`, `symm`
and `trans` conditions of that Library structure, without its étaleness
fields. Monicity makes each related pair have at most one lift. The point
conditions therefore describe the equivalence relation of Definition
39.3.1 on p.2. By Yoneda they also recover the groupoid's identity,
inversion and composition maps: apply reflexivity to `T = U`, symmetry
to `T = R`, and transitivity to `T = R ×_{s,U,t} R`. Their identities
follow from the uniqueness of a lift with specified endpoints. These
observations explain the comparison with the source's groupoid
notation; they are not additional Lean theorems in this module.

Stacks allows an arbitrary base scheme `S`. Here schemes are considered
over the terminal scheme `Spec ℤ`, so the product over `Spec ℤ` is the
categorical product of schemes. This does not impose a field or
separatedness hypothesis. Moreover, a relative equivalence relation over
any `S` gives one of these absolute relations after forgetting its base.
The map `U ×_S U → U × U` is a monomorphism, as a base change of the
diagonal of `S`, so composing it with the relative monomorphism preserves
monicity. For any absolute map `T → U`, its composite `T → S` equips
`T` with the required base structure. The relative reflexivity,
symmetry and transitivity conditions then give the absolute point
conditions above; the equal middle endpoint in transitivity ensures a
common map to `S`. Finiteness, flatness, local finite presentation,
affineness and the underlying points and opens concern the same scheme
maps. Thus these statements apply to the underlying schemes of the
source's relative equivalence relations, while their conclusions record
only the absolute data.

No Noetherian, separatedness, base field, or extra finite type hypothesis
is added. In particular `u` is unrestricted, and every test scheme in that
universe is quantified over.

## Affine quotient statement

`FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}` adds
`IsAffine U` to the common hypotheses. Its conclusion is the existence
of `M : Scheme.{u}` and `q : U ⟶ M` with

- `IsAffine M`;
- `IsPullback t s q q`;
- `IsFinite q`, `Flat q`, `LocallyOfFinitePresentation q`, and
  `Surjective q`.

The pullback condition includes `t ≫ q = s ≫ q` and says that the
square with top `t`, left `s`, and both other arrows `q` is a pullback.
Equivalently, `(t, s)` identifies `R` with `U ×_M U`.

Proposition 39.23.9, pp.50–51, assumes both `U = Spec A` and
`R = Spec B` affine. The Lean statement needs only `IsAffine U`:
the finite morphism `t : R → U` is affine, so `R` is affine as well.
For the invariant subring
`C = {a ∈ A | t♯(a) = s♯(a)}`, the source constructs `M = Spec C`
and proves that `q : U → M` is finite locally free and that
`R = U ×_M U`. This yields all the Lean conclusions except for the
explicit surjectivity clause; Lemma 39.23.6(1), p.47, supplies that
clause for this same map. Thus forgetting the construction of `M`
gives exactly the existence form recorded here.

The source also identifies `M` with the fppf quotient sheaf. The Lean
definition records neither that quotient-sheaf property nor the
identification of its existentially quantified `M` with the spectrum of
the invariant subring. It records only the affine scheme, the morphism
properties and the pullback square. None of those conclusion data is
assumed as a hypothesis.

## Invariant affine open statement

`FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u}`
uses the common hypotheses without assuming `U` affine. For every
`E : Set U` and open `W : U.Opens`, it assumes

- `E.Finite`;
- `IsAffineOpen W`;
- `∀ r : R, s r ∈ E → t r ∈ W`.

It concludes that there is an open `V : U.Opens` with `IsAffineOpen V`,
`E ⊆ (V : Set U)`, and `s ⁻¹ᵁ V = t ⁻¹ᵁ V`. The final equality is
equality of inverse-image opens of `R`, expressing `R`-invariance.
The given affine open `W` is not required to be invariant.

Lemma 39.24.1 on p.52 is printed for one point `u`. Its proof works
with the finite orbit `t(s⁻¹({u})) = {u₁, …, uₙ}` throughout. For a
finite set `E`, replace that orbit by `F = t(s⁻¹(E))`. This is a
finite union of finite sets, because `s` has finite fibres.
Reflexivity gives `E ⊆ F`, and the third Lean hypothesis above is
exactly `F ⊆ W`. The relation on points of Lemma 39.3.4, p.3, shows
that `F` is a union of whole equivalence classes.

The same proof on p.52 then applies verbatim to this finite `F`.
It first constructs an invariant open `W'` with `F ⊆ W' ⊆ W`,
then chooses a function `f` on the affine `W` with
`F ⊆ D(f) ⊆ W'`. For the restriction of the finite locally free
map `s` to `s⁻¹(W')`, it uses `g = Norm_s(t♯ f)`. Its norm
argument gives the invariant affine open `D(g)` containing `F`.
Taking `V = D(g)` yields `E ⊆ V` as required. This is the
provenance of the finite-set extension; no norm construction or proof
of that extension is implemented in this statement module.

Although the printed lemma allows general groupoids, the Lean
proposition specializes to equivalence relations through its monicity
hypothesis. It retains arbitrary schemes and arbitrary finite `E`,
including the empty set. It assumes neither an invariant affine open
containing `E` nor an affine quotient. A successor proof must establish
the stated conclusion from the displayed hypotheses.
