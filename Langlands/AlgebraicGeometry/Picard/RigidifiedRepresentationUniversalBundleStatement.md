# Universal rigidified bundles from representations of the class presheaf

`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.RepresentationUniversalBundleStatement`
is a proposition in every universe `u`. It states that a representation of the
actual presheaf of rigidified line-bundle classes comes from an actual universal
rigidified line bundle. This module only states the proposition. A proof is a
separate, later unit; nothing here proves the statement.

## The data

The proposition quantifies over arbitrary schemes `S X : Scheme.{u}`, a morphism
`f : X → S`, a morphism `ε : S → X` and a proof `section_eq : ε ≫ f = 𝟙 S`. It also
takes an explicit proof
`coherence : Langlands.SchemeModule.RigidifiedModule.PullbackCoherenceStatement.{u}`,
an arbitrary `S`-scheme `P : Over S` and a representation

`r : (classPresheaf coherence f ε section_eq).RepresentableBy P`.

No hypothesis is placed on `f`, `S`, `X` or `P`.

These are the unchanged Library objects from `RigidifiedClassPresheaf` and
`RigidifiedUniversalBundle`:

- For `T : Over S`, `relative f ε section_eq T` is the category of rigidified line
  bundles on `T ×_S X` along the section `T → T ×_S X` induced by `ε`. An object
  is a sheaf of modules on `T ×_S X` that is locally free of rank one, with an
  isomorphism `α` from the structure sheaf of `T` to the pullback of the module
  along the induced section. A morphism is a module morphism compatible with
  these isomorphisms.
- `Classes f ε section_eq T` is the actual quotient of these objects by the
  relation "there is an isomorphism of rigidified line bundles". `classOf M` is
  the class of `M`.
- For `h : T → U` over `S`, `classesPullback h` is the map on classes induced by
  the actual relative pullback functor `relativePullback f ε section_eq h`.
- `classPresheaf coherence f ε section_eq : (Over S)ᵒᵖ ⥤ Type (u + 1)` has these
  values and maps. Its object and map functions do not use `coherence`. The
  proof `coherence` (the identity and composition compatibility laws of
  rigidified pullback) is used only to prove its functor laws.

`r` is Mathlib's `Functor.RepresentableBy`. It gives, for every `T : Over S`, a
bijection `r.homEquiv : (T ⟶ P) ≃ (classPresheaf coherence f ε section_eq).obj (op T)`.
The target is by definition `Classes f ε section_eq T`. The bijections are
natural: `r.homEquiv (h ≫ k)` equals the presheaf map of `h` applied to
`r.homEquiv k`, that is, `classesPullback h (r.homEquiv k)`.

## The conclusion

The proposition asserts that there exists an actual object

`L : relative f ε section_eq P`,

a rigidified line bundle on `P ×_S X`, such that both of the following hold:

1. `IsUniversal f ε section_eq L`. This is the unchanged Library predicate: for
   every `T : Over S`, the map `classifyingMap f ε section_eq L T` is bijective.
   Here `classifyingMap L T h` is `classesPullback h (classOf L)`, the class of
   the actual relative pullback of `L` along `h`. By `isUniversal_iff`, this
   means that every rigidified line bundle `M` on `T ×_S X` has exactly one
   `S`-map `h : T → P` with `(relativePullback h).obj L ≅ M` as rigidified line
   bundles.
2. For every `T : Over S` and every `h : T ⟶ P`,
   `classifyingMap f ε section_eq L T h = r.homEquiv h`. So the given
   representation is the classification by pullback of `L`. By
   `classifyingMap_eq_iff`, if `M` represents the class `r.homEquiv h`, then
   `(relativePullback h).obj L ≅ M` as rigidified line bundles.

Both clauses quantify over all `S`-schemes `T` in universe `u` and all `S`-maps
`T → P`. The bundle `L` is not given in advance; the proposition asserts that it
exists. The statement does not say that `L` is unique, or that its isomorphisms
are unique. It changes no imported definition.

## Conditional scope

The proposition is an implication from two explicit inputs: the coherence proof
and the representation `r`. It does not assert that the class presheaf is
representable for any `f`, and it does not assert that a universal bundle exists
without `r`. The Library's `RigidifiedModule.pullbackCoherence` (in
`RigidifiedPullbackProofs`) can supply `coherence` later. This module does not
import it.

The forward direction is already in the Library: `RigidifiedLineBundle.representableBy`
builds a representation of `classPresheaf` from a bundle that is already universal.
This proposition states the converse extraction. It is a categorical (Yoneda)
fact, not a geometric one.

## Source and provenance

The source is Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI §1,
paragraph (6.2), printed p.88 (PDF p.92). It is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The project
has no errata note for this source. The page was read directly.

There the source defines the functor `P_{X/S,ε}` sending `T` to isomorphism
classes of rigidified line bundles `(L, α)` on `X ×_S T`, with
`α : O_T ≅ ε_T^* L`, and pullback along `T' → T`. It then says: suppose
`P_{X/S,ε}` is representable by an `S`-scheme. Then `X ×_S P_{X/S,ε}` carries a
universal rigidified line bundle `(P, ν)`, the Poincaré bundle. Its universal
property: every rigidified `(L, α)` on `X ×_S T` is isomorphic, as a rigidified
bundle, to `(id_X × g)^*(P, ν)` for a unique `g : T → P_{X/S,ε}`. The source
states this passage from representability to a universal bundle without proof.

This statement is a derived, categorical formalization of that passage. Its
input is a representing `S`-scheme `P` with an explicit Mathlib representation
`r`. Its output is an actual bundle `L` with the source's universal property, in
the Library form `IsUniversal`. The second clause, equality of the canonical
classifying map with `r.homEquiv`, is an internal addition. It records that `L`
induces the given representation, and not only some other one. Other internal
choices, all taken from the imported modules:

- The fibre product is written `T ×_S X`, not the source's `X ×_S T`; the
  canonical symmetry is supplied by `RelativeGeometry`.
- The presheaf is set-valued. The source's group structure plays no role in
  representability or in this statement.
- The isomorphism `(relativePullback h).obj L ≅ M` runs in the opposite
  direction from the source's `(L, α) ≅ (id_X × g)^*(P, ν)`. Its existence does
  not depend on the direction.
- The canonical pullback compatibility laws are the explicit input `coherence`.

The source imposes the hypotheses `(∗)` of (6.2): `f` is quasi-compact and
quasi-separated, `f_*(O_{X ×_S T}) = O_T` for all `S`-schemes `T`, and `f` has a
section. The source uses them for the absence of nontrivial automorphisms of
rigidified bundles (p.88) and for the comparison of `P_{X/S,ε}` with
`Pic_{X/S}` through the facts (i)–(iii) of (6.2) (printed pp.88–89). Paragraph
(6.3), printed p.89 (PDF p.93), quotes geometric representability results under
further hypotheses, such as `f` proper, flat and of finite presentation. None of these hypotheses is needed for the abstract implication
stated here, and none is assumed. Conversely, this proposition proves nothing
about when a representation exists, about the Picard scheme, about
automorphisms, or about comparison with the fppf Picard sheaf. Those remain
separate obligations.

## Intended proof (not part of this unit)

The proof is a separate exact-target task. The intended route, proposed by
Worker 361, is the Yoneda argument. Choose a representative `L` of the class
`r.homEquiv (𝟙 P)`. Naturality, `r.homEquiv_comp h (𝟙 P)`, shows that
`r.homEquiv h` is `classesPullback h (classOf L)`, which is
`classifyingMap L T h`. Each `r.homEquiv` is bijective, so `IsUniversal L`
follows.
