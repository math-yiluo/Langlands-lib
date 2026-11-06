# Descent of a reduced geometric singleton

The paired module
`Langlands.AlgebraicGeometry.ReducedGeometricSingletonStatement` defines
`Langlands.AlgebraicGeometry.ReducedGeometricSingletonStatement.{u} : Prop`.
It supplies a statement for a later proof; no proof of this proposition is
provided.

## Meaning of the Lean statement

Fix an arbitrary universe `u`, fields `K Ω : Type u`, an `Algebra K Ω`
instance, and `IsAlgClosed Ω`. Let `X : Scheme.{u}` and let
`f : X ⟶ Spec (CommRingCat.of K)` be locally of finite type. Write

```lean
XΩ := pullback f (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
```

This is the actual pullback in the category of schemes, representing
`X ×[Spec K] Spec Ω`. The proposition asserts that the three hypotheses

```lean
AlgebraicGeometry.IsReduced XΩ
Nonempty XΩ
Subsingleton XΩ
```

imply `IsIso f`. The first is Mathlib's scheme reducedness predicate: the
ring of sections of the structure sheaf on every open subset is reduced.
The latter two use the coercion of a scheme to its underlying type of
topological points. Together they say that the geometric base change has
exactly one point. The conclusion concerns the given structure morphism,
so it identifies `X` with `Spec K` over `K`.

There is no algebraicity or separability assumption on `Ω/K`. The statement
includes finite and imperfect fields `K`, in every characteristic. It
requires local finite type of `f`; it does not require a chosen affine
presentation of `X`, a group structure, smoothness, or properness.

Reducedness is imposed after base change. Over an imperfect field of
characteristic `p`, choose `a ∈ K` that is not a `p`th power and set
`L = K[t]/(t^p - a)`. Although `Spec L` is reduced and has one point, after
extension to `Ω` its coordinate ring is
`Ω[t]/((t - b)^p)`, where `b^p = a`. This base change has one point but
is not reduced, and `Spec L → Spec K` is not an isomorphism. Infinitesimal
examples such as `Spec (K[ε]/(ε²))` likewise show why the point premises
alone do not suffice. `Nonempty` also excludes the empty scheme.

## Derived provenance

This is an internal algebraic-geometric descent statement motivated by the
following sources, rather than a literal translation of a numbered theorem.
The cited passages were read in the registered originals; PDF page numbers
are one-based.

- R. Steinberg, *Regular elements of semi-simple algebraic groups*,
  Publications Mathématiques de l'IHÉS **25** (1965), 49–80. Source ID:
  `steinberg-1965-regular-elements-semisimple-groups`; SHA-256:
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
  Theorem 8.1, printed p.70/PDF p.23, relates regularity, the cross-section,
  and independence of the character differentials. The opening of §9,
  printed p.72/PDF p.25, explicitly assumes a perfect ground field.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic
  groups II*, Tohoku Mathematical Journal (2) **20** (1968), 443–497.
  Source ID: `borel-springer-1968-rationality-properties-ii`; SHA-256:
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`.
  Section 8.6, printed pp.483–484/PDF pp.41–42, explains the extension to
  arbitrary ground fields using §8.2 and the unique intersection of a
  regular semisimple class with the cross-section, with multiplicity one,
  deduced from Steinberg 8.1.

No source-specific errata note for these works was found in the supplied
project or current Library notes. The Borel–Springer rational-conjugacy
conclusion motivates the later application; it is not a hypothesis or an
import of this statement.

A possible later proof proceeds as follows. A nonempty scheme with one
topological point is affine, since an affine neighbourhood of its point is
the whole scheme. For reduced `XΩ`, its affine coordinate ring has zero
nilradical and a unique prime ideal, so that ideal is zero and the ring is
a field. Local finite type over the algebraically closed field `Ω` then
identifies the coordinate field with `Ω`. The base-changed structure
morphism is therefore an isomorphism. Isomorphisms descend under the
faithfully flat, quasi-compact map `Spec Ω → Spec K`. This explains the
formulation; the Lean module implements none of these proof steps.

## Intended use

For a scheme-theoretic intersection over `K` that becomes one point with
multiplicity one over `Ω`, a consumer must first construct its structure
morphism, prove local finite type, and establish reducedness, nonemptiness,
and the singleton point property after base change. Once this proposition
has been proved, it will identify that intersection with `Spec K`;
the inverse structure morphism gives its unique `K`-rational point. This
isolates the effective descent step in the arbitrary-field Steinberg
cross-section argument.

This statement does not construct an intersection or establish its
multiplicity, reducedness, or uniqueness. It does not prove a Steinberg
cross-section theorem or the parent quotient statement. The module
imports only Mathlib and adds this one proposition definition.
