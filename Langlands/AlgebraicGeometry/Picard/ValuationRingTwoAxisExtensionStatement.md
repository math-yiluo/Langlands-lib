# Extension of two-axis-trivial bundles over a valuation ring

`Langlands.AbelianScheme.ValuationRingTwoAxisExtensionStatement.{u}` defines a
proposition: a line bundle on the generic self-product of an abelian scheme over
a valuation domain, trivial on both unit axes, extends to a line bundle on the
total self-product, up to an actual isomorphism of module sheaves. This module
states the proposition and supplies no proof or new axiom.

Worker 477 authored the Lean prototype in parent task
`8164c2fb-4716-46ba-af56-abf5d4e1e235`, draft revision 1. Worker 339 retained its
mathematical body unchanged and wrote the documentation and source comparison.

## Formal statement and scope

Fix a universe `u`. The proposition quantifies over every commutative valuation
domain `R : Type u`, every field `K : Type u` with `[Algebra R K]` and
`[IsFractionRing R K]`, and every Library abelian scheme
`A : AbelianScheme (Spec (CommRingCat.of R))`.

Write `S = Spec R`, `T = Spec K`, and

```text
b = Spec.map (CommRingCat.ofHom (algebraMap R K)) : T ⟶ S,
B = (baseChange b).obj A,
π = pullback.fst A.X.hom b : B.X.left ⟶ A.X.left.
```

`B` is the actual scheme pullback, with the induced abelian-scheme structure.
The products in the statement are

```text
P = (mumfordProduct A).left = A ×_S A,
P_K = (mumfordProduct B).left = B ×_T B.
```

The displayed `pullback.map` defines the canonical morphism `q : P_K ⟶ P`:
its two components are the projections to `B` followed by `π`. Its compatibility
over `S` follows from the two base-change squares. Thus, under the canonical
identification `P_K ≅ P ×_S T`, `q` is the base-change projection. The
statement uses these actual pullbacks and this particular morphism, rather
than an unspecified isomorphic model of the generic square.

For every `D : LineBundle P_K`, its two hypotheses are the existence of
isomorphisms

```text
(id_B, e_B)^* D ≅ O_B,
(e_B, id_B)^* D ≅ O_B.
```

The first axis is `mumfordSection B`. The second is the explicit
`pullback.lift (B.X.hom ≫ unitSection B) (𝟙 B.X.left) ...` in the Lean
definition. Both isomorphisms are in the category of actual module sheaves.
They are asserted with `Nonempty`; no particular trivializations or
compatibility witnesses are inputs.

The conclusion is

```text
∃ E : LineBundle P, Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj).
```

Here `LineBundle` is the full subcategory of actual module sheaves that are
locally free of rank one, and `LineBundle.pullback q` lifts the ordinary
`Scheme.Modules.pullback q`. Consequently the conclusion requires an actual
bundle and an actual restriction isomorphism. It is stronger than merely
asking for some abstract relative Picard or correspondence class to extend.
It does not choose extended axis trivializations, assert uniqueness of `E`,
or assert that the particular trivializations chosen in a proof extend.

The valuation domain may have arbitrary rank; fields are included. There is
no noetherian, discrete-valuation, finite-rank, henselian, completeness or
characteristic assumption. Every fraction field with its given `R`-algebra
structure is allowed. There is no hypothesis on `A` beyond the Library
abelian-scheme bundle, and no ampleness, polarization or projectivity premise.

## Original sources

Michel Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, Lecture Notes in Mathematics 119 (1970), project copy second
corrected printing (1986), registered source
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`,
SHA256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`.
The source comparison uses rendered PDF pp.43–44 (printed pp.39–40) and
pp.165–166 (printed pp.161–162).

Definitions III 2.1–2.2 define the fppf sheaf of divisorial correspondences and
the subgroup `Pic^(e,f)(X ×_S Y)` of the ordinary Picard group consisting of
classes rigidifiable along the two sections. The two axis rigidifications
must agree after restriction to their intersection.

Proposition III 2.3(2) gives a bijection

```text
Pic^(e,f)(X ×_S Y) → Corr_S(X,Y)(S)
```

when the structure morphisms of `X` and `Y` are quasi-compact and
quasi-separated, both have the displayed sections, and the canonical maps
from `O_S` to the pushforwards of `O_X`, `O_Y` and `O_(X ×_S Y)` are
isomorphisms.

In the proof of Théorème XI 1.4, Raynaud recalls that for an abelian scheme
`G/S`, `Corr_S(G,G)` is represented by a separated scheme locally of finite
presentation over `S`, citing III 4.4. Lemme XI 1.5 then says that for
integral, geometrically unibranch `S` with generic point `η`, restriction
from its sections over `S` to its generic rational points is bijective.
The lemma does not require an ample bundle. Although phrased under the
hypotheses of XI 1.4, that theorem's invertible sheaf can be taken to be the
trivial sheaf for this application.

The proof of XI 1.5 is local on `S` and reduces by passage to the limit to a
noetherian base; it then uses extension over traits and EGA IV 18.10.20.
Noetherianity occurs in that proof, not among the hypotheses of XI 1.5.
On printed p.162 Raynaud explicitly identifies
`Pic^(e,e)(G ×_S G)` with `Corr_S(G,G)(S)` by III 2.3(2).

For the valuation-base specialization we also use the registered Stacks
Project source `stacks-valuation-normal-unibranch-2026-10-30`, retained in
`literature/Stacks Project - Valuation rings, normal schemes and geometric
unibranchness (HTML snapshot 2026-10-30)`. The relevant originals are
Section 10.50, Definition 10.50.1 and Lemmas 10.50.3–10.50.5 and 10.50.9
(`00I8.html`), Definition 15.108.1 (`0BPZ.html`), and Definition 28.16.1 and
Lemma 28.16.2 (`0BQ2.html`, `0BQ3.html`).

No source-specific Raynaud or valuation-source errata note was found in the
checked workspace, project notes and current Library notes. The retained
Section 10.50 comments concern typography and the arrangement of equivalent
characterizations; the three individual unibranchness pages have no comments.
This records the bounded check, without asserting that no errata exist.

## Why the sources imply this specialization

### The valuation base and the chosen fraction field

Mathlib's `ValuationRing R` for a domain requires divisibility of any two
elements to be comparable. Its
`ValuationRing.iff_isInteger_or_isInteger R K` identifies this with the
condition that every `x : K` is in the image of `R` or has its inverse in
that image. Stacks Lemmas 10.50.4–10.50.5 identify this with the source notion
of a valuation ring. Stacks explicitly allows fields, as does Mathlib's
`ValuationRing.of_field`.

`Spec R` is integral. Every local ring is a localization of `R`, hence a
valuation ring by Lemma 10.50.9 and a normal domain by Lemma 10.50.3.
Therefore `Spec R` is normal and, by Lemma 28.16.2, geometrically unibranch.
Definition 15.108.1 explains the latter step: a local normal domain is its
own integral closure, and its unchanged residue field is trivially purely
inseparable over itself. Definition 28.16.1 cites the same EGA IV 6.15.1
convention used by Raynaud. None of these steps requires a restriction on
rank or noetherianity.

The algebra map to the chosen fraction field `K` identifies `Spec K` with
the spectrum of the residue field at the generic point of `Spec R`, over
`Spec R`. Thus `B`, `P_K` and `q` are the generic fibres and restriction
map occurring in XI 1.5 after transport along that canonical identification.
This also covers the case when `R` is already a field: the fraction-field
algebra map is then an isomorphism.

### The pushforward hypotheses of III 2.3(2)

The Library bundle `AbelianScheme S` is a commutative group scheme whose
structure morphism `p : A → S` is smooth, proper and geometrically
connected. Forgetting explicit commutativity gives the geometric conditions
for an abelian scheme; no converse commutativity theorem is needed here.
Properness gives quasi-compactness and separatedness, hence
quasi-separatedness, as required in III 2.3(2).

The published theorem
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`, in
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`,
proves for every such morphism, over an arbitrary base, that the canonical
section map `p.app U` is an isomorphism for every open `U` of the base.
These are the components of `O_S → p_* O_A`, so the canonical sheaf map is
an isomorphism.

The first projection `A ×_S A → A` is a base change of `p`. It is smooth,
proper and geometrically connected; its composite with `p`, the product
structure morphism, has the same three properties. Applying the theorem
to this composite supplies the third pushforward isomorphism in III 2.3(2);
the two factors both use `p`. The unit sections supply `e` and `f`.
All three geometric properties are preserved by arbitrary base change.
Applying the same argument after any `T → S` gives the same canonical
pushforward identifications there, in particular over the given `Spec K`.
Thus the comparison is available on both the total and the generic square,
and naturally with respect to restriction. This explanation uses an already
proved Library theorem; this statement module does not import that proof or
formalize the sheaf-level comparison.

### Compatible rigidifications from the two hypotheses

Choose the inverses of the two isomorphisms asserted in the hypotheses, so
they have the source's orientation `O_B → i_j^*D`. Restrict them along the
unit `e_B : Spec K → B`. After the canonical pullback identifications both
are isomorphisms

```text
O_(Spec K) → (e_B,e_B)^*D.
```

They differ by an automorphism of `O_(Spec K)`, hence multiplication by a
unit `c ∈ Kˣ`. If the second is the first followed on its source by
multiplication by `c`, replace the second axis rigidification by its
precomposition with multiplication by the constant `c⁻¹` on `O_B`.
Its restriction now agrees with the first. Thus `D` is rigidifiable in the
precise sense of III 2.2, without any compatibility assumption on the two
independently chosen witnesses. This adjustment does not identify distinct
line bundles or assert that an axis-trivial bundle is trivial.

### From an extended correspondence to an actual bundle

The preceding adjustment puts `[D]` in `Pic^(e,e)(P_K)`. By III 2.3(2)
it gives a generic rational point of the scheme representing
`Corr_S(A,A)`. XI 1.5 extends that point to a section over `S`.
Applying III 2.3(2) over `S` gives a class `[E]` in `Pic^(e,e)(P)`.
This is a subgroup of the ordinary Picard group of actual invertible
sheaves: its elements are represented by actual bundles rigidifiable
along the axes. Choose such a representative `E`.

Naturality of the correspondence comparison identifies the image of
`[q^*E]` with the image of `[D]`. Injectivity of III 2.3(2) over `Spec K`
then gives equality in `Pic^(e,e)(P_K)` and hence in the ordinary Picard
group. Equality there means isomorphism of the actual invertible sheaves,
yielding the required `q^*E ≅ D`. This step uses both the comparison and
its injectivity, rather than treating equality of correspondence classes
as automatically an actual bundle isomorphism.

Our proposition specializes the base and the pair of schemes in XI 1.5
and III 2.3(2), and weakens their combined conclusion to existence of this
actual bundle and restriction isomorphism. It forgets the extended
correspondence, its uniqueness, and all axis rigidification data. It
does not use the ampleness conclusion of XI 1.4 or the Néron–Severi
construction in XI 1.6.

## Remaining proof obligations

This definition does not implement Raynaud's argument. A future exact-target
proof must construct or otherwise replace correspondence representability and
generic-point extension, including any needed limit reduction; prove the
rigidification and class comparisons and their naturality; turn the available
section-map theorem into the required pushforward statements for factors,
products and base changes; identify an arbitrary chosen fraction field with
the generic point; and transport the resulting actual bundle isomorphism
to the Library pullbacks along precisely `q`.

Neither this definition nor its publication discharges those obligations.
The imports use the published `MumfordBundle`, `AbelianScheme.Basic` and
`LineBundlePullback` interfaces. They do not assume
`PicardZeroValuativeExtensionStatement`,
`RelativeDualSchemeValuativeExistenceStatement` or
`ValuationRingAmpleExtensionStatement`. Proving this extension prerequisite
and obtaining an ample diagonal pullback over a field are separate tasks.
