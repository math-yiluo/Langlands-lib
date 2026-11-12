# The geometric theorem of the cube with a smooth third factor over arbitrary fields

Authors: Worker 816 (the published seesaw and local two-axis proof) and
Worker 2509 (the smooth-third generalization and proper specialization).
The proof body and all categorical helpers are reused from Worker 816's
published `FieldCubeTrivialityProof`; no unpublished draft is used.

The module proves the exact published proposition
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement.{u}`:

```lean
theorem Langlands.AlgebraicGeometry.Picard.fieldCubeTrivialitySmoothThird :
    Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement.{u}
```

The first two factors are smooth, proper and geometrically connected. The
third factor is smooth and geometrically connected. Its properness is
unnecessary: the original proof introduced `IsProper Z.hom` as a local
instance but did not use it. Removing this hypothesis and instance leaves
the seesaw, open-and-closed locus and rigidified gluing proof unchanged.
The existing theorem `fieldCubeTriviality : FieldCubeTrivialityStatement.{u}`
is retained, now by applying `fieldCubeTrivialitySmoothThird` and forgetting
its extra `IsProper Z.hom` hypothesis.

The universe `u` is arbitrary. All fields, schemes, sections, line bundles,
face morphisms and module-sheaf pullbacks are those of the unchanged
statement. The conclusion is `Nonempty` of an actual isomorphism from
`L.obj` to the structure-sheaf module on `(X ⨯ (Y ⨯ Z)).left`.

## Published inputs and geometric hypotheses

The argument uses these unconditional Library results:

- `localTwoAxisTriviality`, from `LocalTwoAxisTrivialityProof`: a line
  bundle on a product of two smooth proper geometrically connected
  families, trivial on the two section axes and one scheme-theoretic
  fibre, is trivial over a neighbourhood of that base point.
- `noetherianLineBundleSeesaw`, from `NoetherianLineBundleSeesawProof`:
  local isomorphism of two line bundles on a flat proper geometrically
  integral family, with the stated universal global-functions property,
  is represented by a closed subscheme of a locally noetherian parameter.
- `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`,
  from `SmoothProperConnectedGlobalFunctionsProof`: the canonical map on
  sections over every open of the base is an isomorphism for every smooth
  proper geometrically connected morphism. It is applied to actual base
  changes, including all test schemes used for rigidified uniqueness.
- `Langlands.AbelianScheme.smoothGeometricIntegrality`, from
  `SmoothGeometricIntegralityProof`: smooth geometrically connected
  schemes over a field are geometrically integral.
- `RigidifiedLineBundle.relative_iso_subsingleton` and
  `RigidifiedLineBundle.classes_zariskiSeparated_of_unique`, from
  `RigidifiedRelativeIsoUniqueness` and
  `RigidifiedClassesZariskiSeparatedGeneral`: under the universal
  structure-sheaf condition, actual relative rigidified isomorphisms are
  unique and their isomorphism classes are determined Zariski-locally.

Set `A = X ⨯ Y`. The published `product_geometry` shows that `A.hom` is
smooth, proper and geometrically connected. Hence it is flat and
geometrically integral, and its global functions commute with every affine
base change as required by seesaw. Smoothness makes `Z.left` locally
noetherian. Geometric connectedness makes it connected; smooth geometric
integrality also makes it reduced. These are derived properties, not
additional hypotheses.

## Implemented proof

The private `cubeIso` identifies the relative space
`R = Z ×_K (X ×_K Y)` with the actual product
`X ×_K (Y ×_K Z)`. It composes the published `relativeSpaceProdIso` with
the categorical product associator. The three projection identities and
the identities `section_cubeIso` and `third_face_cubeIso` are proved as
equalities of scheme morphisms, using the pullback universal properties.
Write `M` for the pullback of `L.obj` to `R`, and `N` for its structure
sheaf.

**The closed locus.** Apply `noetherianLineBundleSeesaw` to `A.hom`, the
parameter `Z`, and `M,N`, transported to the seesaw theorem's product
order. It supplies a closed immersion `ι : D ⟶ Z.left`. The published
`locallyIsoOver_seesaw_iff` rewrites its factorization criterion: a test
map `h : T ⟶ Z` factors through `ι` if and only if the pullbacks of `M,N`
to the relative space over `T` are isomorphic locally over `T`.

The third face makes `M` trivial after the test map `z₀`. Thus `z₀`
factors through `D`, so `Set.range ι` is nonempty.

**The range is open.** For `z ∈ Set.range ι`, `factor_residue` constructs
a factorization of `Z.left.fromSpecResidueField z` through `ι`.
Indeed, the base change of `ι` to `Spec κ(z)` is a surjective closed
immersion into a reduced scheme, so it is an isomorphism. Its inverse
gives the factorization. The seesaw criterion now gives local
isomorphism over `Spec κ(z)`. Since its topological space has one point,
`iso_of_locallyIsoOver_field` turns this into an actual global module
isomorphism on that relative fibre.

The helper `relative_trivial_along_of_fac` pulls this isomorphism to the
scheme-theoretic fibre of
`bc Z.hom X ⨯ bc Z.hom Y` over `z`. Its map to the original cube is the
published `productComparison`. The two axes are trivial by the first two
face hypotheses and the published `axisX_productComparison` and
`axisY_productComparison` identities. Therefore
`local_triviality_of_fibre` applies `localTwoAxisTriviality` to obtain an
open neighbourhood `U` of `z` on which the entire family is trivial.
This helper is the fibre-assumption version of the categorical
transport in `RelativeCubeAssembly.exists_local_triviality`; it does
not invoke that lemma's field-cube premise.

Pull the trivialization back to the relative family over `U`. The seesaw
criterion makes `U.ι` factor through `D`, showing that every point of `U`
lies in `Set.range ι`. This proves openness. The range is closed because
`ι` is a closed immersion. Connectedness of `Z.left` makes the nonempty
open and closed range the entire space. Reducedness of `Z.left` then
turns the surjective closed immersion `ι` itself into an isomorphism.

**Recovering a global isomorphism.** Apply the seesaw factorization
criterion to the identity of `Z`, using `inv ι`, and remove the identity
pullback comparisons. This gives actual local isomorphisms `M ≅ N` over
an open cover of `Z`.

The section of `A` determined by `(x₀,y₀)` induces a section of `R ⟶ Z`.
Its composite with `cubeIso` factors through the first cube face.
Consequently the first face trivialization equips `M` with an actual
rigidification along this section. The helper
`relative_trivial_of_locallyIsoOver` normalizes each local carrier
isomorphism by the published `nonempty_iso_of_forget_iso`, so it respects
the rigidifications. Universal global functions supply uniqueness via
`relative_iso_subsingleton`. The generic Zariski separation theorem
identifies the rigidified class with the trivial class, and
`Quotient.exact` recovers an actual rigidified isomorphism. This is the
general-relative version of the local-to-class argument in the
published seesaw reduction; it uses the generic separation theorem,
without an abelian group structure.

Forgetting rigidification gives `M ≅ N`.
`CubeRelativeTransport.recoverTrivialization` transports this along
`cubeIso` to the required isomorphism on the original cube. Its witness
is wrapped in `Nonempty`.

No properness, quasi-compactness, separatedness or finite type of `Z`
is required. No projectivity, ample bundle, field closure, restriction on
characteristic, Picard representability or supplied cube identity occurs
as a premise. There is no compatibility requirement on the original
three face trivializations. The elaborator option
`backward.isDefEq.respectTransparency false` assists definitional
unfolding. The checked theorem retains the level parameter `u` and uses
only `propext`, `Classical.choice` and `Quot.sound`.

## Original statement and proof provenance

The smooth-third target is the published specialization of Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, Theorem (2.5), printed p. 18
(PDF p. 22). That theorem permits a connected locally noetherian third
factor. Here smoothness supplies local noetherianity and, together with
geometric connectedness, reducedness, which is needed by the implemented
closed-immersion argument. The target's paired Markdown explains the
source's conventions and arbitrary-field specialization. No source-specific
errata note was found for this draft. Milne's Remark 6.3, p. 9, also records
that completeness of the third factor can be dropped over an algebraically
closed field; that remark alone is not the source of the present
arbitrary-field statement.

The original proper target is J. S. Milne, *Abelian Varieties*, author's corrected
January 2, 2022 version of the 1986 chapter, Theorem 6.1, printed/PDF
page 8. Page 2 gives his geometrically integral variety convention.
The statement companion explains the smooth proper geometrically
connected specialization. The exact Lean target and its import closure
are preserved.

Milne's proof invokes seesaw, a reduction to curves using Lemma 3.5
(page 5), Mumford §6, pages 57–58, and field-extension descent in
Lemma 6.2 (pages 8–9). These passages, the seesaw discussion on pages
7–8, and the retained Milne errata page were read. The listed errata
contain no change to Theorem 6.1. The retained Mumford Chapter II scan
was read at printed pages 54–58, including the cube statement and
curve/divisor proof.

The Lean proof uses an alternative route: the published local two-axis
theorem makes the seesaw locus open, eliminating the curve/divisor
reduction and extension to an algebraic closure. The local theorem's
paired proof traces its geometric input to Stacks tag 0BF3 and its
preceding lifting results; the seesaw proof traces its geometric input
to the published Anthropic FLT port. Those inputs are imported by Lean
name. The residue-field, product, local-to-global and open-and-closed
arguments in this module are internal consequences of the cited
published theorems and Mathlib's scheme/category/topology lemmas.

Registered sources:

- `edixhoven-vandergeer-moonen-abelian-varieties-draft`;
  retained `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`;
  SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`;
  locators: (0.4), printed p. 1 (PDF p. 5); Theorem (2.5), printed p. 18
  (PDF p. 22).
- `milne-abelian-varieties-1986-author-2022`;
  retained `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
  SHA-256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`;
  locators: pages 2, 5, 7–9, especially Theorem 6.1.
- `milne-abelian-varieties-1986-errata-2026-10-25`;
  retained `literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`;
  locator: complete errata list.
- `mumford-abelian-varieties-chapter-ii-scan`;
  retained `literature/David Mumford - Abelian Varieties, Chapter II (scan).pdf`;
  locators: §5, printed page 54; §6, printed pages 55–58
  (retained PDF pages 9–11). This is background for Milne's reference,
  rather than the implemented curve/divisor proof.
