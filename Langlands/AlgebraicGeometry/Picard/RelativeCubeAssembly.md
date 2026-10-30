# Assembling relative cube triviality from fibrewise and local inputs

This module is a conditional assembly. It derives the ordinary relative
three-face cube criterion for abelian schemes, and from it the published
target `Langlands.AbelianScheme.RelativeRigidifiedCubeStatement.{u}`, from
three explicit geometric hypotheses:

* `hF : FieldCubeTrivialityStatement.{u}`, the published theorem of the cube
  over an arbitrary field (statement only; its proof is owned by task
  `43f34b60-51af-49af-a39f-c17180f99b48`);
* `hL`, local two-axis triviality for smooth proper geometrically connected
  families over an arbitrary scheme. Its body is written out in full as a
  hypothesis. It is exactly the proposition requested by statement task
  `39e84a50-12a4-4e68-a013-c5e551c531c5`
  (`LocalTwoAxisTrivialityStatement`, Worker 606's interface), with the bound
  variables renamed. That statement is now published as
  `Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement` in
  module `Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement`
  (statement only; no proof of it is published). Since the two propositions
  agree up to the names of bound variables, a term of
  `LocalTwoAxisTrivialityStatement.{u}` can be passed for `hL` unchanged; a
  development check of exactly this application compiles. This module does not
  import that statement;
* `hZ : RigidifiedClassesZariskiSeparatedStatement.{u}`, the published
  Zariski separatedness of actual rigidified classes. It is now proved, with
  no further hypotheses, as
  `Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated` in module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof`.
  This module does not import that proof and keeps `hZ` as an explicit
  hypothesis.

Tensor preservation is not a hypothesis: the published proved theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` is used directly.
None of `hF`, `hL` or `hZ` is proved here. Therefore this module does not
prove the relative theorem of the cube. It reduces it to these three inputs.
Of the three, only `hZ` has a published proof, so the relative theorem of the
cube still depends on the unproved `hF` and `hL`.

## Main declarations

`Langlands.AbelianScheme.relativeRigidifiedCube_of_field_local_zariski`
has type `hF → hL → hZ → RelativeRigidifiedCubeStatement.{u}`, with the
arbitrary universe `u`. It feeds the three-face criterion below to the
published adapter `rigidifiedClasses_eq_of_ordinaryCubeTriviality`, together
with `pullbackTensorComparisonIsIso`.

`RelativeCubeAssembly.nonempty_iso_structureSheaf_of_faces` is the ordinary
three-face criterion. For an arbitrary scheme `S`, abelian schemes `A`, `B`,
`C` over `S`, and an actual line bundle `D` on `(A.X ⨯ (B.X ⨯ C.X)).left`,
assume actual module isomorphisms from the pullbacks of `D.obj` along
`CubeFace.first`, `CubeFace.second` and `CubeFace.third` (unit points) to the
structure sheaves. Then `D.obj` is isomorphic to the structure sheaf. The
hypotheses and conclusion have exactly the shape of the triviality input of
`rigidifiedClasses_eq_of_ordinaryCubeTriviality`. No quasi-separatedness,
noetherian, reducedness or projectivity assumption is used.

## Notation and elementary transports

`TrivialAlong f M` means that `(Scheme.Modules.pullback f).obj M` is
isomorphic to `Langlands.Scheme.Modules.structureSheaf` of the source.
`TrivialAlong.comp` and `TrivialAlong.of_fac` say that triviality along `f`
gives triviality along every morphism of the form `g ≫ f`. They use the
pullback composition isomorphism and `pullbackUnitIso`.
`TrivialAlong.pullback_iff` identifies triviality of a pulled-back module along
`g` with triviality along the composite. Almost every geometric comparison
below is reduced to an equality of scheme morphisms by these three lemmas.

For `t : T ⟶ S` and `X : Over S`, `bc t X` is `Over.mk (pullback.snd X.hom t)`,
the actual scheme base change. `baseChangeSection t x₀` is the induced
section `pullback.lift (t ≫ x₀.left) (𝟙 T)`. `toBase t φ` turns a
`T`-morphism `φ` into `bc t X` into the `S`-morphism
`φ.left ≫ pullback.fst` out of the composite `(Over.map t).obj W`.
`cubeBaseChange t X Y Z` and `pairBaseChange t Y Z` pair these maps into the
canonical comparisons from products of base changes to the original products
in `Over S`. `cubeBaseChange_first`, `_second` and `_third` show that the base
change of each cube face, followed by `cubeBaseChange`, equals
`pairBaseChange` followed by the original face. The proofs use the universal
property of products in `Over S`.

## Step 1: fibre triviality from the field cube

`trivialAlong_cubeBaseChange` takes a field `K : Type u`, a morphism
`t : Spec (CommRingCat.of K) ⟶ S`, and smooth proper geometrically connected
pointed `X`, `Y`, `Z`. Smoothness, properness and geometric connectedness of
`pullback.snd _ t` hold by stability under base change. The line bundle
`D` is pulled back along `(cubeBaseChange t X Y Z).left`. The face lemmas
transport the three face trivializations, and `hF` gives triviality of the
pulled-back bundle.

## Step 2: local triviality over the third factor

Let `X`, `Y`, `Z` be pointed smooth proper geometrically connected objects of
`Over S`. Over the base scheme `Z.left`, the two families are `bc Z.hom X`
and `bc Z.hom Y`. `productComparison X Y Z` is the canonical `S`-morphism from
their product over `Z.left` to `X ⨯ (Y ⨯ Z)`. It is built from the two `toBase`
maps and the structure map to `Z`. `productSection X Y Z` goes the other way.
It is defined over `Z.left` via `thirdProjection X Y Z`.
`productSection_comparison` proves that the composite
`productSection ≫ productComparison` is the identity. Its proof
(`triple_hom_ext`) checks the three coordinates through the pullback squares
of `Over.isPullback_of_binaryFan_isLimit`.

The section axes of the local two-axis statement are the cube faces.
`axisX_productComparison` identifies
`prod.lift (𝟙 _) (Over.mkIdTerminal.from _ ≫ y₀')` followed by
`productComparison` with `Over.prodLeftIsoPullback`'s inverse followed by
`CubeFace.second`. `axisY_productComparison` identifies the other axis with
`CubeFace.first`. For a point `c : Z.left`, let `residueBase Z c` be
`Z.left.fromSpecResidueField c ≫ Z.hom`. Then `fibreMap X Y Z c` maps the
scheme-theoretic fibre `(…).hom.fiber c` of the product over `Z.left` to the
triple product of the base changes to `Spec κ(c)`. It is built from
`fiberι`, `productComparison` and `fiberToSpecResidueField`.
`fibreMap_cubeBaseChange` shows that composing it with `cubeBaseChange` gives
`fiberι ≫ productComparison`.

`exists_local_triviality` puts these together. Pull `D` back along
`productComparison`. The second and first face hypotheses give triviality on
the two axes, and Step 1 at the residue field gives triviality on the fibre
at `c`. Hence `hL` yields an open `U ∋ c` of `Z.left` over which the pulled
back bundle is trivial. The conclusion is that, for every scheme morphism
`j : W ⟶ (X ⨯ (Y ⨯ Z)).left` with `j ≫ thirdProjection = k ≫ U.ι`, the
bundle `D` is trivial along `j`. The proof uses the factorization
`j = pullback.lift (j ≫ productSection) k _ ≫ pullback.fst _ U.ι ≫
productComparison`, which follows from `productSection_comparison`.

## Step 3: gluing by Zariski separatedness

In `nonempty_iso_structureSheaf_of_faces`, set `T = B.X ⨯ C.X` and let
`q : T.left ⟶ C.X.left` be the projection. Choosing a neighbourhood `U c`
from Step 2 for every `c : C.X.left` gives the open cover
`T.left.openCoverOfIsOpenCover (fun c ↦ q ⁻¹ᵁ U c)`, indexed by the points
of `C.X.left` in universe `u`. The first face trivialization makes `D` an
actual rigidified family `R = CubeRelativeTransport.cubeRigidified …` in
`RigidifiedFamily A T`.

`classesPullback_eq_trivial` shows that a rigidified family whose carrier is
trivial after base change along `h : V ⟶ T` has the trivial class there.
It uses `RigidifiedLineBundle.trivialIsoOfCarrierIso` with the relative
projection, whose section law is `relativeSection_projection`. This applies
on every cover member to both `R` and the trivial family. For `R`, the carrier
of the restriction is the pullback of `D` along
`(relativeSpace A.X.hom).map h ≫ (relativeSpaceProdIso _ T).hom`. That morphism
followed by `thirdProjection` factors through `(U c).ι` via
`relativeSpaceProdIso_hom_snd`, naturality of `relativeProjection` and
`morphismRestrict_ι`, so Step 2 applies. Thus `hZ` gives equality of the
classes of `R` and of the trivial family. The resulting rigidified isomorphism
gives a carrier isomorphism, and `CubeRelativeTransport.cubeRecoverTrivialization`
returns the required isomorphism from `D.obj` to the structure sheaf.

## Provenance

This is a derived assembly. Its shape follows the proof of the theorem of the
cube in the Stacks Project, More on Morphisms, Section "Theorem of the cube",
Theorem `theorem-of-the-cube` (tag 0BF4), `more-morphisms.tex` lines
9652–9720 at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. The
registered source is `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`. That
proof writes `X ×_S Y ×_S Z → Z` as `(X ×_S Z) ×_Z (Y ×_S Z) → Z`, applies
Lemma `lemma-pic-of-product` (tag 0BF3) with the sections induced by `x` and
`y` at points of `Z`, and finally pulls back along `x × y × id_Z`. Step 2
corresponds to the first two parts. `hL` is the specialization of 0BF3
requested by task `39e84a50-12a4-4e68-a013-c5e551c531c5`.

The implemented route differs from the source in two ways. First, Stacks
obtains fibrewise triviality on a "universal" locally closed subscheme from
Lemmas 0BDP and 0BF0 and a connectedness argument. Here the three face
hypotheses and the field theorem of the cube give fibre triviality at every
point directly (Step 1). The field form is Milne, *Abelian Varieties*,
Theorem 6.1 (registered `milne-abelian-varieties-1986-author-2022`), as
formalized by `FieldCubeTrivialityStatement`. Second, Stacks descends the
bundle to a line bundle on `Z` and then identifies it using the face
`x × y × id_Z`. Here the local trivializations are glued by Zariski
separatedness of rigidified classes over the parameter product, with the
rigidification supplied by the first face.

The relative theorem of the cube over an arbitrary base is the input cited in
Moret-Bailly, *Pinceaux de variétés abéliennes*, Chapter I, Proposition 2.6,
case (i), via Raynaud, LNM 119, IV.2.1. This module neither reproduces nor
relies on those proofs.

## Scope

All results hold in every universe `u`, over an arbitrary base scheme. This
includes nonreduced and non-noetherian bases. The quasi-separatedness
assumption of the target is not used. The abelian-scheme structure enters
only through `hZ`, the published adapter and the unit sections. Steps 1 and 2
apply to arbitrary pointed smooth proper geometrically connected objects of
`Over S`. The module adds no statement and changes no published
Lean/Markdown pair.
