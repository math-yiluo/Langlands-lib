# The Picard-zero direction of the field Picard-zero comparison

This module proves the "Picard-zero implies the origin component" half of
`Langlands.AbelianScheme.FieldPicardZeroGeometricComponentComparisonStatement`,
conditional on `Langlands.AbelianScheme.SmoothFamilyPicardZeroComparisonStatement.{u}`.
It then combines both halves into
`fieldPicardZeroGeometricComponentComparison_of`, which derives the whole
comparison statement from that one remaining hypothesis. The reverse direction
uses the published `fieldPicardZeroComponentConstancy` theorem. The companion
module `FieldPicardZeroGeometricComponentComparisonProof` discharges the
smooth-family input with the published `smoothFamilyPicardZeroComparison`
theorem. Like the Library module
`FamilyBaseChange`, the file sets
`backward.isDefEq.respectTransparency` and its `.types` variant to `false`. This
lets `pullback.lift_fst` rewrite through the carriers of base-changed abelian
schemes.

## Setting

Fix `S`, an abelian scheme `A` over `S`, `T : Over S` and `C : Over T.left`.
The geometric smooth-family predicate on the family `familyLineBundle A L`
over `T` produces data over the abelian scheme

```text
witnessScheme A T = (baseChange (𝟙 T.left)).obj ((baseChange T.hom).obj A)
```

over `T.left`: a parameter `C`, a line bundle `N` on `C ×_{T} witnessScheme`,
and two rational points `c0, c1` of `C`. The rigidified-family machinery for `A`
works instead on `(Over.map T.hom).obj C`, which is `C` viewed over `S`, with
product `C ×_S A`.

## Section `Transport`

- `witnessSpaceMap A T C : C ×_S A ⟶ C ×_{T} witnessScheme A T` is built from
  pullback lifts. Its first component is the projection to `C`. Its second
  component is the point of `(A ×_S T) ×_T T` given by the `A`-coordinate and the
  image of the `C`-coordinate in `T.left`.
- `witnessSymmetry A T : T ×_S A ⟶ (witnessScheme A T).X.left` is the lift of
  the product symmetry `relativeSpaceSymmetry A.X.hom T` along the base change
  by `𝟙 T.left`.
- `witnessPoint T C c : T ⟶ (Over.map T.hom).obj C` is a rational point
  `c : Over.mk (𝟙 T.left) ⟶ C` viewed as a morphism over `S`.
- `witnessPoint_projection`, `witnessPoint_fst`, `witnessPoint_snd`,
  `witnessSymmetry_fst`, `witnessSymmetry_snd` and `witnessSymmetry_hom` are the
  component identities of these maps.
- `witnessPoint_spaceMap`: restricting along `witnessPoint` and then applying
  `witnessSpaceMap` equals `witnessSymmetry` followed by the Library's
  `smoothFamilyPointMap (witnessScheme A T) C c`. Both sides are compared
  componentwise with `pullback.hom_ext`, through three nested pullbacks.
- `witnessSymmetry_comp`: `witnessSymmetry`, followed by the first projection and
  the inverse product symmetry, is the identity of `T ×_S A`.

## Section `Witness`

Fix in addition `N`, a line bundle `M` on `C.left`, and an isomorphism `ev`
between the tensor product of `M` with the unit-section restriction of the
transported bundle `witnessSpaceMap^* N`, and the structure sheaf.

- `witnessFamily A T C N M ev` is the rigidified family on
  `(Over.map T.hom).obj C` obtained by `LineBundle.normalize`. Its carrier is
  `witnessSpaceMap^* N ⊗ pr^* M`, and `ev` supplies its rigidification.
- `witnessRestrictionIso`: suppose `c^* M` is trivial. Then the carrier of the
  family pulled back along `witnessPoint T C c` is isomorphic to
  `witnessSymmetry^* (smoothFamilyPointMap c)^* N`. The iso chain is: pullback of
  a tensor product (`pullbackTensorObjIso`), triviality of the `M` factor
  (`tensorIsoTrivialIso`, `pullbackCompEqIso` with `witnessPoint_projection`, and
  the hypothesis), then `pullbackCompEqIso` with `witnessPoint_spaceMap`.
- `witnessFamily_trivial`: if also `(smoothFamilyPointMap c)^* N` is trivial,
  the pulled-back family is isomorphic to the relative trivial family over `T`.
- `witnessFamily_endpoint`: if instead `(smoothFamilyPointMap c)^* N` is
  isomorphic to `fibreLineBundle ((baseChange T.hom).obj A)
  (familyLineBundle A Lt) (𝟙 T.left)`, the pulled-back family is isomorphic to
  `Lt`. The carrier chain uses `witnessSymmetry_comp` to cancel the symmetry
  hidden in `familyLineBundle`.

The last two lemmas compare carriers only. The Library lemma
`RigidifiedLineBundle.nonempty_iso_of_forget_iso` turns a carrier isomorphism
into a rigidified isomorphism.

## Section `Main`: `mem_originComponent_of_isPicardZeroFamily`

Assume the smooth-family comparison, a universal pair `(P, L)` over `Spec k`,
and a geometric point `s : Spec K ⟶ P.left` with `K` algebraically closed, at
which the pulled-back family is Picard-zero. Put `T = Over.mk (s ≫ P.hom)` and
`σ = Over.homMk s rfl`.

1. The family conjunct of the comparison turns the Picard-zero hypothesis into
   the smooth-family condition. Its instance at the geometric point
   `𝟙 T.left` gives `C`, the geometric integrality of `C.hom`, `c0`, `c1`, `N`,
   an isomorphism `h0` with the trivial bundle and an isomorphism `h1` with the
   fibre of the family.
2. `LineBundle.exists_tensorObj_iso_structureSheaf` supplies `M` and `ev`. Every
   rational point `c` of `C` gives a line bundle `c^* M` on `Spec K`, which is
   trivial by `fieldLineBundleTriviality`.
3. Let `g` be the classifying map of `witnessFamily`. Two facts follow from
   `classifyFamily_pullback`, `classifyFamily_eq_of_iso`,
   `classifyFamily_trivial` and `classifyFamily_self`, applied with the two
   witness lemmas: `witnessPoint c0 ≫ g` is the terminal map followed by the
   trivial parameter, and `witnessPoint c1 ≫ g = σ`.
4. Geometric integrality gives geometric irreducibility, and the base `Spec K`
   is a one-point space. By
   `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`, `C.left` is
   irreducible, so the range of `g.left` is preconnected.
5. That range contains the origin point, by evaluating the first identity of
   step 3 at the closed point and using `trivialParameter_apply`. It also
   contains every point of the range of `s`, by the second identity. Hence
   `IsPreconnected.subset_connectedComponent` puts the range of `s` inside the
   connected component of the origin.

## `fieldPicardZeroGeometricComponentComparison_of`

The two directions are `mem_originComponent_of_isPicardZeroFamily` (from the
explicit smooth-family comparison hypothesis) and
`isPicardZeroFamily_of_mem_originComponent` (from the published constancy proof
and `LocallyOfFiniteType P.hom`, in `FieldPicardZeroComponentAssembly`). The
resulting reduction has the explicit hypothesis
`SmoothFamilyPicardZeroComparisonStatement.{u}`.
`FieldPicardZeroGeometricComponentComparisonProof` supplies its published proof
to obtain the exact unconditional target.

## Provenance

This is internal plumbing. The mathematical input to this direction is the
smooth-family comparison, the content of (7.21)–(7.22) of Edixhoven, van der
Geer and Moonen, *Abelian Varieties* (source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, PDF pp. 109–110). The
remaining steps are the universal property of `(P, L)` and the connectedness of
the image of an irreducible parameter scheme.


## Authorship and dependency boundary

This pair retains the carried Task 2104 forward argument (historically Worker
860). Worker 2104 updated the assembly to use the reverse implication
proved from published constancy. The actual smooth-family comparison is proved
in the published `SmoothFamilyPicardZeroComparisonProof` module, whose
authorship remains recorded there.

The proof does not import geometric-point or all-test-scheme Picard-zero
openness, any supplied-open-locus-to-component result, or an assumed
`IsPicardZeroOpenLocus`. The target and its protected imported pairs remain
unchanged.
