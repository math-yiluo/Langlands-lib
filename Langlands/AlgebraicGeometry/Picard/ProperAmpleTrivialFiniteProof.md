# Finiteness of a proper field scheme with an ample trivial line bundle

Author: Worker 475.

`Langlands.AlgebraicGeometry.Picard.properAmpleTrivialFinite` proves the
unchanged Library proposition
`Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteStatement.{u}`.
For every field `K : Type u`, scheme `X : Scheme.{u}`, morphism
`f : X ⟶ Spec (CommRingCat.of K)` and actual line bundle `L`, properness of
`f`, ampleness of `L`, and an actual module-sheaf isomorphism
`L.obj ≅ SheafOfModules.unit X.ringCatSheaf` imply `IsFinite f`.
The theorem has no additional hypotheses. It includes empty and nonreduced
schemes and fields of every characteristic, and its conclusion concerns the
whole scheme morphism.

This is a derived proof using the published quasi-affineness theorem and
Mathlib's canonical spectrum map. The statement's companion records the
original mathematical provenance. No statement or imported definition is
modified here.

The module imports
`Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineProof` and applies
its theorem `ampleTrivialQuasiAffine` to `L`, its ampleness proof, and the
given nonempty isomorphism type. This supplies
`AlgebraicGeometry.Scheme.IsQuasiAffine X` with no comparison or tensor-power
assumption. The tensor and whole-open comparisons are provided by that
published module and its imports.

The private helper `finite_of_proper_of_quasiAffine` proves the following
more general intermediate result: a proper morphism `f : X ⟶ Y` from a
quasi-affine scheme to an affine scheme is finite. Its proof is:

1. Write `j = X.toSpecΓ`. Naturality
   (`AlgebraicGeometry.Scheme.toSpecΓ_naturality`) identifies
   `j ≫ Spec.map f.appTop` with `f ≫ Y.toSpecΓ`. Since `Y` is affine,
   `Y.toSpecΓ` is an isomorphism, so this composite is proper.
2. `Spec.map f.appTop` is a morphism between affine schemes and is therefore
   separated. `AlgebraicGeometry.IsProper.of_comp` then makes `j` proper.
3. Quasi-affineness gives an open immersion `j`, hence a preimmersion.
   Properness gives that its range is closed. Applying
   `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion` to this closed
   range makes `j` a closed immersion.
4. A closed immersion into the affine scheme `Spec Γ(X, ⊤)` has affine
   source, by `AlgebraicGeometry.isAffine_of_isAffineHom`. Thus `X` is
   affine, and `f` is an affine morphism.
5. The equivalence
   `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom` gives finiteness
   of `f`.

The main theorem installs the supplied properness and the proved
quasi-affineness, then applies this helper with
`Y = Spec (CommRingCat.of K)`. Properness is used to obtain the closed
immersion in step 3. All geometric lemmas in the helper come from the pinned
Mathlib, notably `Mathlib.AlgebraicGeometry.QuasiAffine` and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, through the two direct Library
imports.
