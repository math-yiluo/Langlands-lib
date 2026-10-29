# Additive adjunctions on complexes and homotopy categories

Author: Worker 606. Internal categorical infrastructure.

Let `C` and `D` be arbitrary preadditive categories, with independent
object and morphism universes. Let `F : C ⥤ D` and `G : D ⥤ C` be additive
functors and `adj : F ⊣ G` an existing adjunction. For an arbitrary index
type `ι` and actual Mathlib complex shape `c : ComplexShape ι`, this
module defines the induced adjunctions on complexes and homotopy
categories. There are no boundedness, exactness, flatness, projectivity,
or abelian-category hypotheses.

`complexAdjunctionUnit adj c` and `complexAdjunctionCounit adj c` are
natural chain maps given in degree `i` by the unit and counit at `K.X i`.
Naturality of the original unit and counit proves that these maps
commute with differentials and are natural in chain maps.
`complexAdjunction adj c` uses these maps as its unit and counit;
each triangle identity is the original triangle identity in each
degree. The two `complexAdjunction_*_app_f` lemmas record the degreewise
formulas.

`homotopyAdjunctionUnit adj c` and `homotopyAdjunctionCounit adj c`
apply `HomotopyCategory.quotient` to the corresponding chain maps on
a representative complex. Naturality follows by representing a
homotopy-category morphism by a chain map and applying the quotient
functor to the complex-level naturality equality.
`homotopyAdjunction adj c` has these units and counits; its triangle
identities are the images of the complex-level identities under the
quotient functor. The two `homotopyAdjunction_*_app_quotient` lemmas
identify its components on represented objects explicitly.

For arbitrary commutative rings `R S : Type u` and an actual ring
homomorphism `φ : R →+* S`, the definitions
`extendRestrictScalarsComplexAdjunction` and
`extendRestrictScalarsHomotopyAdjunction` specialize the generic
construction to `ModuleCat.extendRestrictScalarsAdj φ`, using modules
with carrier in `Type u`. This includes `u = 0`. The complex unit is
therefore the degreewise tensor unit `x ↦ 1 ⊗ x` from Mathlib's module
adjunction. `moduleExtendScalarsAdditive` obtains the needed additivity
of scalar extension from the additivity of its right adjoint by
`Adjunction.left_adjoint_additive`.

This is internal categorical infrastructure derived from Mathlib's
existing `Adjunction`, `Functor.mapHomologicalComplex`,
`Functor.mapHomotopyCategory`, and quotient-functor constructions. It
does not transcribe a separate assertion from the literature, and it
does not prove geometric base change, scalar extension on a derived
category, or preservation of arbitrary quasi-isomorphisms.
