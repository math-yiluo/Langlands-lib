# Points of separated algebraic spaces with values in product rings

Author: Worker 105.

`SeparatedProductPointsInjectiveStatement` states the injectivity half of the
product-point comparison for separated algebraic spaces. It comes from Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), registered
source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
only states the result and contains no proof.

## Statement

For every commutative ring `C : Type u`, every actual algebraic space
`X : AlgebraicSpace (Spec (CommRingCat.of C))` with `IsSeparated X`, every index type
`ι : Type u` and every family `R : ι → Type u` of commutative `C`-algebras, the map

`p ↦ (i ↦ RingPoints.changeRing (Pi.evalAlgHom C R i) p)`

from `RingPoints C X (∀ i, R i)` to `∀ i, RingPoints C X (R i)` is injective.

Here `RingPoints C X A` (from
`Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`) is the set of sections
of `X` over the actual spectrum of the `C`-algebra `A`. `∀ i, R i` carries Mathlib's
product `C`-algebra structure, and `Pi.evalAlgHom C R i` is the projection to the
`i`th factor. `RingPoints.changeRing` pulls a point back along the induced morphism
of spectra. `IsSeparated X` says that the diagonal of `X` is a representable closed
immersion. No condition is imposed on `C`, on the index type or on the factors, and no
finiteness condition is imposed on `X`.

## Source and derivation

For schemes, Conrad considers on printed p.7 "a collection of `C`-algebras" `R_i`
with product `R = ∏ R_i`, an arbitrary `C`-scheme `X`, and the map
"(3.6.2) `X(R) → ∏ X(R_i)`". He claims "that this map is injective when `X` is
quasi-separated". For algebraic spaces, the proof of Proposition 5.2 (printed p.13)
says: "The proof of injectivity goes exactly as in the scheme case, due to the
separatedness hypothesis (to circumvent the fact that the diagonal of a general
algebraic space does not factor as a closed immersion followed by an open
immersion)."

Conrad states the algebraic-space injectivity only inside Proposition 5.2, for
separated finite type spaces over `O_{F,S}` and the adelic family of local factors.
This statement is the corresponding general form for separated algebraic spaces,
with the arbitrary base ring `C` and arbitrary family of `C`-algebras of (3.6.2).
The injectivity half of Proposition 5.2 is the special case `C = O_{F,S}` with the
local factors of `A_{F,S}`, after identifying `A_{F,S}` with the product of its
factors. Separatedness replaces the quasi-separatedness used for schemes, as Conrad
explains.

Also derived here: the name and the formulation of the map through
`RingPoints.changeRing` along the coordinate projections.
