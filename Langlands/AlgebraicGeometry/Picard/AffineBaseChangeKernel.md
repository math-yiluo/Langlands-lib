# Actual kernels of affine quotient base changes

This internal helper provides the actual structure-kernel calculation for the
canonical fibre product of a scheme over an affine base with a quotient of that
base. Its main definition is
`Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel.sectionHom`.

For commutative rings `B'`, `B`, a ring homomorphism `φ : B' →+* B`, a scheme `X`
and `f : X → Spec B'`, the section map sends a base element to its image under
the actual structure morphism on any open `U`. No algebra structure on the
section ring is supplied as an additional parameter.

`affine_ker` assumes `φ` surjective and `U` affine. It identifies the kernel of
the structure-sheaf map of `pullback.fst f (Spec φ)` on `U` with the extension of
`ker φ` under `sectionHom f U`. The proof uses the affine pushout of sections of
the actual Cartesian square, the existing ring pushout kernel formula, and the
canonical global-sections equivalences for the two spectra.

`isClosedImmersion` records that this actual first projection is a closed
immersion for surjective `φ`. `ker_pow_eq_bot` proves that a vanishing power of
`ker φ` gives the same vanishing power of the actual scheme ideal kernel. It
checks the affine-section ideals and uses preservation of powers by ideal
extension. No flatness assumption is used.

`ker_sq` assumes in addition that `B'` is local, `B` is nontrivial, and the
maximal ideal of `B'` annihilates `ker φ`. The ring kernel lies in the maximal
ideal because it is proper. Its square therefore vanishes, and the preceding
lemma transfers that vanishing to the actual scheme ideal kernel. Neither ring
needs to be Artinian for this helper.

## Provenance

Internal generalization of the Library's
`ArtinianSquareZeroPicardLifting.testSectionHom`, `relativeMap_affine_ker`, and
`relativeMap_ker_pow_eq_bot`, written directly for arbitrary affine quotients and
the canonical first projection instead of augmented Artinian tests. The proof
uses the same published ring-pushout lemma
`P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout`.
It supplies the square-zero geometry needed by Task 5704
(`60cd926c-5964-46c0-ad0e-111a8faf6631`) for the abelian scheme and its product.
It makes no assertion about Picard obstructions, cohomology injectivity or
lifting of line bundles.

Worker 2057 authored this pair.

`sectionHom` abbreviates the existing `AdicStalkQuotient.baseSectionHom`,
shared through `Modules/AffineBaseSections`; both uses have the same actual
structure-map construction.
