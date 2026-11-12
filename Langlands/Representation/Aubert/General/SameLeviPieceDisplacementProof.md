# Proof of strict displacement on non-identity same-Levi pieces

`sameLeviPieceStrictDisplacement : SameLeviPieceStrictDisplacementStatement.{u}` proves the
intermediate proposition of `Aubert.General.SameLeviPieceDisplacementStatement` with no
extra hypotheses. The provenance is internal. The argument is the displacement step of
Renard VII.3, routed through the published unramified real-part computation of
`LanglandsClassification.UnramifiedPieceDisplacement`.

## Helpers

- `leviImageUnramifiedCharacter l hl χ`: the unramified character of `M(F)` obtained by
  pulling a character `χ` of the valuation image back along the continuous projection
  `M(F) → Hom(X^*(M)_F, ℤ)` (`Plancherel.rationalImageUnramifiedPullback`). By
  `leviImageUnramifiedCharacter_apply`, which holds by `rfl`, its value at `g` is
  `χ (rationalValuationImageProjection M g)`.
- `exists_imageUnramified_realPart_mem_chamber`: for a parabolic root presentation `pres` of
  `(p, l, a)` with reflection data `R`, some `χ` gives an unramified character whose real
  part `leviUnramifiedRealPart` lies in the open chamber `restrictedCorootChamber`. The
  proof takes a point `y` of the open simple-coroot face of the selected simple roots
  (`RelativeRootReflectionData.exists_mem_openSimpleCorootFace`). The restriction of `y`
  to the split component lies in the chamber. That restriction is the normalized real part
  of a pulled-back image character, by
  `Plancherel.normalizedRealPart_imageCharacterPullback_surjective`.

## Main proof

The proof first takes a parabolic root presentation of `P` and the split component `a`
(`parabolicRootPresentation`), and reflection data `R` for its maximal split torus
(`relativeRootReflectionExistence`). It chooses `ψ = leviImageUnramifiedCharacter χ`
with real part in the open chamber.
`GeometricLemmaIntersectionDatum.normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity`
applies to the non-identity double coset of `z`. It gives a nonzero cone vector `δ` such
that the real part of `ψ ∘ (b ≫ φ ≫ l' ≫ p')` on `A(F)` equals the real part of `ψ ∘ a`
minus `δ`.

Suppose, for a contradiction, that `a(t)` and `(b ≫ φ ≫ l' ≫ p')(t)` had the same valuation
image for every `t`. Then `ψ`, which factors through the valuation image, would agree on
the two maps. The two real parts would coincide, which forces `δ = 0`. This is
impossible, so some `t` separates the valuation images.
