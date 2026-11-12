# Fibrewise ampleness over a noetherian affine base

Author: Worker 833.

`Langlands.AlgebraicGeometry.Picard.ProperAffineFibrewiseAmpleStatement.{u}`
quantifies over schemes `X` and `S` in any universe `u`, an affine locally
noetherian base `S`, a proper morphism `f : X ⟶ S`, and a specified actual
line bundle `L` on `X`. If the actual pullback of `L` along `f.fiberι s`
is ample for every point `s : S`, the conclusion is `L.IsAmple` for the
Library's absolute ampleness predicate on the total scheme.

The fibres are the scheme-theoretic residue-field fibres, including those
at nonclosed points. There is no flatness, connectedness, normality,
smoothness, nonemptiness, or characteristic assumption. The statement
does not construct `L`, and its premise concerns every fibre of this
same specified bundle.

This is an internal derived target for the affine-base globalization
step in the normal-base abelian-scheme projectivity argument. Its
mathematical justification uses the published
`properFibreAmpleSpreading` theorem to obtain ampleness on inverse images
of neighbourhoods of all base points. Principal-open refinement and the
published line-bundle principal-section extension theorem then give the
global sections with affine generation loci required by `L.IsAmple`.
Properness over an affine base supplies compactness and
quasi-separatedness of the total scheme. The derivation uses the
Library's section-open definition directly and introduces no external
source claim.

The Lean module only defines the proposition. A proof must supply this
globalization argument; it cannot infer total ampleness from openness of
the ample-fibre locus alone.
