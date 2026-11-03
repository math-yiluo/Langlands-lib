# Affine neighbourhoods of finite sets in an ample fibre of a proper family

`Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenStatement`
is a proposition target in every universe `u`. Let `f : X ⟶ S` be a
proper morphism with `S` locally noetherian, let `L` be an actual line
bundle on `X`, and let `s` be any point of `S`. Suppose that the specified
bundle pulled back along `f.fiberι s` is ample on the scheme-theoretic
residue-field fibre. Then every finite set `E` of points of `X` all
mapping to `s` is contained in one affine open `W` of `X`.

Only the restriction of this fixed bundle at the specified point is
assumed ample. The statement includes nonclosed points, empty finite
sets, nonreduced schemes, and arbitrary locally noetherian bases; no
field or characteristic assumption is imposed. The fibre itself need
not be finite. The conclusion concerns an open of the total space.

## Source and derivation

This is a derived consequence of the following primary Stacks Project
results, read in full including their comments:

- [Lemma 37.50.3, tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S),
  retained as `0D2S.html`, spreads ampleness of the specified invertible
  sheaf from one residue-field fibre to a neighbourhood of its base
  point.
- [Lemma 29.38.5, tag 01VK](https://stacks.math.columbia.edu/tag/01VK),
  retained as `01VK.html`, identifies relative ampleness with ampleness
  on the source when the base is affine.
- [Lemma 29.44.6, tag 0B5N](https://stacks.math.columbia.edu/tag/0B5N),
  retained as `0B5N.html`, gives local projectivity for a proper morphism
  carrying a relatively ample invertible sheaf.

All three pages are registered together as
`stacks-fibre-ampleness-affine-neighbourhood-2026-11-02`, HTML snapshot
retrieved 2 November 2026, content SHA256
`7a654789470ca2c545023588c4949fa09b3559b6801d9ff2f7c74b826eadc3a3`.
The Stacks reference to EGA IV.3, Corollary 9.6.4 is not a claim that
the EGA original has been read.

For the mathematical deduction, spread the fixed bundle from the
specified fibre, then shrink to an affine base neighbourhood `V` of `s`
on which the proper family has a closed immersion into some relative
projective space. Apply the existing theorem
`Langlands.AlgebraicGeometry.RelativeProjectiveSpace.exists_isAffineOpen_forall_mem_of_fibre`
to the finite set in the restricted family. The image of its affine
open under the open immersion `f ⁻¹ᵁ V ⟶ X` is the required affine
open of `X`. Properness is used in the spreading and local projectivity
steps. Local noetherianity is a retained restriction for the intended
quotient application; the cited spreading result allows a broader base.

The actual pullback line bundle and `LineBundle.IsAmple` use the
published scheme-module and section-generation-open definitions. The
conclusion is exactly the finite-set-in-one-fibre criterion required by
`FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`.
This file defines a proposition and supplies no proof of spreading,
local projectivity, the affine-open conclusion, or CM representability.
