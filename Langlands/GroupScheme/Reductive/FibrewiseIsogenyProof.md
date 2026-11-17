# Fibrewise isogenies of reductive group schemes are isogenies

Worker 685, with Worker 717.

`Langlands.GroupScheme.reductiveFibrewiseIsogeny.{u}` proves the unchanged
published proposition `ReductiveFibrewiseIsogenyStatement.{u}` for every
universe. For any scheme `S`, reductive group schemes `G'` and `G` over
`S`, and specified homomorphism `f : G' → G`, if its base change to the
residue field at every point of `S` is finite, flat and surjective, then
`f` itself is finite, flat and surjective.

The proof composes the following Library results.

1. `strictHenselianDvrKernelRemoval` factors a fibrewise isogeny over a
   strictly Henselian domain DVR as an isogeny followed by a homomorphism
   between reductive groups that remains an isogeny on every fibre and
   is an isomorphism on the specified closed fibre.
2. `strictHenselianDVRIsogenyRigidity` makes the generic fibre of that same
   remaining homomorphism an isomorphism.
   `strictHenselianDvrFibrewiseIsogeny_of_kernelRemoval_and_rigidity`
   then applies the generic-and-special-fibre isomorphism criterion and
   composes with the quotient isogeny. This proves the criterion over
   strictly Henselian domain DVRs.
3. `Langlands.CommutativeAlgebra.strictHenselianDvrExtension` supplies a
   faithfully flat strictly Henselian domain DVR extension of every
   domain DVR, in the same universe.
   `dvrFibrewiseIsogeny_of_strictHenselian_and_extension` uses base change
   and fpqc reflection of isogenies to prove the criterion over all
   domain DVRs.
4. `reductiveQuasiFiniteNoetherianModel` supplies a model over a
   noetherian subring for every locally quasi-finite flat surjective
   homomorphism between reductive groups over an affine base, retaining
   the specified map through actual base-change isomorphisms.
   `reductiveFibrewiseIsogeny_of_noetherianModel_and_dvr` combines this
   model with the DVR criterion and glues the result over an affine
   open cover of the arbitrary original base.

The theorem has exactly the published proposition as its type. All local,
extension and approximation inputs are supplied by the named theorems;
there are no additional hypotheses on the original scheme or
homomorphism.

This is an internal composition of the cited Library results. The target
is the Library formulation of Conrad's *Reductive group schemes* (2014),
Proposition 6.1.10. The proof follows the implemented reductions and their
local constructions; the statement and its import closure are unchanged.
