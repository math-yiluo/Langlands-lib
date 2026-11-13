# Actual affine reflections for explicit integer-valued building data

This internal helper extends the published local wrappers in
`ParahoricBuildingAxioms`, `RootReflectionProof`, `RootReflectionAction` and
`NormalizerAffineRootAction` to `IntegerValuationBuildingData v G`. The field
and universe are arbitrary. All algebraic hypotheses come from the supplied
building data; no topological, V7 or apartment-axiom premise is introduced.

`reflectionFunctional a g` has derivative `rootForm B.i a`; for a nonidentity
actual root point its value at every apartment point is that point's root
valuation. `reflectionAffineRoots_eq` identifies these point functionals
with the existing extended affine roots. The actual product of an opposite
factor pair is `reflectionElement`. The published `rootRankOneFactorization`
supplies `hasOppositeFactorPairs`.

`hasRootReflections` ports the final argument of
`RootReflectionProof.hasRootReflections`, reusing its arbitrary-field helpers.
V5 gives depth zero for both opposite factors and for the auxiliary conjugate.
The displacement of the apartment valuation has zero value in the reflecting
root direction. If another root were negative on that displacement, the
published extremal-root and separating-cocharacter argument, V3, and dynamic
subgroup separation would contradict a finite root depth. Applying the same
argument to the inverse excludes positive values. Every root therefore
annihilates the displacement, so it is zero in the reduced apartment.

`reflectionCoroot` is the class of the actual integral coroot. Its root value
is two. The Weyl action formula on characters determines the linear action
on reduced translations. Agreement at a point of the valuation-zero
hyperplane then proves `normalizerAffineEquiv_reflectionElement`: the actual
normalizer action is the affine reflection with this coroot. Generic
normalizer preservation of the original ordinary affine roots yields
`isCoroot_reflectionCoroot_without_apartment_axioms`.

The proof route is inherited from the published modules, rather than a new
source transcription. Its source comparison is KP Proposition 6.2.1,
printed pp.212–214/PDF243–245, Proposition 6.2.4, printed p.215/PDF246,
and Lemma 6.3.12, printed pp.220–221/PDF251–252. The arbitrary equipollence
class, root valuation axioms and actual normalizer action used there are
exactly the supplied interfaces here. The full target also needs derivative
spanning, integrality, discreteness and infinite fibres; this module alone
does not assert that target.
