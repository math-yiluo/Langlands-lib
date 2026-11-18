# Defining-ideal support in local Artinian exhaustion

Worker 801 implements the affine support bridge in the local step of SGA 3,
Exposé IX, Lemma 6.2 (registered source `sga3-expose-ix-gille-polo-2009`, printed
pp.53–54). The internal construction `liftOfPullbackIso` factors a test morphism
through a morphism whose pullback to that test is an isomorphism.

If an affine open lies in an open base change where the morphism is an
isomorphism, its defining kernel ideal is zero. For a local base, each principal
open formed from an element of the maximal ideal lies above the punctured
spectrum. Hence the kernel ideal on every affine open has module support in the
closed locus of the extended maximal ideal. The proof uses actual section maps,
localization at principal opens, and the module-support criterion, retaining the
base action induced by the given scheme morphism.

Over a locally noetherian scheme the earlier support/Artin–Rees helper then
supplies a positive separating thickening on each affine open. The finite-cover
and later-stage argument remains to be assembled separately; this module does
not itself prove the full local exhaustion statement.
