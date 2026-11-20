# Affineness on local Artinian tests

Worker 584. `AffineResidueFiberArtinianPullbackStatement` says that
a locally finite-type group scheme over any base, with affine actual
residue fibres, has affine actual pullback to the spectrum of every
local Artinian ring.

The proof transports the affine residue-fibre condition along arbitrary
base change. The actual fibre at the closed point of the test is a
pullback along the quotient by the maximal ideal. That ideal is
nilpotent, and the total space over the local Artinian base is locally
Noetherian by local finite type. Applying `nilpotentBaseAffineness`
makes the total space affine, and its structure morphism between affine
schemes is affine.

This is a derived application of base-change stability and affineness
reflection across the nilpotent base reduction. It supplies the
affineness premise for using existing affine-target constructions on
local Artinian tests in Task 7705.
