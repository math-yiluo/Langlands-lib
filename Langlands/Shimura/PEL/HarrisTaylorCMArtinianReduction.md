# Reduction of division-case Artinian class lifting to geometric lifting

`DivisionCMArtinianLiftingReductionStatement` takes the published
`DivisionCMPolarizedActionArtinianLiftingStatement` as its premise and gives the
published `DivisionCMArtinianLiftingStatement`. The conclusion concerns the
actual restriction map of `smallLevelClassPresheafTower` for each small Harris
level and each elementary Artinian test over the CM test base field `F`.

The proof first obtains an upper positive polarized action on the thicker
spectrum with an equivariant rational isometry after restriction. The
geometric bridge reflects the normalized determinant and dimension
conditions along this isometry. The surjection of local Artinian rings gives
surjectivity on the pointed monodromy groups at a geometric point of the
thinner spectrum and its pushforward. The pointed class reduction uses these
inputs to lift an actual class representative together with its level orbit.

Evaluation identifies the unpointed class towers with the pointed towers at
the chosen geometric points. The proof uses the equality of structural maps
over `Spec F` to align the pointed restriction and uses the evaluation
square to obtain surjectivity on unpointed classes. Each local Artinian
spectrum has a single connected component. Its component inclusion induces
an isomorphism of connected admissible bases. The square for these inclusions
and the test morphism compares the connected restriction with the
componentwise restriction, and evaluation on the unique component gives the
desired lift in the presheaf.

This internal reduction combines the published normalization, monodromy,
and class comparison results with the pointed class lifting argument.
