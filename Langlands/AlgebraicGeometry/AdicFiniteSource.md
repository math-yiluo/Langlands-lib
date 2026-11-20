# Adic effectivity for maps from spectra of finite algebras

`AdicFiniteAlgebraSourceStatement.{u}` is the finite affine source form of
SGA 3, Exposé XV, Corollary 1.5, Gille–Polo recomposition, PDF p. 4.
For an algebra finite over a complete noetherian local ring, compatible
maps from the spectra of its quotients by powers of the extended maximal
ideal to any scheme lift to a unique map from its spectrum. These
quotients compute the pullbacks by the adic thickenings of the base.

The proof first works over a noetherian ring complete for an ideal with
Artinian quotient. The closed points of the quotient spectrum have clopen
singleton neighbourhoods. Hensel's lemma lifts their idempotents to the
complete ring. The lifted idempotents give pairwise disjoint clopen
affine pieces covering the full source, since every prime specialises to a
point of the first quotient. On each piece, all levels of the compatible
system land in one affine chart of the target. Applying affine adic point
effectivity on these pieces and gluing gives the lift. The same chartwise
comparison proves uniqueness. A finite algebra over a complete noetherian
local ring is complete for the extended maximal ideal and has Artinian
quotient, so the general comparison applies.

The quotient maps used on the affine charts come from `AdicQuotientBaseChange`.
