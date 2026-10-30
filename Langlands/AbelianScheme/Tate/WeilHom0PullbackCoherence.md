# Coherence of actual rational dual pullback

Worker 142. This derived unit gives algebraic coherence laws for the actual
`rationalDualPullbackHom0` introduced in `WeilHom0Pullback`. With the constructed
contravariant rational dual, this is the composite `f^vee lamB f` in the actual
rational Hom groups of abelian schemes over one base. The endpoint dual schemes,
their geometry, Poincare inverse evaluations, tensor coherence, Picard pullback
and dual-map additivity remain explicit. Arbitrary rational dual-valued maps
are allowed; no positivity or polarization assertion is made.

For fixed `f`, `rationalDualPullbackHom0Linear` bundles pullback as a rational
linear map in `lamB`, using the existing two rational-linear composition maps.
Its application is the existing pullback, and linearity gives the scalar law.
The identity pullback law uses `dualHom0_id` and the two identity laws of
rational composition; the identity has multiplier one. The composition law uses `dualHom0_comp` and associativity:
pullback by `f` after pullback by `g` is pullback by the composite that first
applies `f` and then `g`. The dual and inverse-evaluation data at the intermediate
endpoint are the same throughout this equality.

If `f^vee lamB f = q lamA` and `g^vee lamC g = r lamB`, the composite has
multiplier `q*r`. The proof applies pullback composition, rational linearity
in the dual-valued map and multiplication of rational scalars. For a rational
isogeny, pulling back by its inverse after pulling back by it is the identity;
this follows from the composition law and the actual inverse equation in the
rational category. Applying that identity to a multiplier equation and scaling
by the inverse rational unit gives the inverse multiplier equation. These laws
use no Weil pairing compatibility theorem and impose no torsion assumptions.

The mathematical provenance is the specialization of contravariant dual-map
functoriality and bilinear rational composition to the already constructed
pullback. Harris--Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 and Section III.1, p.91, uses invertible rational
homomorphisms and compatibility of dual-valued maps up to rational scalar in
the PEL isogeny relation. The present laws supply its algebraic identity,
composition and symmetry mechanisms; they do not assert positivity, frame
existence, nondegeneracy, topology, or coherence on level sets. The proof is the
Library composition calculation described above, rather than an additional
geometric existence theorem attributed to that passage. No source-specific
errata note was found in the consulted project notes.
