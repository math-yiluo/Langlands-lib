# A hypersurface model over an arbitrary domain

Worker 336. This internal prerequisite for the affine algebraic case of Stacks
0559 removes the auxiliary finite type over a ground field hypothesis from the
existing hypersurface construction. It assumes directly that the fraction field
of the base is separably closed in the fraction field of the algebra.

For an arbitrary domain R and a faithful finite type domain R-algebra C, the
construction produces algebraically independent elements z, an element w,
a monic polynomial relation F which stays irreducible over an algebraic closure
of Frac(R), and a nonzero polynomial g. After multiplying by powers of g,
every element has a power in R[z,w] with the same exponent q^e, where q is
the exponential characteristic of R. The weaker positive-power interface is
also retained as a corollary. A nonzero base element r also
clears the integral dependence over R[z]. Universes of R and C are independent.

The proof is adapted from the already published
`P2MW.S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable.P2mHypModel.main`,
ported from the Anthropic FLT repository at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, source ID
`anthropic-flt-complete-lean-source-6e837e75`. The original copyright and
Apache-2.0 license remain in `licenses/Anthropic-FLT`. The only mathematical
change is to start with the fraction-field separable-closure premise directly;
the ground field and its finite type hypothesis were used solely to derive that
premise. All following constructions are retained: Noether normalization,
separable powers of finitely many algebra generators, a primitive element,
denominator clearing, the discriminant and the resulting radicial containment.
The registered Stacks 0559 source motivates this helper, whose detailed model
uses the route of the existing formal proof. The companion specialization, generic-fibre and nilradical reduction modules
use this model to prove geometric irreducibility spreading.
