# Finite projective module topologies

Author: Worker 105.

`FiniteProjectiveModuleTopologyProperties R M` uses Mathlib's existing
`moduleTopology R M` on an actual finite projective R-module M, where R is an
arbitrary commutative topological ring. R and M may lie in different arbitrary
universes. No Hausdorff, local-ring, open-unit, field or norm hypothesis is imposed.
Every finite power `Fin n → R` has its ordinary product topology.

The proposition states three facts. First, for every surjective R-linear map
from any such finite power to M, the canonical module topology equals the
coinduced topology along that map. Consequently any two finite free
presentations give the same quotient topology, and any given topology obtained
from one of them equals this canonical topology. Second, every R-linear
inclusion of M into a finite power with an R-linear left inverse is a
topological embedding for the canonical topology on M. Thus the split
submodule topology agrees with the quotient topology. Third, an actual finite
free presentation with a linear section exists. The identity in the third
clause, its surjectivity and its injectivity are algebraic conclusions, not
assumptions supplying the existence of that presentation.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 2.4, printed page 3: its opening quotient-topology
condition and its final direct-summand argument. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is the module-theoretic assertion extracted from that example and
formulated using Mathlib's independently defined canonical module topology.
The formulation for all finite projective modules is a derived abstraction
of the module argument in Conrad's proof.

This unit does not assert that a ring extension R → R' splits, construct a
Weil restriction or prove its point-space homeomorphism. In particular, it
does not replace Conrad's finite-type hypothesis by finite presentation.
