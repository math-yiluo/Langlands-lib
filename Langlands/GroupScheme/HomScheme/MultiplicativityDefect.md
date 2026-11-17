# Correcting multiplicativity defects and comparing homomorphisms

For arbitrary group schemes `H` and `G` over `S` and any map `s : H.X → G.X` of the underlying schemes over `S`, `multiplicationDefect s` is an actual morphism from the product of the source with itself to the target. On all test-valued points it is

`δ(h,k) = s(h)s(k)s(hk)⁻¹`.

`multiplicationDefect_cocycle` proves the associativity identity

`δ(h,k)δ(hk,l) = s(h)δ(k,l)s(h)⁻¹δ(h,kl)`.

No commutativity assumption on the target or a kernel is used. When the defect is identified with values in an abelian infinitesimal kernel and conjugation factors through a group action, this is the usual degree-two cocycle equation. This module does not construct that identification.

For a regular correction map `b : H.X → G.X`, `correctedSchemeMap s b` has values `b(h)⁻¹s(h)`. `IsDefectCorrection s b` is the explicit equation

`δ(h,k)b(hk) = s(h)b(k)s(h)⁻¹b(h)`

on every test scheme. A direct group calculation proves that this equation makes the corrected map multiplicative. `correctedHom` then constructs an actual group-scheme homomorphism with those pointwise values, using the Library's group-valued Yoneda construction. `comp_correctedHom` verifies the values on all tests. Since a multiplicative map between groups preserves the identity, no separate normalization hypothesis is required.

For actual homomorphisms `f, f′ : H → G`, `homomorphismDifference f f′` is the actual regular map with values `f′(h)f(h)⁻¹`. It satisfies the crossed one-cocycle identity for conjugation through `f`. The theorem `homomorphism_eq_conjugate_of_difference` proves that a base-point coboundary formula for this difference gives the actual group-scheme equality `f′ = f ≫ innerIso(g).hom`.

There are no smoothness, affineness, flatness, multiplicative-type or nilpotence assumptions in these constructions and group identities. The module proves neither the existence of a scheme-map lift nor the existence of a correction or conjugating point. Those are the geometric and cohomological inputs to the deformation argument.

Provenance: these are derived actual-morphism constructions for the elementary defect calculations in Conrad, *Reductive group schemes* (2014), Proposition B.2.5 and its proof, p.286. The source uses the inverse defect `s(hk)s(k)⁻¹s(h)⁻¹`; our convention is its inverse, hence its negative in an additive abelian kernel. The correction equation and inverse correction map above are consistent with the convention implemented here. The Lean proof establishes the group identities directly, independently of cohomology or the literature proof.
