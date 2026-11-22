# Composition of finite Cartier pullback comparisons

For a tower of commutative rings `R → S → T`, `affineBaseChangeCompIso`
compares direct pullback to `T` with successive pullback first to `S` and
then to `T`. It uses the composition comparison for scheme pullbacks and
lifts it to commutative group schemes. `schemeDualBaseChangeIso_comp`
proves the resulting coherence for a finite locally free commutative
group scheme `G` over `Spec R`, with finiteness, flatness and local finite
presentation expressed as hypotheses on its structure morphism. The
successive path compares the pullbacks of the original dual and then
applies the two Cartier pullback comparisons. The direct path applies
the Cartier comparison over `T` and then the Cartier dual of the inverse
composition comparison for `G`.

The proof evaluates both paths on an arbitrary test scheme and primal
point. The two comparisons along the successive path preserve
evaluation as a global unit by the pullback adjunction. The comparison
between the two induced tests over `Spec R` has identity underlying
scheme map, so restriction across it leaves the unit unchanged. For the
direct path, adjointness moves the last dual map to the primal factor.
The pullback adjunction identifies the resulting primal and dual points
with those from the successive path. Equality of the evaluations on all
restrictions then determines equality of the dual points and the two
group-scheme morphisms.

This is a derived compatibility of the Library's finite Cartier
comparison. It supplies the finite-level composition step for the
split product and tautological pairing in Rapoport–Zink (1996), §6.43,
printed p. 309 (PDF p. 321), preceding (6.17).
