# Quadratic patching from geometric Frobenius polynomials

`Langlands.GaloisRepresentation.quadraticFrobeniusPatching` proves
`Langlands.GaloisRepresentation.QuadraticFrobeniusPatchingStatement`.
The argument formalizes the Frobenius comparisons and the split-place
recovery in Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties*, Theorem VII.1.9, printed pp. 230–231. It uses the abstract
quadratic patching statement, based on Sørensen, §1, Lemma 1, as the
supplied premise. [Frobenius patching statement](QuadraticFrobeniusPatchingStatement.md), [abstract patching statement](QuadraticPatchingStatement.md)

For an auxiliary field \(N\) and an \(F\)-automorphism of \(N\), the
automorphism pullback satisfies the same Euler polynomial formula as \(R_N\)
on a cofinite set of places of \(N\). The completion isomorphism transports the
local action, and the residue degree over \(F\) is preserved. Both
representations are semisimple. The common polynomials give the intertwiner
required for Galois invariance. [Arithmetic transport](QuadraticFrobeniusPatching/Arithmetic.md), [character comparison](QuadraticFrobeniusPatching/Character.md)

For auxiliaries \(N\) and \(M\), the proof uses their actual inclusions into
their compositum. The compositum is Galois over each factor, so both
restrictions are semisimple. At a place \(z\) of the compositum above \(v\)
of \(F\), each transported formula gives the reverse of the root-power
polynomial for \(P_v\) with exponent \(f(z/v)\). The proof intersects the two
cofinite sets on the compositum for this pair and uses density and character
rigidity to produce the required intertwiner.

Applying the abstract premise to these intertwiners gives the rank-\(n\)
semisimple patch and its restriction equivalence for each auxiliary field.
At a specified completely split place \(v\), that equivalence gives the
auxiliary Euler polynomial for the restriction of the patch at the specified
place above \(v\). The degree-one completion isomorphism descends this
polynomial and unramifiedness to the patch at \(v\). This last step uses the
individual matching hypothesis at the specified place.
