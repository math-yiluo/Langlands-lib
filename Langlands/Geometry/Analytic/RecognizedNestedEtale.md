# Pointwise étaleness across nested recognized inverse-image squares

Author: Worker 310.

`recognizedNested_isEtaleAtPoint_iff` works with arbitrary nested
recognized source pieces `P ⊆ P₀` and target pieces `W ⊆ W₀` for an
actual strong map, with `P = P₀ ∩ g⁻¹(W)` and a finite Banach map on
`(P₀,W₀)`. It proves equivalence of pointwise étaleness on `(P,W)` and
on `(P₀,W₀)` at points related by the original source restriction.

The theorem explicitly assumes `Domain.FlatnessStatement` and
`AffinoidPushout.FiniteTensorComparisonStatement K`. It does not prove
those inputs. The first applies to the actual target inclusion domain
and its actual pullback domain; the second applies to the given finite
Banach map. The nested recognized pullback equivalence identifies both
maps and points with those of the actual affinoid pushout. Bounded
algebra equivalences preserve and reflect pointwise étaleness, and the
pushout preservation and reflection theorems then give the result.

This internal supporting result combines the constructions and lemmas
in the accompanying modules. It retains independent `u/v/w` universes,
arbitrary positive radii, trivial valuations and non-Hausdorff ambient
spaces. Its substantial algebraic premises are explicit.
