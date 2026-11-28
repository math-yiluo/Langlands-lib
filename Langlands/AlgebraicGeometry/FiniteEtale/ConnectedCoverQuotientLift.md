# Lifting quotient values through a connected pullback cover

`ConnectedCoverQuotientLiftStatement` takes a morphism \(f:S'\to S\) with connected, locally
Noetherian source and a geometric point \(t\) of \(S'\) over an algebraically closed field.
Write \(s=f\circ t\) and choose a lift \(x\) of \(s\) to a finite étale cover \(Y\to S\).
Suppose that \(Y\times_S S'\) is connected and a group homomorphism \(\rho\) from the pointed
fundamental group at \(s\) kills the image of the fundamental group of \(Y\) at \(x\). Then
\(\rho\circ f_*\) has the same image as \(\rho\). The locally Noetherian hypothesis comes from
the construction of the geometric Galois fibre functor for \(S'\).

## Lean proof

For a connected, locally Noetherian base and a geometric point over an algebraically closed
field, `cover_isConnected_of_connectedSpace` uses a supplied lift into the connected cover to
rule out the initial object. A noninitial subcover has a nonempty geometric fibre. Its image in the connected cover is clopen
and nonempty, so it is surjective. A surjective finite étale monomorphism is an isomorphism.

`connectedCoverQuotientLift` transports the specified lift and its translate to the geometric
fibre of the pulled-back cover. Connectedness gives transitivity of the new fundamental group
on that fibre. An element carrying one lift to the other maps to an element whose action agrees
with the original action at the specified lift. Their difference lies in the point stabilizer,
which is the image of the pointed fundamental group of the cover. The given representation kills
that image, so the two elements have the same value under the representation.

## Source

This is a consequence of the equivalence between finite étale covers and finite fundamental
group sets and its compatibility with pullback. See the Stacks Project, *Fundamental Groups of
Schemes*, Theorem 58.6.2 (tag `0BND`). The proof uses the actual fibre functor and the stabilizer
image in `CoverStabilizerLift`.
