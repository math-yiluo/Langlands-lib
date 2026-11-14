# Spectral character units and algebraic boundedness of tori

Worker 336. This internal helper for Task 6432 isolates the torus part of the
norm-one boundedness argument. Its source motivation is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 2.5.8, printed pages
88–89 / PDF pages 119–120. The precise spectral formulation below is derived
content. It is not asserted to be a verbatim statement of that proposition.
The source's November 2024 corrections to the sign of the valuation homomorphism
do not change its kernel.

Let \(F\) be a complete nontrivially normed ultrametric field and \(K/F\) an
algebraic field extension, all in an arbitrary common universe. The definition
`spectralCharacterUnitLocus F K T` consists of the actual rational points \(p\)
of a group scheme \(T/K\) for which every rational character \(\chi\) satisfies
\(v_{\mathrm{sp},F,K}(\chi(p))=1\). Here character evaluation is the existing
evaluation into \(K^\times\), and `spectralValuation` is the multiplicative
spectral valuation supplied by the complete field \(F\).

The theorem `isAlgebraicallyBounded_spectralCharacterUnitLocus` proves that this
set is algebraically bounded when \(T\) is an actual torus. Its interface
explicitly assumes that the underlying scheme of \(T\) is affine. Boundedness
uses the valuative relation `ValuativeRel.ofValuation (spectralValuation F K)`:
for each actual global regular function on \(T\), there is a nonzero element
of \(K\) bounding all its values on the locus. No completeness, topology,
discreteness or residue-field hypothesis is placed on \(K\).

For a finite Galois extension \(E/K\) in the algebraic tower \(E/K/F\), the first
auxiliary theorem identifies the spectral valuation of the relative field norm
with the spectral valuation of the input raised to the number of Galois
automorphisms. The proof uses the product formula for the field norm,
multiplicativity of the spectral norm, invariance under each automorphism
restricted to \(F\), and equality of spectral norms along algebraic towers.
Since the nonnegative value group has no nontrivial finite-order elements, a
relative norm of valuation one has valuation-one input. The existing
`normCharacter_eval` identity then proves that every character over \(E\)
has a unit-valued evaluation on scalar extensions of points in the defined
locus.

For the boundedness theorem, choose a finite Galois splitting field of \(T\).
The preceding character calculation makes every split coordinate a unit on
the image of the locus. The published unit-coordinate helper bounds that image
in the standard split torus. The splitting isomorphism is a closed immersion,
so boundedness reflects to the base-changed torus. Pulling a regular function
up to that torus gives a bound \(c\in E\). Choose \(b\in F\) with
\(\lVert b\rVert>v_{\mathrm{sp},F,E}(c)\); it is nonzero. The existing
regular-function evaluation formula for rational scalar extension, together
with spectral tower compatibility and extension of the norm on \(F\), shows
that the image of \(b\) in \(K\) bounds the original function.

This helper proves no assertion about the structure of a reductive
centralizer. In particular, applying it to the centralizer in Task 6432 still
requires a proof that that centralizer is a torus and a comparison with the
task's prescribed character kernel and valuative relation.
