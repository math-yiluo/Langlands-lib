# Upper pair coefficient restriction to triple CM kernels

This internal construction restricts the original pair for \(V\leq U\)
to the actual triple common kernels for \(T\leq V\leq U\). It constructs
the map of residual group diagrams and identifies the restricted pair
coefficients with the middle and upper triple coefficients. The original
pair lattice inclusion becomes the original triple upper inclusion.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Arithmetic carriers have
universe zero, and the index category is the full \(\mathbb N^{op}\),
including zero.

## Inputs and original objects

The inputs are the existing central simple unitary datum
`D : CentralSimpleUnitaryData E F A n`, with \(E\) a totally real number
field, \(F\) a totally complex CM number field quadratic over \(E\),
and the compatible \(E,F,\mathbb Q\) algebra structures and scalar towers
on \(A\). The rational algebra \(A\) is finite dimensional.
The coefficient inputs are a number field \(K\), a finite dimensional
\(K\)-vector space \(W\), an algebraic representation \(\rho\) of
`D.rationalInvolution.baseChange K`, a rational finite place \(p\), and a
natural number \(m\neq0\). Write \(R=\texttt{HarrisCoefficientIntegers K p}\).
The levels are actual `SmallCMLevel D` objects, with specified subgroup
inclusions \(h_{TV}:T\leq V\) and \(h_{VU}:V\leq U\).
There is no normality assumption on \(T\) in \(V\) or \(U\).

For \(H=U,V,T\), let \(H_k\) be the original canonical Harris coefficient
kernel at exponent \(k\). The original upper-pair common subgroup is

\[
 P_k=V_k\cap(V\cap U_k).
\]

Its residual group is \(V/(P_k\text{ inside }V)\). The triple subgroup is
the existing literal intersection

\[
 L_k=\bigl(T_k\cap(T\cap U_k)\bigr)\cap(T\cap V_k),
\]

with residual group \(T/(L_k\text{ inside }T)\). These are exactly
`cmHarrisLatticeCommonLevel D ρ p U V hVU m hm` and
`cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm`;
their residual diagrams are `cmHarrisLatticeCommonGroups` and
`cmHarrisTripleCommonGroups`. The imported action-kernel constructions
provide normality inside \(V\) and \(T\) respectively.

The pair own coefficients retain the complete original \(V\)-lattice
coefficient functor; the pair original coefficients retain the complete
original \(U\)-lattice coefficient functor. Their actions factor through
the pair residual groups. The triple middle and upper coefficients retain
these same underlying functors with actions through the triple residual
groups. In particular, all original coefficient quotients by the
exponent ideals and all original reduction maps are preserved.

## The actual upper-pair quotient map

`cmHarrisTripleUpperPairGroupMap` is a natural transformation

\[
 \phi:\texttt{cmHarrisTripleCommonGroups}\longrightarrow
       \texttt{cmHarrisLatticeCommonGroups}(U,V).
\]

At \(k\), it is `QuotientGroup.quotientMapSubgroupOfOfLe` applied to the
existing containment `cmHarrisTripleCommonLevel_le_upperPair` and
\(h_{TV}\). Its representative formula is
\([g]\mapsto[\operatorname{inclusion}_{T,V}(g)]\), proved in
`cmHarrisTripleUpperPairGroupMap_mk`. Naturality follows by induction on
a residual class: both exponent-transition composites are represented
by the same included element of \(V\).

`cmHarrisTripleUpperPairGroupMap_own_app` and
`cmHarrisTripleUpperPairGroupMap_original_app` prove the following
identities of actual quotient homomorphisms:

\[
 T/L_k\longrightarrow V/P_k\longrightarrow V/V_k
 =
 T/L_k\longrightarrow T/(T\cap V_k)\longrightarrow V/V_k,
\]

\[
 T/L_k\longrightarrow V/P_k\longrightarrow V/(V\cap U_k)
       \longrightarrow U/U_k
 =
 T/L_k\longrightarrow T/(T\cap U_k)\longrightarrow U/U_k.
\]

Here every denominator is taken inside the ambient numerator group.
Both proofs use quotient induction and definitional equality on
representatives. The corresponding lemmas without `_app` prove equality
of the complete natural transformations, using natural-transformation
and group-homomorphism extensionality.

## Identity coefficient comparisons and the original inclusion

Let \(\operatorname{res}_{\phi}\) be the published
`EquivariantDiagram.groupRestriction (ModuleCat R) φ`. It retains the
underlying coefficient functor and precomposes its actions with \(\phi\).
`cmHarrisTripleUpperPairOwnCoefficient_action` and
`cmHarrisTripleUpperPairOriginalCoefficient_action` prove equality of
the restricted actions with the triple middle and upper actions,
respectively. Quotient induction reduces both equalities to the same
original representation action on the same included element.

The two constructed equivariant isomorphisms are

\[
 a:\operatorname{res}_{\phi}(\text{pair own})\simeq
        \text{triple middle},\qquad
 b:\operatorname{res}_{\phi}(\text{pair original})\simeq
        \text{triple upper}.
\]

They are `cmHarrisTripleUpperPairOwnCoefficientIso` and
`cmHarrisTripleUpperPairOriginalCoefficientIso`. Their hom and inverse
are the identity natural transformation on the respective complete
original coefficient functor, as the `_hom` and `_inv` projection lemmas
state. The action equalities prove equivariance in both directions;
`EquivariantDiagram.Hom.ext` and category identity laws prove the
inverse laws.

Write \(c_{UV}\) for the original
`cmHarrisLatticeCommonCoefficientInclusion` for \((U,V)\), and \(c^+_{UVT}\)
for `cmHarrisTripleUpperCoefficientInclusion`.
`cmHarrisTripleUpperPairCoefficientInclusion_square` proves

\[
 \operatorname{res}_{\phi}(c_{UV});b_{\rm hom}
   =a_{\rm hom};c^+_{UVT}.
\]

After forgetting actions, restriction retains the original reduced
lattice inclusion and both comparison maps are identities. The triple
upper map has that same underlying original \(V\)-to-\(U\) inclusion,
with its action restricted to \(T\). Extensionality, identity laws and
definitional equality therefore prove the square for the entire
coefficient diagrams. No inverse or injectivity of the reduced lattice
inclusion is asserted.

## Internal provenance and retained scope

The imports supply the actual triple and pair kernels, their quotient
diagrams, original coefficient actions and lattice inclusions, together
with the general group-restriction functor. This file derives a further
quotient map from the proved kernel containment, proves its naturality
and compositions, and constructs the identity comparisons and inclusion
square from the original actions. It introduces no new
external-literature assertion and assumes none of these comparison
outputs.

Geometric pullback-cover comparisons, associated-sheaf inverse-image
coherence, lattice independence, rational adic independence and Hecke
compatibility remain separate obligations. The general arithmetic,
representability, existence and canonical-model obligations of the
containing Harris construction are also retained.
