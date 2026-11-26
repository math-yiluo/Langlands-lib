# Finite span from a common center ideal and parabolic finiteness

`Langlands.Global.InducedConvolutionUniformCenterIdealStatement` concerns a continuous compactly
supported kernel and a smooth inducing function that is left invariant under `U(𝔸)` and finite
under the ambient enveloping center. It asks for one ideal of finite complex codimension that
annihilates every plot-smooth infinite slice of the integrated induced action, for every complex
parameter. The underlying data are a connected reductive adelic group, a parabolic with a
geometric radical and a complementary rational Levi, a maximal Iwasawa compact, and the actual
archimedean differential calculus.

`InducedConvolutionFiniteSpanReductionStatement` is the implication from this common-center
assertion and `ParabolicHarishChandraFinitenessStatement` to the exact
`InducedConvolutionFiniteSpanStatement`. The theorem `inducedConvolutionFiniteSpanReduction`
proves the implication.

## Implemented proof

The parabolic root presentation supplies the parabolic and rational Levi properties. The
multiplication isomorphism for the supplied geometric radical follows from
`ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical`. The compact data of the
kernel give a single open right level and a finite-dimensional space of compact coefficient
functions for the entire family.

Each convolution value is left invariant under the parabolic quotient subgroup and transforms
by the half-modulus on the split component. It is continuous, plot-smooth on the infinite
slices, smooth at the finite places under the common level, finite under the infinite compact
and of moderate growth. The shared annihilator supplies its center finiteness. The weighted
square-integrability theorem now places the value in `A²_P`.

The family satisfies the parabolic finiteness hypotheses for the common ideal, finite level and
compact coefficient space. Harish-Chandra finiteness bounds the span of all such functions, and
hence the span of this family. The rational character module of the parabolic is finite over `ℤ`,
so the complex parameter space is finite-dimensional. The entire-coefficient theorem selects a
basis from the actual convolution values and reconstructs each value with entire coefficients.
Each selected basis element therefore also belongs to `A²_P`.

## Provenance

The implication is the assembly in the derivation of `InducedConvolutionFiniteSpanStatement`.
The center-action comparison and the parabolic finiteness theorem come from C. Mœglin and
J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*, I.2.17, printed pp. 37–38
(PDF pp. 20–21 of `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`), registered as
`moeglin-waldspurger-1995-spectral-decomposition`, folder SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`, chapter SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`. The center input is the
consequence in which the twist and its inverse cancel in the left Levi action, as described
in the finite-span statement's derivation. The theorem here takes that common-ideal assertion
and the finiteness theorem as premises and implements the other steps for the actual operator.
