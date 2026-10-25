# Finite Hecke operators on actual automorphic forms

This construction integrates the published smooth finite adelic right action on
`AutomorphicForms K n`, and its actual central-character and cusp subspaces.
The coefficient field is complex, K is a number field in an arbitrary universe,
and n is any natural rank, including zero. The group is the existing matrix unit
group over the actual finite restricted-product adele ring, with its existing
topology, a Borel measurable structure, and a supplied left Haar measure μ.
No existence or normalization of Haar measure is asserted in this module.

`automorphicHeckeAction` is a nonunital complex algebra homomorphism from the
actual measure-indexed convolution algebra `HeckeAlgebra μ` to the endomorphisms
of the concrete form space. It reuses `Hecke.heckeAction`, constructed by a
finite-fiber algebraic integral on the smooth representation. In particular,
its algebra laws follow from the published integration and convolution proofs;
they are not input certificates. The carrier has no imposed norm or topology.
`automorphicEvaluation` is an ordinary algebraic linear functional. Scalarizing
the actual integral with this functional proves

`(R(h)f)(x) = ∫ d, h(d) f(x · ofFinite(d)) dμ(d)`.

The right translation uses d itself, without inversion. The underlying Hecke
multiplication is left-Haar convolution `h₁*h₂(d) = ∫ t, h₁(t) h₂(t⁻¹d) dμ(t)`.
Smoothness and compact support make the weighted orbit map a finite-image simple
function of finite-measure support, as proved by the reused generic construction.
Thus the displayed scalar formula computes the actual algebraic operator.

For a compact open subgroup L, `automorphicHeckeCornerAction` is the genuine
unital action of the published corner algebra on the existing fixed-vector
subspace. `mem_automorphicFixedVectors` identifies that subspace with the
previously defined finite-level condition on actual functions. The normalized
indicator `e_L = μ(L)⁻¹ 1_L` fixes a form exactly when it has level L. One direction
uses the generic range theorem for averaging; the other uses its identity action
on fixed vectors. Every automorphic form has a compact open finite level by the
published form-space construction, so some such indicator fixes it. Consequently
the Hecke action is nondegenerate: a form annihilated by all Hecke operators is
zero. Neither conclusion assumes admissibility or finite-dimensionality of a
fixed-vector space.

For every ambient invariant subrepresentation S, `restrictedAutomorphicHeckeAction`
acts on the actual inverse-image subspace `RestrictedAutomorphicForms K n S`.
The inclusion into `AutomorphicForms` is injective and intertwines these operators
by naturality of the algebraic integral. This proves the same evaluation formula,
local-unit existence and nondegeneracy on the restriction. The named central-character,
cuspidal, and simultaneous actions specialize this construction. The cusp
specializations retain the explicit `CompactSpace (AdeleQuotient K)` hypothesis
used by the existing normalized constant terms. The central character remains an
arbitrary continuous character of the actual idele-class group into complex units,
with the already published positive-character convention and no unitarity
requirement. The definition acts on these exact subspaces, so finite Hecke
operators preserve all their membership conditions.

The source is Borel and Jacquet, *Automorphic forms and automorphic
representations* (1979), section 3.2, printed page 194 (one-based PDF page 189),
and sections 4.4--4.6, printed page 196 (PDF page 191), registered as
`borel-jacquet-1979-automorphic`. Section 3.2 identifies the finite Hecke algebra
and normalized finite-level idempotents; sections 4.4--4.6 place the action on
actual automorphic and cusp forms. This module is a derived specialization of
those conventions using the published generic finite-fiber Hecke construction,
not a new proof of the analytic assertions in 4.5.

This supplies only the finite Hecke action. It does not construct the infinite
Hecke algebra or a full (g,K) category, prove admissibility, construct irreducible
automorphic subquotients or local components, or assert existence of a nonzero
form. No such consequence is inferred from nondegeneracy of the operator action.

The five local additive-group instances have explicit module-specific names:
`finiteHeckeRationalAddCommGroup`, `finiteHeckeContinuousAddCommGroup`,
`finiteHeckeSmoothAddCommGroup`, `finiteHeckeFormsAddCommGroup`, and
`finiteHeckeRestrictedFormsAddCommGroup`. This implementation-only correction
avoids generated declaration-name collisions with `OperatorCore` when
`OperatorEquivalence` and `PresentedSpectralSystem` are imported together.
The instances remain local and each retains its original type and
`Submodule.addCommGroup _` body. All mathematical definitions, theorem statements,
proof bodies, hypotheses, normalizations, and public mathematical names are
unchanged.
