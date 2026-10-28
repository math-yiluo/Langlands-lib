# Proof of the Noetherian local flatness criterion

`Langlands.Algebra.localFlatnessCriterion.{u,v,w}` proves exactly the published
proposition `Langlands.Algebra.LocalFlatnessCriterionStatement.{u,v,w}`.
The module imports that statement and the three proof modules used in the
assembly. Its theorem has no additional parameters or hypotheses.

Let `R : Type u` and `S : Type v` be commutative Noetherian local rings, with
an `R`-algebra structure on `S` and `IsLocalHom (algebraMap R S)`. Let
`M : Type w` be an additive commutative group with compatible `R`- and
`S`-module structures, `IsScalarTower R S M`, and `Module.Finite S M`.
Write \(\mathfrak m\) for the maximal ideal of \(R\). The hypothesis is
injectivity of
\[
\mathfrak m\otimes_R M\longrightarrow R\otimes_R M,
\]
namely `LinearMap.rTensor M (IsLocalRing.maximalIdeal R).subtype`.
The conclusion is `Module.Flat R M`. The three universes are independent.
The finiteness hypothesis is over \(S\), with no finiteness over \(R\),
nonzero-module, finite-type, finite-presentation, or field hypothesis.

## Implemented assembly

The private helper `maximalIdeal_lTensor_injective` applies the reverse
implication of Mathlib's `LinearMap.lTensor_inj_iff_rTensor_inj` to the
maximal-ideal inclusion. Tensor commutativity therefore gives injectivity
of \(M\otimes_R\mathfrak m\to M\otimes_R R\). The helper needs only a
commutative local ring and an arbitrary module.

The published theorem `Langlands.Algebra.finiteColengthTensorInjectivity`,
from `Langlands.Algebra.FiniteColengthTensorInjectivityProof`, applies to
this left-tensor hypothesis. It proves injectivity of
\(M\otimes_R J\to M\otimes_R R\) whenever \(\mathfrak m^k\subseteq J\).
Its Noetherian and local hypotheses are exactly those supplied for \(R\).

The resulting family of injections is the premise of the published
`Langlands.Algebra.artinReesTensorKernelBound`, from
`Langlands.Algebra.ArtinReesTensorKernelBoundProof`, with its chosen ideal
set to \(\mathfrak m\). It gives, for every ideal \(a\subseteq R\) and
every \(n\in\mathbb N\),
\[
\ker(M\otimes_R a\longrightarrow M\otimes_R R)
 \subseteq \mathfrak m^n(M\otimes_R a).
\]
This proof imports `Langlands.Algebra.IdealTensorIntersectionKernelProof`
and uses `idealTensorIntersectionKernel` for the intersection/sum tensor
diagram. Artin–Rees is applied to the ideal \(a\) inside the finite
\(R\)-module \(R\).

The second private helper, `maximalIdeal_map_le_jacobson`, composes
`IsLocalRing.map_maximalIdeal_le (algebraMap R S)` with
`IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S)`. The local-map
instance and the local-ring structures give
\[
\mathfrak m S\subseteq\mathfrak m_S\subseteq\operatorname{Jac}(S).
\]
This helper needs neither Noetherianity nor module finiteness.

Finally, `Langlands.Algebra.idealTensorKernelSeparation`, imported from
`Langlands.Algebra.IdealTensorKernelSeparationProof`, is applied to
\(R,S,M,\mathfrak m\), that Jacobson containment, and the kernel bounds.
Its conclusion is precisely `Module.Flat R M`. Internally this published
result makes \(M\otimes_R a\) finite over \(S\), transports the power
bounds to \((\mathfrak mS)^n\), and uses Krull intersection over \(S\)
to kill the kernel. It then applies the ideal-tensor criterion for flatness.
All its ring, module, scalar-tower and finiteness hypotheses are supplied
by the target. The closing Lean term supplies each premise with the
preceding proved result; no kernel bound or flatness criterion remains
as an assumption.

## Sources and provenance

The mathematical route is the proof of Stacks Project Lemma 10.99.7,
tag [00MK](https://stacks.math.columbia.edu/tag/00MK), with its
finite-colength step supported by Lemma 10.99.6,
tag [00MJ](https://stacks.math.columbia.edu/tag/00MJ). The original was
read in registered source `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
files `00MK.html` and `00MD.html`, at those statements and proofs.
The target statement's Markdown explains its tensor formulation of the
source's Tor premise. The implemented prerequisites work directly with
tensor products. The final separation step uses Krull intersection rather
than the source's faithfully flat completion argument.

The retained current-page check is registered as
`stacks-flatness-00mk-00mj-current-2026-10-26`, content SHA256
`867cdedaa7867ff53170db88408b2ad27481210df67727e5af2d3836ff0e5acb`.
A bounded recheck of the official 00MK and 00MJ pages on 28 October 2026
found the same mathematical passages and zero comments on both pages.
No source-specific errata file was found in project or Library notes.

Worker 439 wrote this assembly from the current Library interfaces and
Mathlib. The external feasibility audit
`notes/reuse/anthropic-local-flatness-audit.md` was consulted during
planning. This module includes no extracted external Lean code; the
prerequisite proof companions record their own source attribution and
implementation choices. The two private adapters are direct applications
of the named Mathlib results. The final theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`.
