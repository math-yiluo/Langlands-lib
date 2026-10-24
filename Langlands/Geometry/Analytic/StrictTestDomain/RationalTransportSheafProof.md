# Conditional sheaf comparison for finite rational transport sites

Author: Worker 367. The type-valued proof adapts Worker 61's published
`Langlands.Sheaf.Equivariant.isSheaf_of_isSheaf_inclusion` from
`Langlands/Sheaf/Equivariant/Site.lean`. Worker 36 supplied the rational
normalization interfaces, target statements, and the rational proof route
in this task. Both are credited contributors to this adaptation.

This module proves the unchanged Library proposition
`Langlands.Analytic.StrictTestDomain.RationalTransport.SheafComparisonStatement`.
Its closing theorem is `sheafComparison.{u,v,w}`. Fix a complete ultrametric
normed field `K : Type u` and a presented strict affinoid algebra `P`.
For any category `A : Type v` with morphisms in `Type w` and presheaf
`Q : (RationalTransport K P)ᵒᵖ ⥤ A`, the theorem compares its sheaf condition
for `finiteTopology K P` with the sheaf condition of `inclusion.op ⋙ Q`
for `RationalData.finiteRationalTopology K P`. It also compares the two
actual quotient-algebra presheaves' sheaf conditions.

The first reusable lemma, `isSheaf_of_isSheaf_inclusion`, concerns a
presheaf with values in `Type w` and Mathlib's `Presieve.IsSheaf`.
Let `S` be a covering sieve on a transport object `U`, and let `x` be a
compatible family of sections on `S`. The proof pulls `x` back along
`inclusion` to the ordinary sieve `inclusionSieve S`. The published lemma
`mem_finiteTopology_iff_inclusionSieve` proves this sieve covers in the
ordinary finite rational topology. Mathlib's `functorPullback` preserves
compatibility, so the ordinary sheaf hypothesis gives a section `t` on
`U`, its amalgamation property on ordinary inclusions, and its uniqueness.

To prove amalgamation on an arbitrary labelled arrow `f : V ⟶ U` of `S`,
the proof uses `normalizedInclusion_mem_iff` to put
`inclusion.map (normalizedInclusion f)` in `S`. The ordinary amalgamation
property determines the restriction of `t` to that arrow. The published
factorization is

```
(translationIso f.label V).hom ≫ inclusion.map (normalizedInclusion f) = f.
```

Compatibility of `x`, applied to the identity of `V` and this translation
arrow, relates the section on the normalized inclusion to `x f`. Applying
functoriality to the factorization then proves `Q.map f.op t = x f`.
The Lean proof transports equalities explicitly with `congrArg` and
`Functor.map_comp_apply`; it does not identify distinct presentation
objects or distinct labels. Uniqueness follows by restricting any proposed
transport amalgamation to ordinary inclusions and applying the ordinary
uniqueness assertion.

The second reusable lemma, `isSheaf_finiteTopology_iff`, handles arbitrary
categorical coefficients. The forward implication is the published
continuity instance for `inclusion`, via
`inclusion.op_comp_isSheaf_of_isSheaf`. For the converse, Mathlib defines
`Presheaf.IsSheaf` by requiring the type-valued sheaf condition after
composition with each covariant representable `coyoneda.obj (op E)`.
For every `E : A`, the proof applies the type-valued lemma to that composite.
Functor composition associates definitionally here. No limits,
concreteness, or completeness assumption on `A` is used. The coefficient
object universe `v` and morphism universe `w` remain independent of the
field universe `u` and of one another.

The lemma `algebraPresheaf_isSheaf_iff` specializes this generic equivalence
to the actual `CommAlgCat K`-valued `algebraPresheaf`. It then composes the
equivalence with `Presheaf.isSheaf_of_iso_iff` applied to the published
`inclusionAlgebraPresheafIso`, whose target is
`RationalData.rationalPresheaf K P`. The generic theorem is instantiated
at the universes of this algebra category, independently of the arbitrary
`v` and `w` in the first conjunct. Finally, `sheafComparison` introduces
the parameters of each conjunct of `SheafComparisonStatement` and applies
these two reusable categorical equivalences.

This is a conditional comparison. It proves neither actual presheaf is a
sheaf outright, and does not assume an unconditional analytic gluing or
rational-sheaf theorem. It concerns the restriction of a presheaf that
already has transport maps; it does not construct transport maps for an
arbitrary ordinary sheaf or assert equivalence with the category of all
ordinary sheaves. Objects remain chosen unit-radius rational presentations
over the fixed base algebra. Equal loci do not identify presentations,
and automorphism labels are retained. The proof uses covering sieves
without selecting a point or an element of a cover, so empty covers and
loci remain allowed. It imposes no nontrivial-valuation or nondegenerate-
quotient hypothesis. The setting is the constructed finite rational site,
not the full analytic G-topology, an etale or quasi-etale site, or a
continuous topological-group action.

Provenance is derived categorical infrastructure: Worker 61's published
open-set proof supplies the gluing argument; Worker 36's
`RationalTransportNormalization` and `RationalTransportContinuity` supply
the rational-site factorization, covering comparison, continuity, and
presheaf isomorphism. The proof imports those Library constructions by
Lean name and preserves the target and its imported pairs. It uses
Mathlib's sieve and sheaf APIs at pinned revision
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0. The original
analytic literature cited by the target and normalization modules supplies
the geometric context for those imported definitions; the present proof
makes no additional literature theorem claim.
