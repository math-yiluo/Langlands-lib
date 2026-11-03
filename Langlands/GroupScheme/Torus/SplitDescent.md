# Descent of split tori along a section

Author: Worker 1326.

This is an internal consequence of the published base-change coherence
isomorphisms and `splitTorus.baseChangeIso`, together with Mathlib's theorem
that an algebraic field extension of an algebraically closed field has a
bijective structure map. It makes no additional literature assertion.

For any schemes `S` and `S'` in universe `u`, suppose that `b : S' ⟶ S`
admits a section `a : S ⟶ S'`, with `a ≫ b = 𝟙 S`.
The construction `baseChangeSectionIso` identifies successive pullbacks
`(G_b)_a` and `G` as actual group schemes. It is the composite of the inverse
composition comparison, transport across the section equation, and the
identity comparison.

Given an actual isomorphism `G_b ≅ splitTorus S' I` for any finite index
type `I : Type u`, `splitTorus.isoOfBaseChangeSection` constructs
`G ≅ splitTorus S I`. It pulls back the given isomorphism along `a` and
composes with the two comparison isomorphisms. Consequently
`IsSplitTorus.of_baseChange_of_section` proves descent of `IsSplitTorus`
under this section hypothesis, and
`isSplitTorus_baseChange_iff_of_section` combines descent with the published
preservation theorem. An isomorphism of base schemes has its inverse as a
section, giving `IsSplitTorus.of_baseChange_of_isIso`.

Let `k` be an algebraically closed field and let `K / k` be an algebraic
field extension, both in arbitrary universe `u`. Mathlib's
`IsAlgClosed.algebraMap_bijective_of_isIntegral` shows that `k → K` is
bijective. The induced `Spec K ⟶ Spec k` is an isomorphism, so
`IsSplitTorus.of_baseChange_of_isAlgebraic` descends splitness of any actual
group scheme from `K` to `k`. The final equivalence states preservation and
reflection under this algebraic extension.

The algebraicity hypothesis is essential to the implemented route. The
Library's `IsTorus` definition supplies a splitting extension with no
algebraicity assumption. This module does not prove
`IsTorus G → IsSplitTorus G` over an algebraically closed field, finite
Galois splitting of arbitrary tori, or unrestricted dynamic-centralizer
reductivity. It supplies the final descent step once an algebraic splitting
extension has actually been constructed.
