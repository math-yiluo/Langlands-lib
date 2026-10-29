# Actual opposite-to-upper reversal for refined Jacquet exponents

Author: Worker 158, adapting the published reversal constructions of Worker 23.

This internal adapter uses the block reversal constructions of Worker 23's
published `ProductLeviDualOppositeAdapter`. It uses the other orientation of
the proved radical conjugation formula to start from the original opposite
quotient. It introduces no analytic criterion.

For an outer shape `C` and inner refinement `D`, write `D'` for
`reverseRefinement C D`, `w` for `reverseWeyl C D F.Carrier`, and `e` for
`reverseLabel C D`, from flattened labels of `D'` to those of `D`.
`conj_mem_refinedOppositeUnipotent_iff` says that `w g w⁻¹` belongs to
the original opposite radical exactly when `g` belongs to the reversed
upper radical. Componentwise it is
`reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff`.

`toUpper` sends an opposite class `[v]` to the upper class `[ρ(w⁻¹)v]`.
The companion `fromUpper` uses `ρ(w)`. Their composition is the identity
on the original opposite quotient by the published coinvariant translation
identity. In particular, `toUpper` sends nonzero vectors to nonzero vectors.

`refinedLeviInverseHalfModulus_reverse` inverts the existing full-modulus
reversal equality and takes positive square roots. It identifies the
inverse half modulus of the reversed upper quotient with the positive
half modulus of the original opposite quotient, on scalars relabelled by
`e⁻¹`. Therefore `toUpper_normalizedRefinedOppositeJacquet` intertwines
the actual normalized actions. Its proof checks quotient representatives
and uses `w m'(c) w⁻¹ = m_D(c ∘ e⁻¹)`.

`isGeneralizedEigencharacter_toUpper` transports a nonzero common-power
generalized eigenvector along this injective map. The character becomes
`c ↦ χ(c ∘ e⁻¹)` and the same power kills every character defect. This
proves occurrence on the actual reversed upper quotient, for arbitrary
independent field and carrier universes.

`isOpen_ker_relabel` pulls back the open kernel through the continuous
coordinate permutation `c ↦ c ∘ e⁻¹`, with `T.topology` installed.
`isRealPartOf_relabel` transports a supplied real part `x` to `x ∘ e`.
Its proof evaluates the original real-part identity at `c ∘ e⁻¹` and
reindexes the finite product by `e`; it makes no choice of real part.

`positiveRootCone_neg_of_reverse` is finite coordinate algebra. The
positive-root-cone pairing criterion transforms a nonconstant monotone
integer vector `h` to the nonconstant monotone vector `i ↦ -h(i.rev)`.
Reindexing the total and pairing by `Fin.revPerm` proves that a cone for
`i ↦ x(i.rev)` gives a cone for `i ↦ -x(i)`, including empty and singleton
index types.

`blockwiseCone_neg_of_reverse` applies this numerical lemma separately
to each original block. The formula `reverseLabel_apply` identifies the
relabelled coordinates of the reversed refinement with the reversed inner
positions of the original refinement. Consequently, positive cones for
`x ∘ e` on the reversed refinement imply positive cones for `-x` on the
original refinement. This preserves every separate block total and handles
singleton refinements without an exceptional branch. No fine-block size
factors enter any coordinate.

All content here is an internal algebraic and topological adapter derived
from published quotient translation, reversal, normalization, and finite
pairing identities. It neither assumes nor proves square-integrability
necessity. The intended consumer combines an independently proved upper
cone criterion with this transport. No classification or support theorem
is used in the implemented proofs.
