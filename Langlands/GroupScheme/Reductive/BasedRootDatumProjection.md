# Multiplicative based representatives modulo the full integral Weyl group

For a supplied complete `SplitPinning p` of an actual affine group scheme over
any field `k : Type u`, `SplitPinning.basedRootDatumProjection` constructs

`p.rootDatum.Aut →* p.basedRootDatumAut`.

Here the source acts on the entire integral character and cocharacter lattices,
and the target is the subgroup preserving the chosen simple-root support. For
every automorphism `δ`, the construction satisfies

`(p.basedRootDatumProjection δ).val * δ⁻¹ ∈ p.rootDatum.weylGroup`.

The based representative is unique. The projection is the identity on based
automorphisms, and its kernel is exactly the full integral Weyl subgroup. The
lemma `exists_weyl_mul_eq_basedRootDatumProjection` expresses the same correction
as an actual element `w` of that subgroup with `w.val * δ` equal to the projected
automorphism. Composing the projection with the existing pinned lift gives
`rootDatumAutPinnedLift`, a homomorphism to actual automorphisms of the field
group scheme.

The proof is internal and derives these constructions from the imported
chamber, actual Weyl-action and complete pinned-isomorphism results.

1. The closed split maximal torus has finite full actual normalizer image by
   `splitTorusWeylImageFinite`; connected reductivity supplies the smoothness and
   finite-type hypotheses. `IsRootDatumOf.abstractWeylImage_le` embeds the
   abstract Weyl weight image there. Faithfulness of `Equiv.weightHom` then
   proves finiteness of the full root-datum Weyl group.
2. Apply `RootDatumBasedCorrection.exists_positive_correction` with zero fixed
   coweight and the pinning's chosen regular positive cocharacter. Its zero-root
   reflection subgroup is contained in the full Weyl group. The resulting
   positivity equivalence agrees with positivity of the chosen base. Positive
   roots characterize their indecomposable roots, so
   `Base.mem_support_equiv_iff_of_isPos` gives preservation of simple support.
3. A based Weyl element preserves positive roots, as follows by lifting it to
   the complete pinned isomorphism and applying `Iso.isPos_iff`. Realize its
   full weight action by an actual normalizing point. The published
   `hasTrivialPositiveRootStabilizer` makes its actual Weyl quotient class the
   identity. Applying the full character action and then faithfulness of the
   root-datum weight representation makes the root-datum automorphism itself
   the identity. This argument retains central lattice directions and includes
   the case of an empty root system.
4. Conjugating a root reflection by any root-datum automorphism gives the
   reflection at the transported root; this follows from full weight
   faithfulness and `Equiv.weightEquiv_reflection`. Induction through Weyl
   generators gives stability under conjugation. Two based representatives in
   the same left Weyl coset differ by a based Weyl element, so step 3 proves
   their equality.
5. Choose the unique based representative of each automorphism. For inputs
   `δ, ε` and their representatives `θ, φ`, the correction of their product is
   `(θ * δ⁻¹) * (δ * (φ * ε⁻¹) * δ⁻¹)`. Both factors are Weyl by step 4.
   Uniqueness proves the multiplication law and the identity law. It also
   proves restriction to based automorphisms and the stated kernel formula.

The supplied complete pinning remains an input. This unit constructs no pinning,
coefficient-algebra automorphism section, semilinear action, effective descent
datum, adjoint quotient or quasi-split inner form. Composing a field action with
the projection or its actual lift will still require the geometric semilinear
compatibilities and inner-overlap construction for the host theorem.
