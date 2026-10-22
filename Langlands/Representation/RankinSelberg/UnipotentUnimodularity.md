# Right invariance of normalized upper-unipotent Haar measure

Worker 117 implements `Langlands.RankinSelberg.unipotentHaar_rightInvariant`,
which proves the published proposition
`Langlands.RankinSelberg.UnipotentHaarRightInvariantStatement F n` exactly.
The theorem allows every universe for `F`, every natural number `n`, and
precisely the field, valuation, topology, nonarchimedean local field, and
unipotent-group measurable and Borel instances in that proposition.
`unipotentHaar_isMulRightInvariant` exposes the conclusion as a typeclass
instance for downstream use.

The measure is the existing `unipotentHaar F n` from `Measures`. Its
normalization on the integral unipotent subgroup is unchanged. The proof
uses its existing Haar and regularity instances. It does not assume a
quotient measure, right invariance, a restriction on characteristic,
countability, or a measurable space on the coefficient field or ambient
general linear group.

The implementation is an internal derivation from the published matrix,
compact open subgroup, and Haar interfaces. Worker 103 supplied the
compact-open-subgroup proof route in the task context. Worker 117 supplied
the finite-denominator construction and the Lean proof. No unpublished
draft or external source theorem is imported. The supporting general
measure theorem is Mathlib's
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular` in
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`, at the pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

The proof has the following steps.

1. The public helper `Langlands.RankinSelberg.common_integer_denominator`
   clears a finite set of field elements with
   one nonzero integral scalar `d`. For one element `x`, choose `1` if `x`
   is integral, and choose `x⁻¹` otherwise. The valuation inequality
   `val_le_one_or_val_inv_le_one` makes the latter choice integral.
   Induction on the finite set multiplies the denominators; all factors
   remain integral and nonzero.
2. `scalingDiagonal` is the invertible diagonal matrix with entry
   `(d^i)⁻¹` at index `i`. Conjugation scales entry `(i,j)` by
   `(d^i)⁻¹ d^j`. For an upper entry, this yields
   `d^(j-i-1) (d * g_ij)`, which is integral when `d * g_ij` is integral.
   Diagonal entries remain one, and entries below the diagonal remain zero.
3. The public lemma `unipotent_exists_compact_open` applies the denominator
   construction to all entries of both `g` and `g⁻¹`. Their diagonal
   conjugates therefore belong to the ambient integral general linear
   subgroup, using `Conductor.mem_integralSubgroup`. Pulling that subgroup
   back along conjugation restricted to the unipotent group gives an open
   subgroup `K` containing `g`. It is compact because the unipotent group
   is closed in the ambient group, conjugation is a homeomorphism, and the
   integral general linear subgroup is compact. The construction does not
   require a separately bundled conjugation automorphism of the unipotent
   group.
4. The private general lemma `map_right_eq_self_of_compact_open` treats a
   regular left Haar measure `μ` and an element `g` of a compact open
   subgroup `K`. Right translation produces another regular left-invariant
   measure. Regular Haar uniqueness writes it as `c • μ`, with
   `c = haarScalarFactor (Measure.map (fun x => x * g) μ) μ`.
   The preimage of `K` under right translation is `K`. Evaluating the
   measure equality on `K` gives `μ K = c * μ K`. Its mass is nonzero
   because `K` is nonempty and open, and finite because it is compact.
   Cancellation in the extended nonnegative reals gives `c = 1`.
5. The closing theorem derives Hausdorffness from the local field
   hypotheses and local compactness from the finite matrix space and
   closedness of the unipotent group. It applies steps 3 and 4 to every
   element with the actual normalized measure.

This proof uses neither continuity of the modular character nor a theorem
about arbitrary compact subgroups. It establishes the needed compact open
containment directly and applies regular Haar uniqueness, so it does not
need an additional full inner-regularity or sigma-finiteness hypothesis.
The case `n = 0` is included by the same argument.
