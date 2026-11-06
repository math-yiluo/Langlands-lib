# Open-cell gamma with restricted ambient right invariance

Author: Worker 200.

This internal extension of `OpenCellIntegration` and `LocalOpenCellGamma`
weakens the measure hypothesis to invariance under right translation by the
specified subgroup `V`. It keeps the existing open-cell map, Haar measures
and double-indicator gamma. The source motivation is Waldspurger 2003 I.1,
printed p.240 / PDF p.6, but this is a derived local helper, not a separately
printed lemma or the global formula.

The ambient group is a Borel topological group with a left Haar measure `μ`.
The subgroups `P` and `V` are locally compact and second countable and carry
left Haar measures `μP` and `μV`. The map `(p,v) ↦ p v⁻¹` is assumed to be an
open embedding. The explicit premise `hright` states that every right
translation by an element of `V` preserves `μ`. No ambient right-invariance
instance is used.

`openCellPullbackMeasure` is `Measure.comap openCellMap μ` on the actual
product subgroup carrier. Its definition requires no new gamma scalar or
normalization. The theorem below proves left invariance and finiteness on
compacts of this pullback under the stated hypotheses, then uses Haar
uniqueness to obtain the positive comparison coefficient.

`exists_lintegral_range_openCellMap_of_rightInvariantOn` proves the range
integration formula with a finite positive nonnegative-real coefficient.
The proof follows the existing local range argument: pull back `μ` to
`P × V`; left multiplication there becomes left multiplication by `p` and
right multiplication by `v⁻¹` in the ambient group. Ambient left invariance
and precisely `hright` give invariance of this pullback. Haar uniqueness
compares it with the product Haar. The open nonempty image makes the
comparison coefficient nonzero.

`openCellConstant_ne_zero_ne_top_of_rightInvariantOn` applies this formula
to the indicator of a compact open `K`, using the existing
`measure_inter_range_eq_mul_openCellConstant`. The intersection of `K` with
the image is open and contains one, so it has positive Haar mass. Its mass
is finite because it lies in `K`. The identity equating that mass to the
positive finite coefficient times the original gamma excludes zero and
infinity for gamma.

Neither theorem uses or proves conullness, global integration, a source
Iwasawa decomposition, whole-group unimodularity or any Plancherel result.
The rational-point specialization must prove the displayed translation
premise and the actual open embedding separately.
