# The actual local-product power intersection from global half-power descent

Author: Worker 1232.

This module implements the algebraic reduction in Artin and Tate, *Class Field
Theory* (AMS Chelsea, 2009), Chapter X, Section 2, Lemma 2, printed p.77
(one-based PDF p.86). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The local maps are internal constructions on the existing actual adelic objects.
The source's global power argument is a separate arithmetic input.

`prescriptionIdeleRetraction` extracts the whole infinite idele coordinate and
the actual completion coordinates at the selected finite places. The finite
projection lemmas identify the prescribed coordinates and show that every
other finite coordinate is one. Their proofs expand the finite product of
single-place insertions; at the matching place its value is the input, and at
other places it is one. The infinite coordinate of every finite insertion is
one. Thus insertion followed by this algebraic retraction is the identity on
the whole local product, including every real sign component. No comparison
of product and induced topologies is used.

`finiteIdeleProjection_diagonalUnits` identifies a principal idele's finite
coordinate with the actual completion embedding of the global unit. All field
universes remain unrestricted.

`prescription_power_preimage_le_of_half_power` assumes the following arithmetic
implication for the fixed field, finite set and natural number `n`: a global
nonzero element which is a local `(2*n)`th power at every finite place outside
`S` has a global `n`th root. It then proves that the preimage of the `(2*n)`th
powers in actual idele classes is contained in the `n`th powers of the actual
prescription local product.

Given a class power relation, choose an idele representative `x` of the class
root. Equality in the actual principal quotient supplies a global unit `k`
such that `x^(2*n)` times its principal idele equals the inserted local product.
At every finite place outside `S`, that product has coordinate one, so the
coordinate of `x⁻¹` is a local `(2*n)`th root of `k`. The arithmetic hypothesis
gives `k = b^n` globally. The idele `diagonalUnits b * x^2` then has `n`th power
equal to the inserted local product. Applying the algebraic retraction yields
its `n`th root in the prescribed whole local product.

This is a conditional reduction. It proves no almost-everywhere local-global
power theorem, no power-quotient topology assertion, and no unconditional
character prescription. The half-power input is the weaker consequence of
Artin–Tate IX.1 Theorem 1, printed pp.65–66 (one-based PDF pp.74–75); its proof
is supplied separately by `almostEverywherePowerHalfStatement` in
`AlmostEverywherePowerHalfProof` when assembling the unconditional theorem.
