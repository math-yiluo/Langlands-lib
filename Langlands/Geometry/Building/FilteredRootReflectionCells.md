# Actual reflection cells at a filtration jump

This derived module uses the actual apartment, rational root groups, supplied
opposite pairs and supplied zero datum. It defines
`P.rootReflectionCell a ψ m = U_{-ψ} m Z(F)^0 U_{-ψ}` by exhibiting each factor.
Here `Z(F)^0` is mapped by the original centralizer inclusion.

An element of `U_ψ` outside `U_{ψ+}` has valuation exactly `ψ` at one apartment
point: the weak lower bound and failure of the strict lower bound force
equality. Its valuation is finite, so the element is not the identity. Equality
of the linear parts and the value at that point identifies its actual
reflection functional with `ψ`.

Two supplied opposite pairs along the same relative root have equal integral
coroots. The proof uses the published coroot uniqueness theorem, finiteness of
the actual relative roots, and joint spanning by the relative roots and
restricted rational characters of the reductive group. Their full integral
character actions therefore agree, so the quotient of their actual normalizer
representatives centralizes the split torus.

If the two valuation functionals also agree, their quotient fixes every
apartment point. Equality of the integral coroots gives equality in the reduced
real translation space, and the published actual reflection action formula
identifies the two affine actions. This step needs no extra apartment axiom.

V5 for the first opposite factor, and its published consequence for the second
factor, give valuation exactly `-ψ` for both factors at every apartment point.
Thus both belong to the actual group `U_{-ψ}`. These deductions are internal
consequences of the cited Lean imports.

Under `P.SatisfiesApartmentAxioms`, each supplied representative lies in the
supplied simply connected image. Hence so does their quotient, and the actual
zero-subgroup norm-kernel theorem puts this quotient in `G(F)^1`. The centralizer
is represented by `P.centralizer.j`, so the quotient has a preimage `z` in
`Z(F)`. The preceding fixed-apartment result and the published norm-one fixer
lemma put `z` in `Z(F)^1`. With the explicit hypothesis
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`, this preimage belongs
to the actual `P.centralizerZero`. The result
`reflectionElement_inv_mul_eq_centralizerZero` exhibits that preimage and
its exact image. It uses supplied pairs and does not need a pair-existence
hypothesis.

The final inclusion
`affineRootGroup_diff_plus_subset_rootReflectionCell` additionally assumes the
full named `RelativeRoot.HasRankOneFactorization P.i` predicate. For a fixed
`u` at the jump `ψ` and its supplied pair, every other `v` at the same jump
has an opposite pair `q` by the existence component of that predicate. Both
valuation functionals equal `ψ`. The correction result gives
`m(v) = m(u) j(z)` with `z ∈ Z(F)^0`, and V5 puts `q.1` and `q.2` in `U_{-ψ}`.
Rearranging the literal product `m(v) = q.1 v q.2` yields
`v = q.1⁻¹ m(u) j(z) q.2⁻¹`, the required cell witness. This is the first
inclusion in KP Lemma 7.1.4, derived here from the imported valuation,
action, coroot and zero-subgroup results.

The module defines the cell for any character and affine functional. Its
inclusion theorem requires `ψ.linear = rootForm P.i α`; it does not require
membership in a chosen affine-root set or assume the relative root system is
reduced. The local factorization and cover comparison hypotheses remain
explicit intermediate inputs. No strict-cell disjointness, pair-existence
theorem, centralizer comparison theorem, Tits axiom or final Iwahori–Tits
assertion is established here.
