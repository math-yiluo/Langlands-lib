# Dimension at most one for Henselian discretely valued fields

Author: Worker 1673.

`Langlands.FieldTheory.HenselianDiscreteDimensionLEOneStatement.{u}` is
an unproved proposition. For every field `K : Type u` and every surjective
valuation `v : Valuation K (WithZero (Multiplicative ℤ))`, Henselianity of
`v.valuationSubring` and algebraic closedness of its actual residue field
imply `HasDimensionLEOne K`.

The conclusion is the actual unit-norm criterion in
`Langlands.FieldTheory.DimensionLEOne`: for every finite separable `E/K`
and every finite Galois `L/E`, the norm `Lˣ → Eˣ` is surjective.
The hypotheses reproduce exactly the field and valuation hypotheses of
`Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement`.
They impose no completeness, perfectness of `K`, separability of its
completion, or characteristic restriction.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Corollary 2.3.7, printed p.81 (PDF p.112), with the setup printed p.80
(PDF p.111), source `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The finite-separable norm criterion is in Section 2.3, printed pp.78–79
(PDF pp.109–110). The integer value group and its normalization are the
existing quasi-splitness target's interface choice.

The source proof first obtains smooth-point approximation over the
completion (Proposition 2.3.4). It then obtains vanishing of first
cohomology for tori over finite separable extensions via the completion
(Proposition 2.3.5), and uses the kernel torus of the norm map to obtain
surjectivity. These are descriptions of the source's argument and remain
proof obligations; no such cohomology, completion or torsor theorem is
assumed by the Lean statement. Example 2.3.2(2) alone would impose the
extra separability-of-completion condition; the present target uses
Corollary 2.3.7 and retains its broader scope.

The official 1 November 2024 corrections, Chapter 2, PDF pp.24–25,
source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
do not modify Section 2.3. Their later Henselian/perfect-residue additions
do not add any premise to this statement.

This is a field-theoretic prerequisite of the Henselian quasi-splitness
proof, not its conclusion. Combining a proof of this proposition with
the separate connected-reductive dimension-one quasi-splitness theorem
would prove that target.
