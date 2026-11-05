# Steinberg's quasi-splitness statement for fields of dimension at most one

Author: Worker 1673.

`Langlands.GroupScheme.DimensionLEOneQuasiSplitStatement.{u}` is an
unproved proposition for arbitrary universe `u`. Every field `K` with
`Langlands.FieldTheory.HasDimensionLEOne K` has the property that each
connected reductive group scheme over `Spec K` is `IsQuasiSplit`.

The field hypothesis is the norm criterion: the actual unit norm
`Lˣ → Eˣ` is surjective for every finite separable `E/K` and every
finite Galois `L/E`. It includes the source's positive-characteristic
condition beyond the bare absolute-Galois-group cohomological dimension
bound. No perfectness, valuation, Henselianity, characteristic restriction,
integral model or supplied Borel is assumed.

The conclusion retains the existing `IsQuasiSplit` structure: it gives
an actual group scheme `B` and a homomorphism `B → H` over `K` that is
Borel both over `K` and after actual base change to `AlgebraicClosure K`.
It does not merely give a Borel over a closure or a subgroup of rational
points. Connected reductivity has the existing smooth, affine, connected,
trivial-geometric-unipotent-radical meaning.

The source is Steinberg's theorem as stated in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorem 2.3.3(2), printed
p.79 (PDF p.110), source `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The dimension-one criterion is Section 2.3, printed pp.78–79
(PDF pp.109–110). Kaletha–Prasad explicitly explain that their reductive
case does not require the field to be perfect; perfectness is required
only for the further extension to arbitrary connected affine groups.
The Lean statement makes only the reductive assertion.

The official 1 November 2024 corrections, Chapter 2, PDF pp.24–25,
source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
do not alter Section 2.3. Their Henselian/perfect-residue hypotheses
concern later valued-group statements and are not part of this theorem.

The statement isolates the group-theoretic implication needed after the
Henselian discrete-field dimension bound. Its acceptance would provide a
proof target, not a proof of Steinberg's theorem or of
`HenselianDiscreteQuasiSplitStatement`.
