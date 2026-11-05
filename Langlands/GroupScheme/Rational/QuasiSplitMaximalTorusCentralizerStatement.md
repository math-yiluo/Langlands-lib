# Maximally split maximal tori in a quasi-split group

`Langlands.GroupScheme.QuasiSplitMaximalTorusCentralizerStatement.{u}` is an
unproved statement over arbitrary fields `k : Type u`. Let `G` be quasi-split
in the Library's geometric sense: it is connected reductive and has an actual
field-defined Borel inclusion which remains Borel after base change to an
algebraic closure. For every maximal torus `i : T → G`, ambient maximal
split torus `a : A → G`, and actual factorization `f ≫ i = a`, the
statement asserts that `i` represents `torusCentralizer a`.

The conclusion includes monicity of the underlying map and equality of its
range with the whole-group centralizer on every test scheme and after every
refinement. It does not merely compare rational-point subgroups. The tori and
factorization are arbitrary supplied presentations; no equality of their source
objects is required. There is no restriction on characteristic or perfectness
of the field, no splitting-field datum and no additional density premise.

This is a derived formulation of the minimal-Levi descriptions in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Fact 2.6.22,
printed p.104 (PDF p.135), and Remark 2.6.25(2), printed p.105 (PDF p.136).
The source identifies a minimal Levi with the centralizer of a maximal split
torus, and in the quasi-split case identifies minimal Levis with maximally split
maximal tori. Definition 2.6.2, printed p.93 (PDF p.124), defines maximally
split maximal tori by their maximal split subtori. The present formulation
spells out the contained ambient maximal split torus and its factorization.
The geometric identification makes its centralizer a torus; the given maximal
torus containing `A` then equals that centralizer by maximality.

The cited source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The official 2024 corrections, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
Section 2.6, PDF pp.24–25, add Henselian and perfect-residue hypotheses to the
valued-field discussion beginning before Definition 2.6.20. This statement is
the arbitrary-field geometric implication underlying the cited identification,
consistent with the arbitrary-field scope of Section 2.6(a)–(c), printed
pp.92–93 (PDF pp.123–124); it has no valuation terms. This scope and the
all-test representation conclusion are explicit derived packaging, not a
verbatim quotation of the later valued-field remark.

This module supplies no proof of the geometric implication, no quasi-splitness
theorem for any particular field, and no ordinary or sharp conjugacy theorem.
