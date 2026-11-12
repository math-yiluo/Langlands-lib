# Existence and independence of actual Tits indices

Source: J. Tits, *Classification of algebraic semisimple groups* (1966),
§§2.1–2.3, printed pp.38–39 (proceedings PDF pp.43–44).
Registered source `tits-1966-classification-algebraic-semisimple`;
SHA-256 `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
The source makes these choices for an arbitrary field, defines the index
from them, and treats it as an invariant of the group. These declarations
make the resulting existence and choice assertions explicit proof targets.

All names below belong to `Langlands.GroupScheme`. The field is
`k : Type u`, with arbitrary `u`. The ambient group is the actual
`GroupScheme (Spec (CommRingCat.of k))`, with explicit `IsAffineHom`
and `LocallyOfFiniteType` hypotheses on its structure map. There is no
local-field, perfectness, characteristic or nontrivial-rank restriction.
Semisimplicity in the Library includes smoothness, so the explicit
locally-finite-type hypothesis does not narrow the mathematical scope.

`TitsIndexExistenceStatement` asserts that every such semisimple group
admits `TitsIndexData G`. This conclusion supplies the actual maximal
split torus, a maximal torus over `k` containing it, actual based root
data and pinning over the separable closure, and a generic relative
cocharacter whose signs agree with the absolute positive system on
every root with nonzero restriction. The implementation of compatible
orders by these finite root signs is explained in `TitsIndex.md`.
The assertion is not made conditional on the existence of those choices.

`TitsIndexIndependenceStatement` quantifies over every two compatible
choices `d e : TitsIndexData G` for the same group. Semisimplicity is
already a field of each such datum. The conclusion is an inhabited
`TitsIndexEquiv d e`: a bijection of simple vertices preserving every
integral Cartan pairing, the subset of roots vanishing on the maximal
split torus, and the action of each element of `Gal(k_s/k)`. It allows
both maximal tori, both maximal split tori, both positive chambers and
both pinnings to vary. It asserts an equivalence of indices; it does
not assert that the auxiliary tori or pinning data are identical.

`TitsIndexChoiceStatement` is exactly the conjunction of the preceding
two statements, at the same arbitrary universe. It adds no hypotheses.

All three declarations are unproved `Prop`-valued definitions, not
theorems or axioms. The substantive remaining units are existence of
compatible data and independence of the resulting index. The Library's
`StarActionIndependenceStatement` and published proof compare based
absolute root data and full star actions, but do not include the chosen
maximal split torus or the zero-restriction subset. That theorem alone
therefore does not prove the second target. A proof must additionally
control those actual restrictions, using rational conjugacy and
compatible positivity. No local rank-one classification or Kneser–Tits
result is used or assumed by these targets.
