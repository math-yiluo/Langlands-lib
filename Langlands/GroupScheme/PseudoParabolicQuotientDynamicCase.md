# The dynamic pseudo-reductive case of CGP Proposition C.1.6

This module is an internal part of the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6, stated in the
Library as `PseudoParabolicQuotientPseudoCompleteStatement`. It records how that
proof begins: "By Proposition 2.2.10, we may assume that `G` is
pseudo-reductive over `k`" and `P = P_G(λ)`. The rest of the proof is isolated
as an interface proposition.

## `DynamicParabolicQuotientDVRLifting k`

For a field `k : Type u`, this proposition asserts the DVR lifting property
`PseudoComplete.HasDVRLifting Q` for every `Q` and `q : G.X ⟶ Q` such that:

- `G` is a pseudo-reductive `k`-group (`IsPseudoReductive G`);
- `χ : 𝔾_m ⟶ G` is a cocharacter;
- `q` is smooth, surjective and quasi-compact;
- for every test scheme `T` over `Spec k` and points `g h : T ⟶ G.X`, we have
  `g ≫ q = h ≫ q` iff `g⁻¹ * h` lies in the actual dynamic parabolic
  `Dynamic.parabolic χ` (that is, `P_G(χ)`).

No separatedness or finiteness of `Q` is assumed. Being a definition, it proves
nothing.

## `pseudoParabolicQuotientPseudoComplete_of_dynamic`

The theorem takes two hypotheses and proves
`PseudoParabolicQuotientPseudoCompleteStatement.{u}`:

- `hred`: the reduction step. Its body is verbatim the Prop
  `PseudoParabolicQuotientPseudoReductiveReductionStatement` of the separately
  published statement task `61afaf01-88db-478f-9c26-6b12f78d7376` (CGP Proposition 2.2.10 with
  Corollary 2.1.9). That statement is not yet in the Library, so it is
  inlined here as a hypothesis.
- `hdyn`: `DynamicParabolicQuotientDVRLifting k` holds for every field `k`.

Proof. Given the data of the target statement, `hred` presents the same `Q` as
a quotient of a pseudo-reductive `G'` by `P_{G'}(χ)`, with the same three
properties of the projection and the same all-test coset criterion. `hdyn` then
gives `HasDVRLifting Q`. The remaining three fields of `IsPseudoComplete Q`
(separated, locally of finite type, quasi-compact) are hypotheses of the
target statement.
