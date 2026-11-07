# Actual fibre sections from a uniform Lang–Weil estimate

Author: Worker 208.

This derived construction implements the numerical rational-point step following
Lemma 4.6 in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp.12–13. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The final paragraph of the proof of Theorem 4.5 on p.13 deduces a rational
point when the residue-field cardinality is sufficiently large. Here the explicit
sufficient threshold is `q > C²`, for the constant `C` in (4.6.1).

## Numerical positivity and actual points

`langWeil_count_pos` proves the following real inequality for every natural
number `d`, including zero. If `C ≥ 0`, `C² < q`, and
`|N − q^d| ≤ C q^(d − 1/2)`, then `N > 0`.
Indeed, `q > 0` and `C < √q`; the real-power subtraction identity writes the
error term as `C q^d / √q < q^d`. The lower half of the absolute-value
estimate gives positivity.

`nonempty_sections_of_langWeil_bound` applies this calculation to any field `K`,
scheme `V` and structure map `π : V → Spec K`. Its input is the displayed
Lang–Weil bound on `Nat.card` of the actual section subtype
`{s : Spec K → V // s ≫ π = 𝟙 _}`, with `q = Nat.card K` and `q > C²`.
The conclusion is that this section subtype is nonempty. No finiteness instance
is assumed: the positive `Nat.card` also entails finiteness by Mathlib's
`Nat.card_pos_iff`. The cardinality threshold itself excludes infinite `K`,
whose `Nat.card` would be zero. This is a consequence of the given numerical
estimate, with no independent estimate claimed.

## The uniform construction

`uniformLangWeilLargeResidueSections` takes an explicit proof of the published
`UniformLangWeilStatement`, schemes `B`, `Y`, a morphism `f : Y → B`, a common
natural relative dimension `d`, and every hypothesis of that statement:

- the structure morphism from `B` to `Spec (ULift ℤ)` is locally of finite type
  and `B` is quasi-compact (`CompactSpace B`);
- `f` is smooth, separated, surjective, locally of finite type, quasi-compact
  and geometrically connected;
- each actual fibre `f.fiber b` has pure dimension `d`.

In an arbitrary common universe `u`, it returns a dependent pair consisting of
one positive real constant `C` and, for every closed point `b` with
`Nat.card κ(b) > C²`, an actual morphism
`s : Spec κ(b) → f.fiber b` satisfying
`s ≫ f.fiberToSpecResidueField b = 𝟙 _`.
The same `C` works for every such point. The construction obtains this constant
from the supplied uniform estimate, applies the preceding positivity lemma
and chooses a section by classical choice. No uniqueness, naturality or
canonical selection is asserted.

The proof of the full uniform estimate remains an explicit prerequisite.
This unit does not prove Lemma 4.6, finite-exception surjectivity at global
places, compatibility with arbitrary finite residue extensions, spreading
of the smooth morphism or adelic openness. Those remain obligations in the
parent program.
