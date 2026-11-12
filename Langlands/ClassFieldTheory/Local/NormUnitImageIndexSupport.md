# Index arithmetic for norm images of unit filtrations

Helper lemmas for the proof of
`Langlands.LocalClassField.FiniteAbelianNormUnitImageCardinality`. None of them
is a statement from the literature; they are internal tools of the proof.

## Group-theoretic lemmas

- `relIndex_sup_map_dvd`: for a homomorphism `f : G →* G'` into a commutative
  group, subgroups `D ≤ B` of `G` and a subgroup `A` of `G'`, the relative index
  of `A ⊔ f(D)` in `A ⊔ f(B)` divides the relative index of `D` in `B`. The proof
  writes `A ⊔ f(B)` as `f(B) ⊔ (A ⊔ f(D))`, uses `Subgroup.relIndex_sup_right`
  (the second isomorphism theorem for relative indices) and
  `Subgroup.relIndex_comap`, and finishes with `Subgroup.relIndex_dvd_of_le_left`
  since `D` lies in the preimage of `A ⊔ f(D)`.
- `relIndex_map_dvd`: the case `A = ⊥`.
- `card_eq_card_map_mul_card_inf_ker`: the order of a subgroup `S` equals the
  order of `f(S)` times the order of `ker f ⊓ S`. It is
  `Subgroup.relIndex_ker` combined with `Subgroup.relIndex_mul_relIndex` for
  `⊥ ≤ ker f ⊓ S ≤ S`; all quantities are `Nat.card`s, so infinite cases use the
  convention `Nat.card = 0` and need no finiteness hypothesis.
- `card_map_mk_eq_of_dvd`: the counting argument used at the end of the proof.
  Let `Nm`, `Un`, `V` be subgroups of a commutative group with
  `Nm.index ≠ 0`, `V ≤ Nm`, `[Un : V] ∣ c`, and
  `[G' : Un ⊔ Nm] · c ∣ [G' : Nm]`. Then the image of `Un` in `G' / Nm` has
  exactly `c` elements. The image has order `[Un : Un ⊓ Nm]`
  (`Subgroup.relIndex_ker` for the quotient map). This number divides
  `[Un : V]` and hence `c`, because `V ≤ Un ⊓ Nm`. Conversely
  `[G' : Nm] = [G' : Un ⊔ Nm] · [Un : Un ⊓ Nm]`, so cancelling the nonzero
  factor `[G' : Un ⊔ Nm]` gives `c ∣ [Un : Un ⊓ Nm]`.

## The local norm index across universes

`normSubgroup_index_eq_finrank` states that for a finite abelian extension
`E/F` of p-adic fields in independent universes `u` and `v`, the norm subgroup
`N_{E/F}(Eˣ)` has index `[E : F]` in `Fˣ`. This is the norm index equality of
local class field theory, a consequence of the reciprocity isomorphism
`Fˣ / N_{E/F}(Eˣ) ≅ Gal(E/F)`. The Library proves it as
`Langlands.ClassFieldTheory.Local.normSubgroup_index_eq_finrank` when both
fields lie in one universe. The proof here moves the extension to the
universe-zero models `NYLL.universeZeroModel F` and `NYLL.universeZeroModel E`.
`NYLL.universeZeroNormRange_map` says that the units map of the model
equivalence carries the model norm subgroup onto the actual norm subgroup, and
`Subgroup.index_map_equiv` says that a group isomorphism preserves indices.
`NYLL.universeZeroAlgebra_finrank` says that the model degree equals `[E : F]`.
