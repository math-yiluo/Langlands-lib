# Occurrence of inertia types in local Weil representations

## General intertwiner lemmas

- `comp_equiv_ne_zero` and `equiv_comp_ne_zero`: composing a nonzero intertwiner with an
  equivalence, on either side, gives a nonzero intertwiner.
- `equiv_toIntertwiningMap_ne_zero`: an equivalence on a nontrivial space is a nonzero
  intertwiner.

## Occurrence

For a p-adic field `F` and a degree-one `φ`, `WType F φ hφ` is the type of inertia
types of `weilSplit F φ hφ`. `Occurs F φ hφ ρ B` says that there is a nonzero
intertwiner from the inertia restriction of `ρ` to the type `B`.

- `twist_comp_inertia`: unramified twists do not change the inertia restriction.
  `restrictEquiv` turns an equivalence from a twist into an equivalence of inertia
  restrictions.
- Occurrence is invariant under equivalence of `ρ` (`occurs_of_equiv`), under
  unramified twists (`occurs_twist_iff`), and under equivalence or equality of classes
  of the type (`occurs_congr`, `occurs_of_class_eq`).
- `occurs_typeCoind_iff`: the types occurring in `typeCoind S B hp` are exactly the
  conjugates `conjType j [B]` with `j < m + 1`. One direction is `occurs_typeCoind`,
  the other `projType`.
- `occurs_iff_of_occurs`: let `A` be irreducible and continuous, and let `B` occur in
  `A` with exact period `m + 1`. Then the types occurring in `A` are exactly the
  conjugates of `B` below the period. This follows from `twist_equiv_typeCoind`
  and the previous items.
- `exists_twist_of_occurs`: two such representations containing a common type of
  exact period differ by an unramified twist. Their inertia restrictions are
  equivalent through `typeCoind`, so `twist_equiv_of_inertia_ne_zero` applies.
- `inertia_irreducible_of_torsion_one`: if the class of `A` has torsion number one,
  then the inertia restriction of `A` is irreducible.
  - Choose an occurring type `B` (`exists_occurring_type`, with the published
    `continuousWeilFiniteInertiaImage`).
  - `weilTorsionNumber_eq_period` forces its period to be one.
  - Then `A` is a twist of `typeCoind` on `Fin 1 → B`, whose inertia restriction is
    equivalent to `B` by `LinearEquiv.funUnique`.
  - Irreducibility transfers along equivalences (`IsomorphismInvariance.irreducible_iff`).

These are the occurrence statements behind the orbit count in Henniart (1988),
Proposition 2.2. They are internal lemmas for the unramified-descent proof.
