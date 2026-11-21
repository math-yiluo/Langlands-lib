# Types of exact period and the refined Weil strata

Let `F` be a p-adic field and `φ` a degree-one element of `W_F`.

`rank_break_of_occurs` concerns an irreducible continuous `A` containing a type `B` of
exact period `m + 1`. It shows that `rank A = (m + 1) · dim B` and
`lastBreak F A = inertiaBreak F B`. An unramified twist of `A` is equivalent to
`typeCoind`. Use `finrank_typeCoind`, `lastBreak_twist`, the Library's
`lastBreak_equiv` and `lastBreak_typeCoind`.

## Count of types of exact period

`encard_period_goodTypes` assumes `(m + 1) r = k + 1` and `(m + 1) t = s`. It states,
in `ℕ∞`,

`encard {x ∈ goodTypes r t | minimalPeriod (conjType 1) x = m + 1} = encard (weilRefinedStratum F k s (m + 1)) * (m + 1)`.

The relation used is: the class `x` occurs in some representative of the orbit `c`.
The lemma `encard_eq_mul_of_fibers` applies, with the following checks.

- Every good type `B` of exact period `m + 1` lies over an orbit of the stratum. Use
  `typeCoind B` on the stage of degree `m + 1`.
  - Its rank is `(m + 1) r = k + 1`.
  - Its Swan exponent is `(k + 1) · break B = (m + 1) t = s`, by `lastBreak_typeCoind`.
  - Its torsion number is `m + 1` (`weilTorsionNumber_eq_period`).
  - `B` occurs in it (`occurs_typeCoind_iff` with `j = 0`).
- Functionality: two representatives containing a common type of exact period lie in
  one orbit (`exists_twist_of_occurs`).
- Fibers: let `c` be in the stratum, with a representative `A` of torsion number
  `m + 1`.
  - `exists_occurring_type` gives an occurring type `B`. Its period is the torsion
    number `m + 1`, by `weilTorsionNumber_eq_period`.
  - `B` is good, by `rank_break_of_occurs`, the Swan exponent `s` and cancellation of
    `m + 1`.
  - The family `j ↦ conjType j [B]`, for `j < m + 1`, is injective below the minimal
    period.
  - Each member is good of exact period `m + 1` (`conjType_mem_goodTypes`,
    `minimalPeriod_apply_iterate`) and occurs in `A`.
  - Conversely, any type occurring in a representative of `c` occurs in `A`, after an
    unramified twist. So it is one of these conjugates (`occurs_iff_of_occurs`).

## Divisibility of the Swan exponent

`dvd_of_mem_weilRefinedStratum`: if some orbit lies in `W_F(k + 1, s, f)`, then
`f ∣ s`. Let `B` be an occurring type, of period `f = m + 1`.

- Its extension `τ = stageRep B` to the unramified stage `L` of degree `f` is
  irreducible, of rank `r = dim B`.
- The published `HasWeilSwan` gives `τ` an integral Swan label `t'`, with
  `t' = r · lastBreak L τ = r · break B` (`lastBreak_stage`).
- On the other hand `s = (k + 1) · break B = f · r · break B`.
- Hence `s = f · t'`.

These are the orbit-counting and divisibility steps of Henniart (1988),
Proposition 2.2 (route note, Proposition `prop:unram` and `prop:tworeductions`(a)).
