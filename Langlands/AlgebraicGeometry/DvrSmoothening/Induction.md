# The induction on the defect and on the centre

- `TestPoint.lift_map`, `chartPrimes_comp`, `centre_map_le`, `resolved_id`,
  `resolve_of_centre_eq_bot`: behaviour of lifts, chart primes and centres along modifications;
  families with empty centre are already resolved.
- `Claim R n`: for every scheme `X` locally of finite type and quasi-compact over `Spec R` with
  smooth generic fibre and every family `E` of test points of defect `< n`, there is a proper
  morphism `g : X' ⟶ X`, an isomorphism away from the centre of `E`, which resolves every member
  of `E` (`Resolved`).
- `claim_zero`: `Claim R 0` holds trivially.
- `claim_succ`: `Claim R n → Claim R (n + 1)`, given `DefectZeroSmoothAtStatement`,
  `DilatationDefectStatement`, `GoodChartStatement` and `BlowupChartStatement`. The proof is a
  noetherian induction on the centre (well-founded on closed subsets of the noetherian space `X`).
  `GoodChartStatement` gives an affine open `U` meeting the centre and `s` with `D(s)` meeting the
  centre, on which the centre is good. First, the members of `E` specializing outside `D(s)` have
  a strictly smaller centre; the inner induction hypothesis resolves them by a modification
  `g₂ : X₂ ⟶ X` which is an isomorphism over `D(s)`. Next, on `X₂` the family of lifts of the
  members of `E` specializing over `D(s)` has its global centre; using the good chart over `D(s)`
  (transported to `X₂`), `dilatation_step` blows up this centre and lowers below `n` the defects of
  the lifts whose specializations lie in the centre. Finally the outer induction hypothesis
  `Claim R n` resolves only these lifts, and the three modifications are composed. The remaining
  lifts over `D(s)` specialize outside the centre, hence into the smooth locus of `X₂`; they stay
  resolved under the last two modifications, which are isomorphisms away from their centres.
- `claim`: `∀ n, Claim R n`.

This follows the proof of Theorem 2 of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.4 (printed
pp. 71–73), with the partition of `E` replaced by noetherian induction on the centre inside a fixed
scheme and an outer induction on a bound for the defect.
