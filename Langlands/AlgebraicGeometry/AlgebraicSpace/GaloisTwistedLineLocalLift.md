# Zariski-local lifts over `K'`-schemes

Author: Worker 105.

This is support for Conrad's Example 5.13 (printed p.20).

## Statement

Let `W` be a scheme over `Spec K` with a `K'`-structure `q : W → Spec K'` compatible with its
structure map (`hq`). Let `x` be a point of the Galois-twisted line over `W`.
`exists_local_lift` states: every point `w` of `W` has an open neighbourhood `V` on which the
restriction of `x` lifts to the line.

## Proof

1. **The pullback.** Pull the atlas back along `x`. This gives `liftP D x` with an étale
   surjective projection `liftSnd` to `W` and a point `liftFst` of the line (`isPullback_liftP`,
   `etale_liftSnd`, `surjective_liftSnd`).
2. **The splitting idempotent.** The global idempotent `liftIdem` of `liftP` is `splitIdem` of
   two ring maps `K' → Γ(liftP, ⊤)`:
   - the `K'`-structure pulled back from `W`;
   - the restriction of the lifted point to constants.

   It splits `liftP` into two basic opens (`mem_basicOpen_or`).
3. **The type of the lift on each piece.** On the basic open of `liftIdem`, the restriction of
   the lifted point to constants is the `K'`-structure pulled back from `W`
   (`restrict_on_basicOpen`). On the basic open of `1 − liftIdem` it is the conjugate structure
   (`restrict_on_basicOpen_conj`). Both follow from `splitIdem_mul` and `one_sub_splitIdem_mul`,
   after mapping the idempotent to a unit idempotent, which equals `1`.
   - `mono_of_restrict`: suppose that on an open piece, any two lifts over a common point of `W`
     have the same restriction to constants. Then the projection of the piece to `W` is a
     monomorphism.
   - The proof of `mono_of_restrict`: the two lifts have the same image in the quotient, so a
     point `r` of the relation relates them (kernel pair). A ring map out of the relation ring
     whose two composites agree on `K'` has equal composites (`comp_tStar_eq_of_restrict_eq`).
     Hence the two lifts are equal, and `liftP_hom_ext` gives equality of the two maps.
4. **Open immersions.** Each piece therefore maps to `W` by an étale monomorphism (`mono_piece`,
   `mono_piece_conj`). An étale monomorphism is an open immersion
   (`IsOpenImmersion.of_flat_of_mono`).
5. **The lift.** The image of the piece containing a preimage of `w` is the required open set.
   The lift is read off from `liftFst` (`lift_of_openImmersion`).
