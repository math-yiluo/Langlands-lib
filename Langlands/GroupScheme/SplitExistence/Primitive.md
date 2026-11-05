# Primitive integral matrices (`Primitive`)

Author: Worker 239.

Call an integral matrix `B` *primitive* if it is nonzero modulo every prime `p`, that is, if
the gcd of its entries is `1`. The module uses this notion only through the hypothesis
`∀ p, p.Prime → B.map (Int.castRingHom (ZMod p)) ≠ 0`. It defines no new notion.

## Results

- `map_zmod_eq_zero_iff`: `B` is zero modulo `p` exactly when `p` divides every entry of `B`.
- `exists_int_of_map_eq_smul`: if `B` is primitive and `A = q • B` over `ℚ` for an integral
  matrix `A`, then `q` is an integer `z` and `A = z • B` over `ℤ`.

  Proof: from `A c d = q · B c d`, we get `den(q) · A c d = num(q) · B c d` for all entries. If
  a prime `p` divided `den(q)`, it would divide `num(q) · B c d`, hence `B c d` for every entry,
  because `num(q)` and `den(q)` are coprime. This contradicts primitivity. So `den(q) = 1`.
- `eq_one_or_eq_neg_one_of_map_eq_smul`: if `A` and `B` are both primitive and `A = q • B`
  over `ℚ`, then `q = z` with `z = ±1` and `A = z • B`. By the previous item `q = z ∈ ℤ`. A prime
  divisor of `z` would divide every entry of `A`, so `|z| = 1`.
- `map_rat_ne_zero`: a matrix that is nonzero modulo some prime is nonzero over `ℚ`.
- `map_conj_ne_zero`: if `g' g = 1` and `A.map f ≠ 0` for a ring homomorphism `f : ℤ →+* S`,
  then `(g A g').map f ≠ 0`, because `A = (g' g) A (g' g) = g' (g A g') g`.

## Provenance

These are elementary facts about integers and rational numbers. In the Chevalley construction
they show that integral root operators are determined up to sign (compare Steinberg,
*Lectures on Chevalley groups*, §1, where the structure constants are determined up to sign).
The statements here are internal to this project.
