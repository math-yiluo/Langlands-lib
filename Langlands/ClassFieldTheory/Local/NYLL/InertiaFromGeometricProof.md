# Proof that the geometric residue clause gives the inertia clause

Worker 35 authored this derived proof of
`Langlands.LocalClassField.NYLL.InertiaFromGeometricStatement.{u, v}`.
Worker 248 checked the shared proof against the published statement and prepared
this paired explanation for submission; the Lean proof is unchanged from
Worker 35's shared draft revision 2 of Task 928.
The theorem is `Langlands.LocalClassField.NYLL.inertiaFromGeometric`.
Its type is exactly that proposition, with independent carrier universes `u`
and `v`.

## Notation

Fix the data `p`, `F`, `E`, `TF`, `TE`, the isomorphism `r`, the geometric
hypothesis and `σ`. Write `ρ` for the actual supplied residue action
`Ramification.Padic.residueHom TE F.Carrier`. It is a group homomorphism from
`Gal(E/F)` to the ring automorphisms of the residue field `k_E` of `TE`.
Write `q` for `TF.residueCardinality`, and `[a]` for the class of a unit `a`
in the norm quotient.

## Steps

1. **Inertia criterion.** For every `τ`, `ρ τ = 1` exactly when `τ` fixes
   every integral element modulo the maximal ideal. This is the published
   `suppliedInverseResiduePower` applied to `τ⁻¹` with exponent `1`. The proof
   rewrites `(ρ τ⁻¹)⁻¹` to `ρ τ` with `map_inv` and `inv_inv`, and
   `τ⁻¹.symm` to `τ` with `AlgEquiv.aut_inv` and `AlgEquiv.symm_symm`.
   The theorem's goal is rewritten with this criterion, so it becomes
   `(∃ a, TF.ord a = 0 ∧ r [a] = σ) ↔ ρ σ = 1`.

2. **Frobenius of order-one units.** For every unit `a` of order one,
   `(ρ (r [a]))⁻¹` is the map `y ↦ y ^ q` on `k_E`. This is
   `suppliedInverseResiduePower` applied to `r [a]` and `q`, together with the
   geometric hypothesis.

3. **A uniformizer unit.** `TF.uniformizer` has order one by
   `TF.ord_uniformizer`. It is nonzero because `TF.ord 0 = 0`. Let `π` be the
   corresponding unit and `g := ρ (r [π])`.

4. **Order-zero units act trivially.** Let `a` have order zero. Then `π * a`
   has order one by `TF.ord_mul`. By step 2, `(ρ (r [π * a]))⁻¹` and
   `(ρ (r [π]))⁻¹` agree on every residue class, so they are equal. Since
   `QuotientGroup.mk`, `r` and `ρ` are multiplicative, `g * ρ (r [a]) = g`.
   Hence `ρ (r [a]) = 1`. This proves the forward implication.

5. **The residue action of every class.** For every unit `b` with order `n`,
   `ρ (r [b]) = g ^ n`. The unit `b * π ^ (-n)` has order zero by `TF.ord_mul`
   and `TF.ord_zpow`, so step 4 applies to it. Multiplicativity, `map_zpow` and
   `QuotientGroup.mk_zpow` then give the formula.

6. **Choice of a representative.** For the reverse implication assume
   `ρ σ = 1`. Since `r` is surjective and `QuotientGroup.mk` is surjective,
   there is a unit `b` with `r [b] = σ`. Let `n := TF.ord b`. By step 5,
   `g ^ n = 1`.

7. **Residue-degree divisibility.** Let `f_F := TF.residueDegree` and
   `f_E := TE.residueDegree`, the absolute residue degrees over the prime
   field, so the supplied residue cardinalities are `p ^ f_F` and `p ^ f_E`.
   The proof shows `f_E ∣ f_F * |n|`.
   - From `g ^ n = 1`, `orderOf_dvd_iff_zpow_eq_one` and `Int.natCast_dvd` give
     `orderOf g ∣ |n|`, so `g⁻¹ ^ |n| = 1`.
   - By induction with step 2, `(g⁻¹ ^ k) y = y ^ (q ^ k)` for all `k` and all
     `y` in `k_E`. With `TF.residueCardinality_eq_pow`, `q ^ |n| = p ^ N`,
     where `N := f_F * |n|`. Hence `y ^ (p ^ N) = y` for every `y`.
   - Therefore every unit `x` of `k_E` satisfies `x ^ (p ^ N - 1) = 1`.
     `k_E` is finite by `TE.finite_residueField`. Its cardinality is
     `p ^ f_E` by `TE.residueCardinality_eq_pow`.
     `FiniteField.forall_pow_eq_one_iff` gives
     `p ^ f_E - 1 ∣ p ^ N - 1`.
   - `Nat.pow_sub_one_gcd_pow_sub_one` turns this into
     `p ^ f_E - 1 = p ^ gcd(f_E, N) - 1`. Both powers are positive, so
     `Nat.sub_one_cancel` and `Nat.pow_right_injective` (with `2 ≤ p`) give
     `f_E = gcd(f_E, N)`. This divides `N`.

8. **A norm of the same order.** By step 7 and `Int.natCast_dvd`,
   `f_F * n = f_E * k` for some integer `k`. `TE.ord_surjective_nonzero`
   gives a nonzero `e` in `E` with `TE.ord e = k`. Let `c` be the unit
   `Units.map (Algebra.norm F.Carrier) (Units.mk0 e _)`. It lies in the norm
   range by construction. The published `residueDegree_mul_ord_relative_norm`
   gives `f_F * TF.ord (N e) = f_E * TE.ord e = f_F * n`. Since `f_F` is
   positive by `TF.residueDegree_pos`, `TF.ord c = n`.

9. **Conclusion.** Let `a := b * c⁻¹`. By `TF.ord_mul` and `TF.ord_inv`,
   `TF.ord a = n - n = 0`. By `QuotientGroup.eq`, `[a] = [b]`, because
   `(b * c⁻¹)⁻¹ * b = c` lies in the norm range. Hence `r [a] = r [b] = σ`.

## Dependencies and scope

The proof uses the published `suppliedInverseResiduePower`
(`Langlands.ClassFieldTheory.Local.NYLL.SuppliedInverseResiduePowerProof`),
`residueDegree_mul_ord_relative_norm`
(`Langlands.ClassFieldTheory.Local.NormOrderProof`), the normalization laws of
`Langlands.LocalField.Normalization.Proof`, and Mathlib's finite-field and
natural-number arithmetic. The argument uses the finite-dimensional extension
and the supplied `TF : F.TopologicalData` and `TE : E.TopologicalData`
throughout. It has no `IsGalois` or `IsAbelianGalois` premise, no continuity
premise on `r`, and no additional compatibility premise on `TF` and `TE`.
Its mathematical steps use no Artin map, reciprocity theorem, ramification
filtration or Lubin–Tate construction.

## Provenance

The statement's source analogue is the Corollary to Proposition 13 in
Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, Chapter XIII, §4,
pp. 197–198 (source `serre-1979-local-fields`; retained file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, PDF pages
202–203, source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`).

The corollary says that, for a finite abelian extension, reciprocity sends
the valuation-zero units onto inertia. Serre first applies Proposition 13's
explicit unramified formula to the maximal unramified subextension. For an
inertia element represented by `b`, that formula implies divisibility of
`ord b` by the relative residue degree. Serre then chooses a norm with the
same valuation and divides `b` by it.

The implemented proof obtains the divisibility directly from the supplied
residue action, using the finite-field argument in step 7, instead of
passing to the maximal unramified subextension. Step 8 then follows Serre's
norm adjustment. Serre's Proposition 13 uses arithmetic normalization.
Here the geometric hypothesis places the `q`-power action on the inverse
automorphism: step 2 identifies `g⁻¹` with that power action. Both
normalizations have the same trivial residue action, hence the same inertia
criterion. This is an internal consequence of the Library's geometric
clause for an arbitrary norm-quotient isomorphism, rather than a
construction of a reciprocity map.

The proof compiled without errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.
