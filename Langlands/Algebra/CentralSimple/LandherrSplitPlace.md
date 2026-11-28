# Finite places of a number field at which a quadratic extension splits

Module: `Langlands.Algebra.CentralSimple.LandherrSplitPlace`.

- `localDegree_eq_one_of_identity_frobenius`: for an extension `L/K` of number fields, a
  finite place `q` of `L` over `p`, unramified, whose arithmetic Frobenius is the identity has
  local degree `[L_q : K_p] = 1`. The local degree is `e · f` (`localDegree_eq`, module
  `Langlands.Global.AdelicFunctoriality.LocalDegree`), `e = 1`, and `f` is the order of the
  Frobenius of the residue field extension, which is trivial.
- `exists_split_finitePlace`: for a separable quadratic extension `E/F` of a number field and
  any finite set `S` of finite places of `F`, there is a finite place `v ∉ S` at which
  `d = skewSq F E` is a square in `F_v`.

## Proof of `exists_split_finitePlace`

The Chebotarev density theorem in the form `Global.chebotarevPrimeRealizationStatement`
(module `Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof`) gives a place `p ∉ S`
of `F` and an unramified place `q` of `E` over it with trivial Frobenius. Then
`[E_q : F_p] = 1`, so the square root `r` of `d` in `E` lies in `F_p`
(`Global.Arithmetic.KummerRadical.exists_pow_eq_of_finrank_eq_one`).

## Provenance

Infinitely many places of `F` split in a quadratic extension (a special case of the
Chebotarev density theorem). In the proof of Landherr's theorem a split place outside the
exceptional set is the auxiliary place `v₀` at which strong approximation leaves the
coordinates unconstrained (compare the places `v₀`, `v₁` of Step 4 in Kneser, *Lectures on
Galois Cohomology of Classical Groups* (1969), §5.5, printed p. 75, PDF p. 81); at a split
place the equation `X² - d Y² = z` is always solvable.
