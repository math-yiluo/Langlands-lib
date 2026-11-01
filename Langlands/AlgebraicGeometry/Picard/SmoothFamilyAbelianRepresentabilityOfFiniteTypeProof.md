# Proof: reducing the smooth-family representer to finite type over `ℤ`

This module proves
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfFiniteTypeStatement.{u}`
as the theorem
`Langlands.AbelianScheme.smoothFamilyAbelianRepresentabilityOfFiniteType`.
That statement is the implication from the finite-type case
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}` to the shared
target `SmoothFamilyAbelianRepresentabilityStatement.{u}`. The finite-type
case is the hypothesis of the implication and is not proved here. Every other
input is a published Library theorem.

## Declarations

- `finiteType_int_subringClosure`: for a commutative ring `R` and a finite
  set `s : Finset R`, the unital subring `Subring.closure s` is of finite
  type over `ℤ`. The proof transfers `Algebra.FiniteType.adjoin_of_finite`
  along Mathlib's `ℤ`-algebra equivalence `Subring.closureEquivAdjoinInt`
  between `Subring.closure s` and `Algebra.adjoin ℤ s`.
- `smoothFamilyAbelianRepresentability_spec_of_finiteType`: given the
  finite-type case, every abelian scheme `A` over `Spec R`, for any
  `R : CommRingCat.{u}`, has an abelian-scheme parameter `B` over `Spec R`
  and a family `L` for `A` on `B.X` with
  `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`.
- `smoothFamilyAbelianRepresentabilityOfFiniteType`: the target implication.

## Proof

The affine case runs as follows. Let `A` be an abelian scheme over `Spec R`
and assume the finite-type case.

1. The published theorem `affineObjectSpreading` gives a finite set
   `s ⊆ R`, an abelian scheme `A₀` over `Spec R₀` with
   `R₀ = Subring.closure s`, and an isomorphism `e` from the base change of
   `A₀` along `b = Spec.map (R₀ ↪ R)` to `A`.
2. By `finiteType_int_subringClosure`, `R₀` is of finite type over `ℤ`, so
   the finite-type case gives an abelian scheme `B₀` over `Spec R₀` and a
   family `L₀` for `A₀` on `B₀.X` that is universal on quasi-separated
   tests.
3. The published theorem `smoothFamilyUniversalBaseChange` shows that the
   family `(baseChangeFamily b A₀ B₀.X).obj L₀` is universal on
   quasi-separated tests. It is a family for the base-changed abelian scheme
   `(baseChange b).obj A₀` on the parameter `(Over.pullback b).obj B₀.X`.
4. The published theorem `smoothFamilyUniversalIsoTransport`, applied to
   `e.symm`, gives a family `L` for `A` on the same parameter that is
   universal on quasi-separated tests. This parameter is by definition the
   underlying object of the abelian scheme `(baseChange b).obj B₀`, so
   `B = (baseChange b).obj B₀` and `L` are the required witnesses.

For a quasi-separated base `S`, the published Zariski gluing theorem
`smoothFamilyAbelianRepresentabilityOfOpenCover` is applied to Mathlib's
affine open cover `S.affineOpenCover.openCover`. Its members are spectra
`Spec (S.affineOpenCover.X i)` of commutative rings, so the affine case
supplies the local hypothesis for every member. This proves
`SmoothFamilyAbelianRepresentabilityStatement.{u}` from the finite-type
case.

The predicate `IsUniversalSmoothFamilyOnQuasiSeparatedTests` is used
unchanged throughout. No hypothesis is added: every quasi-separated base,
every quasi-separated test (including nonreduced tests) and universe `u`
are retained. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Route

The proof follows reduction steps (1) and (2) in Faltings–Chai,
*Degeneration of Abelian Varieties*, Chapter I, proof of Theorem 1.9,
printed p. 6. Step (1), the reduction to affine bases, is the Zariski gluing
step. Step (2), the reduction to bases of finite type over `ℤ` by finite
presentation, is the combination of spreading, base change and
transport along the isomorphism `e`.
