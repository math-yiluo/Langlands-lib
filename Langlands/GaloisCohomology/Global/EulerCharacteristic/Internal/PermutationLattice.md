# Permutation modules with the same character

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/PermutationLattice.lean`, namespace `Langlands.GaloisCohomology`.

Let `Γ` be a finite group and `X`, `X'` finite `Γ`-sets with `#X^γ = #X'^γ` for every `γ ∈ Γ` (the
permutation characters agree). Then:

* over a field of characteristic `0`, two finite-dimensional representations with the same
  character are isomorphic (`nonempty_equiv_of_character_eq`, by Maschke's theorem and induction on
  the dimension), so the permutation representations `k^X` and `k^{X'}` are isomorphic;
* the permutation lattices `ℤ^X`, `ℤ^{X'}` are then related by an injective intertwining map with
  finite cokernel (`exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq`), obtained from the
  real isomorphism by `Langlands.Cohomology.Herbrand.exists_intMatrix_det_ne_zero`;
* an additive function `d` on finite `𝔽_ℓ[Γ]`-modules takes the same value on `𝔽_ℓ^X` and `𝔽_ℓ^{X'}`
  (`AdditiveFunction.toFun_funPermRep_eq_of_card_fixedBy_eq`): `d(𝔽_ℓ^X) = g(ℤ^X)` for the
  associated function `g(A) = d(A/ℓA) - d(A[ℓ])` (`AdditiveFunction.g_funPermAction`), which is
  unchanged by an injective map with finite cokernel.

This is the lattice argument in Tate's proof of the global Euler characteristic formula; here it
serves the reduction to cyclic subgroups (Artin's induction theorem) in
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Artin`.

```lean
theorem exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x)
theorem toFun_funPermRep_eq_of_card_fixedBy_eq [NeZero l] [Finite Γ] {X X' : Type u}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) =
      d.toFun (X' → ZMod l) (funPermRep (ZMod l) Γ X')
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq : ∀ {Γ : Type u_1}
  [inst : Group Γ] [Finite Γ] {X : Type u_2} {X' : Type u_3} [inst_2 : MulAction Γ X] [inst_3 : MulAction Γ X']
  [Finite X] [Finite X'],
  (∀ (γ : Γ), Nat.card ↑(MulAction.fixedBy X γ) = Nat.card ↑(MulAction.fixedBy X' γ)) →
    ∃ (φ : (X → ℤ) →ₗ[ℤ] X' → ℤ),
      Function.Injective ⇑φ ∧
        (∃ (n : ℤ), n ≠ 0 ∧ ∀ (y : X' → ℤ), ∃ (x : X → ℤ), φ x = n • y) ∧
          ∀ (γ : Γ) (x : X → ℤ),
            φ (((Langlands.GaloisCohomology.funPermRep ℤ Γ X) γ) x) =
              ((Langlands.GaloisCohomology.funPermRep ℤ Γ X') γ) (φ x)
```

## Outline of the proofs

Over `ℚ` or `ℝ`, finite-dimensional representations of a finite group with equal characters are isomorphic (Maschke and orthogonality of characters, here by induction on the dimension). A real isomorphism between permutation lattices yields, through an integral matrix with nonzero determinant (`Herbrand.exists_intMatrix_det_ne_zero`), an injective intertwiner `ℤ^X → ℤ^{X'}` with finite cokernel, and the function `g(A) = d(A/ℓ) - d(A[ℓ])` is invariant under such maps.

- `exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq`: **Permutation lattices with the same character.** There is an injective intertwining map `ℤ^X → ℤ^{X'}` whose image contains `n · ℤ^{X'}` for some `n ≠ 0`.
- `toFun_funPermRep_eq_of_card_fixedBy_eq`: **Additive functions on permutation modules depend only on the permutation character.**

## Declarations

`funPermRep`, `funPermRep_apply`, `funPermAction`, `character_prod`, `equivProdRight`, `exists_equiv_prod_of_injective`, `nonempty_equiv_of_character_eq`, `character_funPermRep`, `nonempty_equiv_funPermRep_of_card_fixedBy_eq`, `toMatrix'_funPermRep`, `exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq`, `Local.AdditiveFunction.finite_modN_fun`, `Local.AdditiveFunction.g_funPermAction`, `Local.AdditiveFunction.toFun_funPermRep_eq_of_card_fixedBy_eq`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.1) Lemma, p. 503, and (8.7.2) Proposition, p. 504 (Galois modules with isomorphic extensions of scalars; the S-units as a Galois lattice).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeDefs.lean` lines 1–16, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean` lines 1–155, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeCharacter.lean` lines 1–145. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).
