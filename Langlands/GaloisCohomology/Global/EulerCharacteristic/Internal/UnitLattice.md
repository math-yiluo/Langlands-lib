# The `S`-units as a Galois lattice

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/UnitLattice.lean`, namespace `Langlands.GaloisCohomology`.

Let `L / K` be a finite Galois extension of number fields with group `Γ`, `S` a finite set of finite
places of `K` and `S_L` the places of `L` above `S`. For an additive function `d` on finite
`𝔽_ℓ[Γ]`-modules, extended to finitely generated `ℤ[Γ]`-modules by `g(A) = d(A/ℓ) - d(A[ℓ])`
(`Local.AdditiveFunction.g`), this file computes
`g(𝒪_{L,S}ˣ) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` (`g_sUnitsOf`).

The proof is Tate's. For the units: `𝒪_Lˣ/torsion ⊕ ℤ` is the augmented logarithmic lattice of the
library's class field theory (`fullLogIntegralSplit`), a `Γ`-stable full lattice in `ℝ^{∞_L}`, as is
`ℤ^{∞_L}`; two such lattices are related by an injective `Γ`-map with finite cokernel
(`Langlands.Cohomology.Herbrand.exists_injective_finite_coker_of_isZLattice`), on which `g` does not change
(`g_units`). For the `S`-units: the valuations at the places of `S_L` give the exact sequence
`1 → 𝒪_Lˣ → 𝒪_{L,S}ˣ → ℤ^{S_L}` with finite cokernel (`SUnitIndex`), equivariant for the action of
`Γ` on the places by transport of structure (`finitePlaceAction` of the module
`Langlands.Galois.RestrictedRamification.Unramified`, through `finitePlaceEquiv`).

```lean
theorem g_eq_add_of_exact_of_finite_cokernel {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C] (f : A →+ B) (p : B →+ C)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b)
    (hf : Function.Injective f) (hfp : Function.Exact f p) [Finite (C ⧸ p.range)] :
    d.g B = d.g A + d.g C
theorem g_units :
    d.g (Additive (𝓞 L)ˣ) =
      d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) -
        d.one
theorem g_sUnitsOf :
    letI
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.g_units : ∀ {K L : Type u} [inst : Field K] [inst_1 : Field L] [inst_2 : NumberField L]
  [inst_3 : Algebra K L] {ℓ : ℕ} [inst_4 : NeZero ℓ] (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.g (Additive (NumberField.RingOfIntegers L)ˣ) =
    d.toFun (NumberField.InfinitePlace L → ZMod ℓ)
        (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) (NumberField.InfinitePlace L)) -
      d.one
@Langlands.GaloisCohomology.g_sUnitsOf : ∀ {K L : Type u} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L]
  [inst_3 : NumberField L] [inst_4 : Algebra K L]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_5 : Finite ↑S] {ℓ : ℕ}
  [inst_6 : NeZero ℓ] (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.g (Additive ↥(Langlands.GaloisCohomology.sUnitsOf S L)) =
    d.toFun (↑(Langlands.Galois.finitePlacesAbove L S) → ZMod ℓ)
          (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) ↑(Langlands.Galois.finitePlacesAbove L S)) +
        d.toFun (NumberField.InfinitePlace L → ZMod ℓ)
          (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) (NumberField.InfinitePlace L)) -
      d.one
```

## Outline of the proofs

Dirichlet's unit theorem in the Library's form (`augmentedFullLogUnitLattice`) embeds `ℤ ⊕ 𝒪_{L,S}ˣ/μ(L)` as a Galois lattice of full rank in `ℝ^{S_L ∪ ∞_L}`; the permutation lattice `ℤ^{S_L ∪ ∞_L}` has the same real span, so `PermutationLattice` gives `g(𝒪_{L,S}ˣ) + g(ℤ) = g(ℤ^{S_L}) + g(ℤ^{∞_L})`, and `g` of a permutation lattice is `d` of the permutation module.

- `g_eq_add_of_exact_of_finite_cokernel`: **Additivity with a finite cokernel.** For `0 → A → B → C` exact with `C/B` finite, `A` and `C` finitely generated: `g(B) = g(A) + g(C)`.
- `g_units`: **The units.** `g(𝒪_Lˣ) = d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)`.
- `g_sUnitsOf`: **The `S`-units.** `g(𝒪_{L,S}ˣ) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)`.

## Declarations

`finite_modN_of_moduleFinite`, `finite_torsN_of_moduleFinite`, `Local.AdditiveFunction.g_congr`, `Local.AdditiveFunction.g_eq_of_surjective_of_finite_ker`, `Local.AdditiveFunction.g_eq_add_of_exact_of_finite_cokernel`, `distribMulActionOfAut`, `instAddCommGroupAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion_langlands`, `g_units`, `sUnitsOfAction`, `coe_toMul_sUnitsOfAction_smul`, `g_sUnitsOf`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.2) Proposition, p. 504, and (8.7.3) Corollary, p. 505 (the S-units as a Galois lattice, by Dirichlet's unit theorem).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/UnitsDefs.lean` lines 1–28, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean` lines 1–301. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `sUnitAction` → `sUnitsOfAction`, `g_sUnits` → `g_sUnitsOf`.
