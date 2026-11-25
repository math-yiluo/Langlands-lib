# The Artin conductor of a difference of two induced characters is an integer

Module `Langlands.LocalFactor.Ramification.InducedRankOneDifference`, namespace
`Langlands.Ramification.Padic`; auxiliary definitions in
`Langlands.Ramification.Padic.InducedRankOneDifference`.

Let `F/K` be a finite Galois extension of p-adic fields with group
`G = F.Carrier ≃ₐ[K] F.Carrier`, valuation data `T` on `F`, inertia group `G_0 = inertia T K`.
For a subgroup `S ≤ G` with fixed field `K_S` and two characters `χ, χ'` of `S`, this module
proves that `a_K(Ind_S χ) − a_K(Ind_S χ')` is an integer: it is `[G : S ⊔ G_0]` times the
difference of the Artin conductors over `K_S` of the corresponding characters of `Gal(F/K_S)`,
which are natural numbers. These are the generators of the degree-zero Brauer theorem used by
`Langlands.LocalFactor.Ramification.FiniteIntegralityProof`.

## Statements

**The residue degree as an index** (variables of `Langlands.LocalFactor.Ramification.InductionStatement`:
`{p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)`, `(K : Type uK)` and
`(K' : Type uK')` in a scalar tower `ℚ_p → K → K' → F` with the five instances on `K'`):

```lean
theorem Langlands.Ramification.Padic.inertia_index_eq_mul :
    (inertia T K).index = (inertia T K').index *
      ((AlgEquiv.restrictScalarsHom (S := K') (A := F.Carrier) K).range ⊔ inertia T K).index
```

So the coefficient `(inertia T K).index / (inertia T K').index` of the Library's induction formula
(the residue degree of `K'/K`) is the natural number
`[G : Gal(F/K') ⊔ G_0]`. No Galois hypothesis is used.

**The scalar tower through an intermediate field** (instance):

```lean
instance Langlands.Ramification.Padic.intermediateFieldPadicScalarTower
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} {K : Type uK} [Field K]
    [Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (E : IntermediateField K F.Carrier) : IsScalarTower (Padic p) E F.Carrier
```

It lets an intermediate field of `F/K` serve as the field `K'` of the induction formula; the
Library's `fixedFieldPadicScalarTower` (module `Herbrand.ArithmeticStatement`) is the case of a
base given as a `PadicField`.

**The difference identity and its integrality**, for `T`, `{K : Type uK}` with
`[Field K] [Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
[FiniteDimensional K F.Carrier]`:

```lean
theorem Langlands.Ramification.Padic.artinConductor_ind_sub_eq [IsGalois K F.Carrier]
    (S : Subgroup (F.Carrier ≃ₐ[K] F.Carrier)) (χ χ' : S →* ℂˣ) :
    artinConductor T K (Representation.ind S.subtype (FiniteRep.oneDimensional χ).ρ) -
        artinConductor T K (Representation.ind S.subtype (FiniteRep.oneDimensional χ').ρ) =
      ((S ⊔ inertia T K).index : ℚ) *
        (artinConductor T (InducedRankOneDifference.fixedField S)
            (LocalClassField.rankOneCharacterRepresentation
              (InducedRankOneDifference.transportCharacter S χ)) -
          artinConductor T (InducedRankOneDifference.fixedField S)
            (LocalClassField.rankOneCharacterRepresentation
              (InducedRankOneDifference.transportCharacter S χ')))

theorem Langlands.Ramification.Padic.exists_int_artinConductor_ind_sub [IsGalois K F.Carrier]
    (S : Subgroup (F.Carrier ≃ₐ[K] F.Carrier)) (χ χ' : S →* ℂˣ) :
    ∃ z : ℤ,
      artinConductor T K (Representation.ind S.subtype (FiniteRep.oneDimensional χ).ρ) -
        artinConductor T K (Representation.ind S.subtype (FiniteRep.oneDimensional χ').ρ) =
      (z : ℚ)
```

`InducedRankOneDifference.fixedField S` is `IntermediateField.fixedField S`, and
`transportCharacter S χ = χ ∘ e_S⁻¹` with `e_S = IntermediateField.subgroupEquivAlgEquiv S :
S ≃* Gal(F/K_S)`. The hypothesis `[FiniteDimensional K F.Carrier]` is always true here
(`Module.Finite.of_restrictScalars_finite`); it makes `G` finite, hence `S` of finite index and
the induced spaces finite-dimensional, which the statements need in order to elaborate.

## Proof outline

1. *Index* (`inertia_index_eq_mul`): `G_0 = G_0(K)` and `Gal(F/K')_0` is the preimage of `G_0`
   under restriction of scalars (`lowerRamificationGroup_zero`, `lowerRamificationGroup_comap`).
   The index of a preimage is a relative index (`Subgroup.index_comap`); since `G_0` is normal,
   `[φ.range : φ.range ∩ G_0] = [φ.range ⊔ G_0 : G_0]` (`Subgroup.relIndex_sup_right`), and the
   tower law `Subgroup.relIndex_mul_index` gives the product. This is the identity `r1` inside
   the Library's proof of `finiteGaloisInducedConductor`, at index `0`.
2. *From the subgroup to the fixed field*: `S.subtype = φ_S ∘ e_S` on elements, where
   `φ_S = AlgEquiv.restrictScalarsHom K : Gal(F/K_S) → G` (both sides are the same automorphism of
   `F`). By `FiniteRep.indCongrEquiv` (module `Langlands.Representation.Finite.InductionTransport`),
   `Ind_{S.subtype}(oneDimensional χ) ≅ Ind_{φ_S}((oneDimensional χ) ∘ e_S⁻¹)` (`indEquiv`), and
   `(oneDimensional χ) ∘ e_S⁻¹ ≅ rankOne(χ ∘ e_S⁻¹)` by `FiniteRep.oneDimensionalEquiv`
   (`transportEquiv`). Equivalent representations have equal conductors (`artinConductor_equiv`).
3. *Induction formula* (`finiteGaloisInducedConductor T K K_S`, module `InductionProof`) for each
   character: `a_K(Ind_{φ_S} ψ) = dim ψ · a_K(Ind_{φ_S} 1) + ([G:G_0]/[Gal(F/K_S):Gal(F/K_S)_0]) ·
   a_{K_S}(ψ)`. Both representations have dimension `1` (`FiniteRep.oneDimensional_finrank`), so
   the terms with `Ind 1` cancel in the difference. The range of `φ_S` is `S`
   (`range_restrictScalars`, from `e_S` being surjective), so by step 1 the coefficient is
   `[G : S ⊔ G_0]`; `field_simp` and `ring` finish the identity.
4. *Integrality*: by rank-one integrality (`exists_nat_artinConductor_rankOne`, module
   `Langlands.LocalFactor.Ramification.RankOneConductorIntegrality`) over `K_S`, both conductors over
   `K_S` are natural numbers `a, a'`; the difference is `[G : S ⊔ G_0] · (a − a')`.

## Declarations, in order

- `inertia_index_eq_mul`.
- `intermediateFieldPadicScalarTower` (instance).
- In `InducedRankOneDifference`: `fixedField S`, `galoisEquiv S` (`e_S`), `restrictScalars S`
  (`φ_S`), `restrictScalars_galoisEquiv`, `range_restrictScalars`, `transportCharacter S χ`,
  `indEquiv S χ`, `transportEquiv S χ`.
- `artinConductor_ind_sub_eq`, `exists_int_artinConductor_ind_sub`.

## Sources

Serre, *Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`),
Proposition 4 and its corollary (the conductor of an induced representation, printed page 101)
and the proof of Theorem 1′ (printed page 102), where Theorem 1′ for induced characters reduces
to the abelian case. The Library's induction formula has the term `dim ψ · a(Ind 1)` where Serre
has the valuation of the discriminant; in a difference of two characters of the same subgroup that
term cancels, which is how Deligne's degree-zero form of Brauer's theorem is used (Deligne, *Les
constantes des équations fonctionnelles des fonctions L* (1973), Proposition 1.5, printed page
510, literature ID `deligne-1973-local-constants`).
