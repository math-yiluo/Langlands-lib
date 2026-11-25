# Reduction of the Euler characteristic formula to modules induced from cyclic quotients

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Cyclic.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a profinite group, `Q ⊆ G` an open normal subgroup and `ℓ` a prime. A finite `𝔽_ℓ[G/Q]`-module
`ρ` gives a smooth `G`-module `infl Q ρ`. A function `χ` of finite smooth `G`-modules with values in
`ℚ_{>0}` that is multiplicative on short exact sequences of modules killed by `ℓ` (`MultKilled`) gives,
for every prime `p`, an additive function `ρ ↦ v_p(χ(infl Q ρ))` on finite `𝔽_ℓ[G/Q]`-modules
(`valFun`). By Artin's induction theorem for additive functions
(`Local.AdditiveFunction.toFun_eq_zero_of_forall_isCyclic`), `χ(infl Q ρ) = 1` as soon as
`χ = 1` on the modules induced from the cyclic subgroups of `G/Q` (`eq_one_of_forall_isCyclic`).

For `G = G_S` of a number field `K`, `Q` the subgroup fixing a finite Galois extension `L ⊆ K_S` and
`χ` the Euler characteristic ratio `globalEulerRatio`, the cyclic subgroups of `Gal(L/K)` are the
groups `Gal(L/L')` with `L/L'` cyclic, and the induced modules are `Ind_{G_S(L')}^{G_S} M`
(`coindResIsoFunRep`). So the formula for a module `M` killed by `ℓ` on which `G_S(L)` acts trivially
follows from the formula for the modules `Ind_{G_S(L')}^{G_S} M`, `L/L'` cyclic
(`globalEulerRatio_eq_one_of_cyclic`). This is the first reduction step of Tate's proof.

```lean
theorem eq_one_of_forall_isCyclic (hmult : MultKilled l χ) (hpos : PosKilled l χ)
    [Finite (G ⧸ (Q : Subgroup G))] {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X)
    (h : ∀ D : Subgroup (G ⧸ (Q : Subgroup G)), IsCyclic D →
      χ (infl Q (funRep ((G ⧸ (Q : Subgroup G)) ⧸ D) ρ)) = 1) :
    χ (infl Q ρ) = 1
theorem globalEulerRatio_eq_one_of_cyclic {ℓ : ℕ}
    [Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, ℓ • m = 0)
    (htriv : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)),
      M.ρ g = 1)
    (hcyc : ∀ (L' : IntermediateField K Ω) [NumberField L']
      (hL' : ∀ x : L', algebraMap L' Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
        GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' →
      IsCyclic ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) →
      globalEulerRatio ι (Rep.coind (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) = 1) :
    globalEulerRatio ι M = 1
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.eq_one_of_forall_isCyclic : ∀ {G : Type u} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] (Q : OpenSubgroup G) [inst_3 : (↑Q).Normal] {l : ℕ} [inst_4 : Fact (Nat.Prime l)]
  {χ : (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) → [Langlands.IsSmoothRep A] → ℚ},
  Langlands.GaloisCohomology.MultKilled l χ →
    Langlands.GaloisCohomology.PosKilled l χ →
      ∀ [Finite (G ⧸ ↑Q)] {X : Type u} [inst_6 : AddCommGroup X] [inst_7 : Module (ZMod l) X] [Finite X]
        (ρ : Representation (ZMod l) (G ⧸ ↑Q) X),
        (∀ (D : Subgroup (G ⧸ ↑Q)),
            IsCyclic ↥D →
              χ (Langlands.GaloisCohomology.infl Q (Langlands.GaloisCohomology.funRep ((G ⧸ ↑Q) ⧸ D) ρ)) = 1) →
          χ (Langlands.GaloisCohomology.infl Q ρ) = 1
@Langlands.GaloisCohomology.globalEulerRatio_eq_one_of_cyclic : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ} [Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ (L : IntermediateField K Ω) [inst_7 : NumberField ↥L]
      (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
      [inst_8 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_9 : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (m : ↑M), ℓ • m = 0) →
        (∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1) →
          (∀ (L' : IntermediateField K Ω) [inst_11 : NumberField ↥L']
              (hL' : ∀ (x : ↥L'), (algebraMap (↥L') Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
              ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) ≤
                  ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL') →
                IsCyclic
                    (↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL') ⧸
                      (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subgroupOf
                        ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL')) →
                  Langlands.GaloisCohomology.globalEulerRatio ι
                      (Rep.coind.{u, u, u, u}
                        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL')).subtype
                        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL')).subtype
                          M)) =
                    1) →
            Langlands.GaloisCohomology.globalEulerRatio ι M = 1
```

## Outline of the proofs

For a prime `p`, the `p`-adic valuation of `χ(infl Q ρ)` is additive in `ρ` by multiplicativity of `χ`, hence vanishes by `Artin` once it vanishes on modules induced from cyclic subgroups; a positive rational with all valuations `0` is `1`. For `G_S`, the module induced from `Gal(L/L')` is `Ind_{G_S(L')}^{G_S}` of the restriction (`coindResIsoFunRep`), and every module killed by `ℓ` and trivial on `G_S(L)` is an inflation.

- `eq_one_of_forall_isCyclic`: **Reduction to cyclic subgroups.** If `χ = 1` on the modules induced from the cyclic subgroups of `G/Q`, then `χ(infl Q ρ) = 1`.
- `globalEulerRatio_eq_one_of_cyclic`: **Reduction to cyclic quotients.** Let `L ⊆ K_S` be finite Galois over `K` and `M` a finite module killed by a prime `ℓ` (with the places above `ℓ` in `S`) on which `G_S(L)` acts trivially. If the formula holds for the modules induced from `G_S(L')` for the fields `K ⊆ L' ⊆ L` with `L/L'` cyclic, it holds for `M`.

## Declarations

`inflHom`, `infl`, `infl_apply`, `finite_infl`, `isSmoothRep_infl`, `rat_eq_one_of_padicValRat`, `MultKilled`, `PosKilled`, `nsmul_eq_zero_of_zmod`, `valFun`, `eq_one_of_forall_isCyclic`, `addAct`, `zmodRepOfAddAct`, `nonempty_iso_of_addEquiv`, `exists_iso_infl_of_module`, `exists_iso_infl`, `coindRes_apply_mul'`, `coindResToFun`, `coindResToFun_mk`, `funToCoindRes_mem`, `coindResEquivFunRep`, `cosetEquiv`, `cosetEquiv_mk`, `cosetEquiv_smul`, `cosetEquiv_symm_smul`, `nonempty_coind_iso_infl_funRep`, `multKilled_globalEulerRatio`, `posKilled_globalEulerRatio`, `exists_fixingOpenSubgroup_eq_comap`, `globalEulerRatio_eq_one_of_cyclic`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 507–508 (reduction, by (7.3.4), to modules induced from cyclic subgroups).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkKilledC.lean` lines 1–238, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkQuotV.lean` lines 1–71, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkCoinfB.lean` lines 1–87, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroCoind.lean` lines 1–223. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `isDiscreteRep_infl` → `isSmoothRep_infl`, `gs_multKilled` → `multKilled_globalEulerRatio`, `gs_posKilled` → `posKilled_globalEulerRatio`, `exists_field_of_cyclic` → `exists_fixingOpenSubgroup_eq_comap`, `zmodRep` → `zmodRepOfAddAct`, `coind_eq_infl_funRep` → `nonempty_coind_iso_infl_funRep`.
