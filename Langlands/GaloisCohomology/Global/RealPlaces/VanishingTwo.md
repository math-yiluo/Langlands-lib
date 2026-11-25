# The localization of `Hʳ(G_S, ℤ/2)` to the real places, `r ≥ 3`

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingTwo.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` containing the places
above `2`, `G_S = Gal(K_S/K)` and `ι : PlaceEmbeddings K Ω`.

**Theorem** (`bijective_realLocalization_zmodRep_two`). For every `r ≥ 3` the localization
`Hʳ(G_S, ℤ/2) → ∏_{w real} Hʳ(K_w, ℤ/2)` is bijective.

On the way:

* `realLocalization_coeffMap`: the localization at an infinite place is natural in the module;
  `bijective_realLocalization_of_iso`: bijectivity of the localization to the real places is preserved by
  isomorphisms of modules (with `bijective_coeffMap_of_iso` of the module
  `Langlands.Cohomology.Profinite.Functoriality`).
* `dualizingModule_two_ρ_apply`: `G_S` acts trivially on `μ₂`; `dualizingModuleTwoIso`: `ℤ/2 ≅ μ₂`.
* For a subgroup `U` of a group `G` and `c ∉ U` with `g c⁻¹ ∈ U` for every `g ∉ U` (index `2`):
  `coindSumTwo` (`f ↦ f(1) + f(c)` on `Ind_U^G(ℤ/2)`), `coindQuotientZModTwo` and
  `coindQuotientZModTwoIso : Ind_U^G(ℤ/2)/(ℤ/2) ≅ ℤ/2`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.realLocalization_coeffMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (f : A ⟶ B) (w : NumberField.InfinitePlace K) (r : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology A r)) :
  (Langlands.GaloisCohomology.realLocalization ι B w r)
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap f r)) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap ((Rep.resFunctor ↑(Langlands.Galois.realLocalizationHom ι S w)).map f)
          r))
      ((Langlands.GaloisCohomology.realLocalization ι A w r) x)
Langlands.GaloisCohomology.bijective_realLocalization_of_iso.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (e : A ≅ B) (r : ℕ)
  (h : Function.Bijective fun x w => (Langlands.GaloisCohomology.realLocalization ι A (↑w) r) x) :
  Function.Bijective fun x w => (Langlands.GaloisCohomology.realLocalization ι B (↑w) r) x
Langlands.GaloisCohomology.dualizingModule_two_ρ_apply.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
  (x : ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2)) :
  ((Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2).ρ σ) x = x
Langlands.GaloisCohomology.dualizingModuleTwoIso.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) :
  Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) 2 ≅
    Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2
Langlands.GaloisCohomology.coindSumTwo.{u} {G : Type u} [Group G] (U : Subgroup G) (c : G) :
  ↑(Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2))) →ₗ[ULift.{u, 0} ℤ]
    ULift.{u, 0} (ZMod 2)
Langlands.GaloisCohomology.coindSumTwo_apply.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G}
  (f : ↑(Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2)))) :
  (Langlands.GaloisCohomology.coindSumTwo U c) f = ↑f 1 + ↑f c
Langlands.GaloisCohomology.coind_zmodRep_apply_mul.{u} {G : Type u} [Group G] (U : Subgroup G)
  (f : ↑(Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2)))) {u : G}
  (hu : u ∈ U) (x : G) : ↑f (u * x) = ↑f x
Langlands.GaloisCohomology.mul_mem_of_not_mem.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g ∉ U, g * c⁻¹ ∈ U) {g : G} (hg : g ∉ U) : c * g ∈ U
Langlands.GaloisCohomology.coindSumTwo_ρ.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g ∉ U, g * c⁻¹ ∈ U) (σ : G)
  (f : ↑(Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2)))) :
  (Langlands.GaloisCohomology.coindSumTwo U c)
      (((Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2))).ρ σ) f) =
    (Langlands.GaloisCohomology.coindSumTwo U c) f
Langlands.GaloisCohomology.coindSumTwo_coindUnit.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G}
  (a : ↑(Langlands.ProfiniteCohomology.zmodRep G 2)) :
  (Langlands.GaloisCohomology.coindSumTwo U c)
      ((Rep.Hom.hom (Langlands.ProfiniteCohomology.coindUnit U (Langlands.ProfiniteCohomology.zmodRep G 2))) a) =
    0
Langlands.GaloisCohomology.coindQuotientZModTwo.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g ∉ U, g * c⁻¹ ∈ U) :
  (Langlands.GaloisCohomology.coindUnitSequence U (Langlands.ProfiniteCohomology.zmodRep G 2)).X₃ ⟶
    Langlands.ProfiniteCohomology.zmodRep G 2
Langlands.GaloisCohomology.coindQuotientZModTwo_mk.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g ∉ U, g * c⁻¹ ∈ U)
  (f : ↑(Rep.coind.{u, u, u, u} U.subtype (Rep.res U.subtype (Langlands.ProfiniteCohomology.zmodRep G 2)))) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.coindQuotientZModTwo U hc hU))
      ((Rep.Hom.hom (Langlands.ProfiniteCohomology.coindUnit U (Langlands.ProfiniteCohomology.zmodRep G 2))).range.mkQ
        f) =
    ↑f 1 + ↑f c
Langlands.GaloisCohomology.bijective_coindQuotientZModTwo.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G}
  (hc : c ∉ U) (hU : ∀ g ∉ U, g * c⁻¹ ∈ U) :
  Function.Bijective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.coindQuotientZModTwo U hc hU))
Langlands.GaloisCohomology.coindQuotientZModTwoIso.{u} {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g ∉ U, g * c⁻¹ ∈ U) :
  (Langlands.GaloisCohomology.coindUnitSequence U (Langlands.ProfiniteCohomology.zmodRep G 2)).X₃ ≅
    Langlands.ProfiniteCohomology.zmodRep G 2
Langlands.GaloisCohomology.bijective_realLocalization_zmodRep_two.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) {r : ℕ}
  (hr : 3 ≤ r) :
  Function.Bijective fun x w =>
    (Langlands.GaloisCohomology.realLocalization ι
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) 2) (↑w) r)
      x
```

## Outline of the proofs

Degree `3` is `bijective_realLocalization_dualizingModule_two` transported along `ℤ/2 ≅ μ₂`. If `K` is
totally complex both sides vanish (`bijective_realLocalization_of_odd_or_isTotallyComplex`). Otherwise
let `U = G_S(K(i))` (`exists_isTotallyComplex_intermediateField`) and `c` the image of the complex
conjugation of a real place: `c ∉ U` and `g c⁻¹ ∈ U` for `g ∉ U`
(`realLocalizationHom_closureConj_not_mem`, `mul_inv_realLocalizationHom_closureConj_mem`). The map
`f ↦ f(1) + f(c)` is invariant (the cosets of `U` are `U` and `Uc`), kills the constants and induces
`Ind_U(ℤ/2)/(ℤ/2) ≅ ℤ/2`; so the dimension shift `bijective_realLocalization_succ` passes from degree `r` to
`r + 1` for `ℤ/2`.

## Declarations

`realLocalization_coeffMap`, `bijective_realLocalization_of_iso`, `dualizingModule_two_ρ_apply`, `dualizingModuleTwoIso`, `coindSumTwo`, `coindSumTwo_apply`, `coind_zmodRep_apply_mul`, `mul_mem_of_not_mem`, `coindSumTwo_ρ`, `coindSumTwo_coindUnit`, `coindQuotientZModTwo`, `coindQuotientZModTwo_mk`, `bijective_coindQuotientZModTwo`, `coindQuotientZModTwoIso`, `bijective_realLocalization_zmodRep_two`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingUnitsTwo.lean` (lines 143–174: `galRootsOfUnity_two_ρ_apply`, `nonempty_rootsOfUnity_two_iso_zmodRep`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The iso is a definition for the Library's `dualizingModule K Ω S 2` and `zmodRep`; the rest of the file (naturality, the quotient of the induced module, the induction on the degree) has no counterpart in the source, which obtains the degrees `≥ 4` from the units of `K_S`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VII, §2, (7.2.17), p. 390 (duality for `G(ℂ|ℝ)`; in its proof the Kummer sequence `1 → μ₂ → ℂˣ → ℂˣ → 1` gives `H²(G, ℂˣ) ≅ H³(G, μ₂)`).
