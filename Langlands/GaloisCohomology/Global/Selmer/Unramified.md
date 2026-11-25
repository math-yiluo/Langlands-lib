# The unramified condition

`Langlands/GaloisCohomology/Global/Selmer/Unramified.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `S` a finite set of finite places, `G_S = Gal(K_S/K)`, `M` a smooth
`G_S`-module and `v` a finite place. The unramified condition at `v` is the subgroup
`H¹_ur(K_v, M) ⊆ H¹(K_v, M)` of the classes that vanish on the inertia subgroup of `Gal(K̄_v/K_v)`:
`Local.unramifiedClasses` of `Langlands.GaloisCohomology.Local.Unramified` for the local field
`K_v = v.adicCompletion K`, applied to `localModule ι M v` (`unramifiedCondition`,
`mem_unramifiedCondition_iff`).

* For `M` finite, `#H¹_ur(K_v, M) = #H⁰(K_v, M)` (`card_unramifiedCondition`): an unramified condition
  contributes the factor `1` to the formula of Greenberg and Wiles.
* For `N ≥ 1` killing `M`, `S` containing the places above `N`, `v ∈ S` and `#M` a unit at `v`, the
  orthogonal complement of `H¹_ur(K_v, M)` under the local pairing is `H¹_ur(K_v, M')`,
  `M' = Hom(M, μ_N)` (`rightOrthogonal_unramifiedCondition`), so that the dual of a family of
  conditions unramified at `v` is unramified at `v` (`LocalConditions.dual_finite_eq_unramifiedCondition`).
* **The formula over the places where the condition is not the unramified one**
  (`LocalConditions.card_selmerGroup_div_card_selmerGroup_dual_of_unramified`): if
  `L_v = H¹_ur(K_v, M)` for the places `v ∈ S` outside a finite set `T`,
  `#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ T} #L_v / #H⁰(K_v, M)
  · ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`.
* For the zero family: `#Ш¹_S(M) / #H¹(G_S, M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M)⁻¹
  · ∏_{w real} #H⁰(K_w, M)⁻¹ / (#M)^{r₂}` (`card_sha_one_div_card_cohomology_one_dual`).

A coefficient map sends unramified classes to unramified classes and an isomorphism of coefficients
identifies them (`coeffMap_mem_unramifiedClasses`, `coeffMap_mem_unramifiedClasses_iff` of the module
`Langlands.GaloisCohomology.Local.Unramified`); an integer
that is a unit at `v` is a unit of `𝒪_v` and prime to the residue characteristic
(`isUnit_natCast_adicCompletionIntegers`, `coprime_ringChar_of_natCast_not_mem`).

```lean
theorem coprime_ringChar_of_natCast_not_mem {m : ℕ} (hm : ((m : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    letI
def unramifiedCondition (v : HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (cohomology (localModule ι M v) 1)
theorem card_unramifiedCondition [Finite M] (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (unramifiedCondition ι M v) = Nat.card (cohomology (localModule ι M v) 0)
theorem rightOrthogonal_unramifiedCondition
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (v : S) (hv : ((Nat.card M : ℕ) : 𝓞 K) ∉ v.1.asIdeal) :
    rightOrthogonal (localPairing ι N M v) (unramifiedCondition ι M v) =
      unramifiedCondition ι (PoitouTate.dual N M) v
theorem dual_finite_eq_unramifiedCondition
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) {v : S}
    (hL : L.finite v = unramifiedCondition ι M v) (hv : ((Nat.card M : ℕ) : 𝓞 K) ∉ v.1.asIdeal) :
    (L.dual N).finite v = unramifiedCondition ι (PoitouTate.dual N M) v
theorem card_selmerGroup_div_card_selmerGroup_dual_of_unramified
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) (T : Finset S)
    (hT : ∀ v : S, v ∉ T → L.finite v = unramifiedCondition ι M v) :
    (Nat.card L.selmerGroup : ℚ) / Nat.card (L.dual N).selmerGroup =
      (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
        (∏ v ∈ T, (Nat.card (L.finite v) : ℚ) / Nat.card (cohomology (localModule ι M v) 0)) *
        (∏ w : {w : InfinitePlace K // w.IsReal},
          (Nat.card (L.real w) : ℚ) / Nat.card (cohomology (realLocalModule ι M w.1) 0)) /
        (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K
theorem card_sha_one_div_card_cohomology_one_dual
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) :
    letI : Fintype S
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.isUnit_natCast_adicCompletionIntegers : ∀ {K : Type u} [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {m : ℕ},
  ↑m ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal v → IsUnit ↑m
@Langlands.GaloisCohomology.coprime_ringChar_of_natCast_not_mem : ∀ {K : Type u} [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {m : ℕ},
  ↑m ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal v →
    Nat.Coprime m
      (ringChar
        (IsLocalRing.ResidueField
          ↥(Valuation.integer (ValuativeRel.valuation (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))))
@Langlands.GaloisCohomology.unramifiedCondition : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                      AddSubgroup
                        ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 1)
@Langlands.GaloisCohomology.mem_unramifiedCondition_iff : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 1)),
  x ∈ Langlands.GaloisCohomology.unramifiedCondition ι M v ↔
    (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.res (Langlands.GaloisCohomology.localModule ι M v)
            (Langlands.GaloisCohomology.Local.inertia (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
            1))
        x =
      0
@Langlands.GaloisCohomology.card_unramifiedCondition : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [Finite ↑M]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  Nat.card ↥(Langlands.GaloisCohomology.unramifiedCondition ι M v) =
    Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 0)
@Langlands.GaloisCohomology.rightOrthogonal_unramifiedCondition : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] (N : ℕ) [NeZero N] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (v : ↑S),
        ↑(Nat.card ↑M) ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal ↑v →
          Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.GaloisCohomology.localPairing ι N M v)
              (Langlands.GaloisCohomology.unramifiedCondition ι M ↑v) =
            Langlands.GaloisCohomology.unramifiedCondition ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v
@Langlands.GaloisCohomology.LocalConditions.dual_finite_eq_unramifiedCondition : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M) {v : ↑S},
        Langlands.GaloisCohomology.LocalConditions.finite L v = Langlands.GaloisCohomology.unramifiedCondition ι M ↑v →
          ↑(Nat.card ↑M) ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal ↑v →
            Langlands.GaloisCohomology.LocalConditions.finite (Langlands.GaloisCohomology.LocalConditions.dual N L) v =
              Langlands.GaloisCohomology.unramifiedCondition ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v
@Langlands.GaloisCohomology.LocalConditions.card_selmerGroup_div_card_selmerGroup_dual_of_unramified : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M) (T : Finset ↑S),
        (∀ v ∉ T,
            Langlands.GaloisCohomology.LocalConditions.finite L v =
              Langlands.GaloisCohomology.unramifiedCondition ι M ↑v) →
          ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup L)) /
              ↑(Nat.card
                  ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                      (Langlands.GaloisCohomology.LocalConditions.dual N L))) =
            ((↑(Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 0)) /
                    ↑(Nat.card
                        ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M)
                            0)) *
                  ∏ v ∈ T,
                    ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.finite L v)) /
                      ↑(Nat.card
                          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v)
                              0))) *
                ∏ w,
                  ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.real L w)) /
                    ↑(Nat.card
                        ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w)
                            0))) /
              ↑(Nat.card ↑M) ^ NumberField.InfinitePlace.nrComplexPlaces K
@Langlands.GaloisCohomology.card_sha_one_div_card_cohomology_one_dual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ↑(Nat.card ↥(Langlands.GaloisCohomology.sha ι M 1)) /
          ↑(Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1)) =
        ((↑(Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 0)) /
                ↑(Nat.card
                    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0)) *
              ∏ v,
                (↑(Nat.card
                      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v)
                          0)))⁻¹) *
            ∏ w,
              (↑(Nat.card
                    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w)
                        0)))⁻¹) /
          ↑(Nat.card ↑M) ^ NumberField.InfinitePlace.nrComplexPlaces K
```

## Outline of the proofs

- `card_unramifiedCondition`: `Local.card_unramifiedClasses` (`#M^G` unramified classes) and
  `H⁰ = M^G` (`zeroIso`).
- `rightOrthogonal_unramifiedCondition`: the isomorphism `dualIsoCartierDual` of `M'` with the Cartier
  dual respects unramified classes (restriction to inertia commutes with coefficient maps,
  `res_naturality`); `Local.mem_unramifiedClasses_cartierDual_iff` characterizes the unramified
  classes of the Cartier dual as the orthogonal of those of `M` under the Tate pairing, and the local
  pairing is the Tate pairing after `dualToCartier` (`PoitouTate.ptLocalPairing_eq_localTatePairing`).
  The coprimality hypothesis of the local theorem comes from `#M ∉ v`: `#M` is a unit of `𝒪_v`, so
  its image in the finite residue field is not `0`, and the residue characteristic is prime.
- The formula over `T`: the factors at the places outside `T` are `#H⁰(K_v, M)/#H⁰(K_v, M) = 1`
  (`Finset.prod_subset`).
- The zero family: `dual_bot`, `selmerGroup_bot`, `selmerGroup_top`.

## Declarations

`isUnit_natCast_adicCompletionIntegers`, `coprime_ringChar_of_natCast_not_mem`, `unramifiedCondition`, `mem_unramifiedCondition_iff`, `card_unramifiedCondition`, `rightOrthogonal_unramifiedCondition`, `LocalConditions.dual_finite_eq_unramifiedCondition`, `LocalConditions.card_selmerGroup_div_card_selmerGroup_dual_of_unramified`, `card_sha_one_div_card_cohomology_one_dual`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (7.2.15) (unramified classes are mutually orthogonal complements), p. 387; (8.7.9), p. 513
  (`#H¹(G_p/T_p, A^{T_p}) = #H⁰(G_p, A)`, the factor `1` of the unramified places).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §2, Theorem 2.6, p. 30.
