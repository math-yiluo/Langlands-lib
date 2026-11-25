# The real places in Tate's base case

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/RealCount.lean`, namespace `Langlands.GaloisCohomology`.

In the situation of Tate's base case with `ℓ` odd, let `w` be a real place of `K`, `c ∈ G_S` the
complex conjugation at `w` and `τ_w` its restriction to `L`. Then `c` acts on `μ_ℓ` by inversion
(`rootsOfUnity_realConj`), so a homomorphism `f : μ_ℓ → M` is fixed by `τ_w` exactly when its value
at a generator lies in `M^{c = -1}`, and `#M = #M^{c} · #M^{c = -1}` (`ℓ` odd). With
`H⁰(K_w, M) = M^c` this gives
`#H⁰(K_w, M) · ℓ^{dim N^{Stab(w̃_w)}} = #M` (`baseCase_card_real`).

```lean
theorem card_tateQuot_eq_one_of_odd {ℓ : ℕ} (hℓ : Odd ℓ) (hM : ∀ m : M, ℓ • m = 0) :
    Nat.card (tateQuot σ) = 1
theorem card_eq_card_fixedSub_mul {ℓ : ℕ} (hℓ : Odd ℓ) (hM : ∀ m : M, ℓ • m = 0)
    (hσ : ∀ x, σ (σ x) = x) :
    Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ))
theorem rootsOfUnity_realConj (w : InfinitePlace K) (hw : w.IsReal) (n : ℕ) (hn : 0 < n)
    (t : rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) n) :
    (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) n).ρ (realConj ι w hw) t = -t
theorem card_cohomology_zero_realLocalModule_eq (w : InfinitePlace K) (hw : w.IsReal) :
    Nat.card (cohomology (realLocalModule ι M w) 0) =
      Nat.card (fixedSub (M.ρ (realConj ι w hw)).toAddMonoidHom)
theorem pow_finrank_stabilizer_eq_card (hTr : Module.finrank (ULift.{u} (ZMod ℓ))
      (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) = 1)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
      ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w)).subtype)) =
      Nat.card (fixedSub (-(M.ρ (realConj ι w hw)).toAddMonoidHom))
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.card_tateQuot_eq_one_of_odd : ∀ {M : Type u_1} [inst : AddCommGroup M] {σ : M →+ M} {ℓ : ℕ},
  Odd ℓ → (∀ (m : M), ℓ • m = 0) → Nat.card (Langlands.GaloisCohomology.Involution.tateQuot σ) = 1
@Langlands.GaloisCohomology.card_eq_card_fixedSub_mul : ∀ {M : Type u_1} [inst : AddCommGroup M] {σ : M →+ M} {ℓ : ℕ},
  Odd ℓ →
    (∀ (m : M), ℓ • m = 0) →
      (∀ (x : M), σ (σ x) = x) →
        Nat.card M =
          Nat.card ↥(Langlands.GaloisCohomology.Involution.fixedSub σ) *
            Nat.card ↥(Langlands.GaloisCohomology.Involution.fixedSub (-σ))
@Langlands.GaloisCohomology.rootsOfUnity_realConj : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K) (hw : w.IsReal) (n : ℕ),
  0 < n →
    ∀ (t : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n)),
      ((Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n).ρ
            (Langlands.GaloisCohomology.realConj ι w hw))
          t =
        -t
@Langlands.GaloisCohomology.card_cohomology_zero_realLocalModule_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (hw : w.IsReal),
  Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M w) 0) =
    Nat.card
      ↥(Langlands.GaloisCohomology.Involution.fixedSub
          (M.ρ (Langlands.GaloisCohomology.realConj ι w hw)).toAddMonoidHom)
@Langlands.GaloisCohomology.pow_finrank_stabilizer_eq_card : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [inst_5 : Fact (Nat.Prime ℓ)]
  {L : Type u} [inst_6 : Field L] [inst_7 : NumberField L] [inst_8 : Algebra K L] [inst_9 : Algebra L Ω]
  [inst_10 : IsScalarTower K L Ω] (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  [inst_11 : IsGalois K L] [inst_12 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
  (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑M]
  (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
  (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Module.finrank (ULift.{u, 0} (ZMod ℓ))
        ↑(Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ
            (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
            ⋯) =
      1 →
    ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      ℓ ^
          Module.finrank (ULift.{u, 0} (ZMod ℓ))
            ↥(Representation.invariants
                (MonoidHom.comp (Langlands.GaloisCohomology.baseTwistRep hL hζ M hMℓ hMP)
                  (MulAction.stabilizer Gal(L/K) (Langlands.GaloisCohomology.infiniteBasePlace hL ι w)).subtype)) =
        Nat.card
          ↥(Langlands.GaloisCohomology.Involution.fixedSub
              (-(M.ρ (Langlands.GaloisCohomology.realConj ι w hw)).toAddMonoidHom))
```

## Outline of the proofs

For an involution `σ` of a finite group killed by an odd number, `M = M^σ ⊕ M^{σ = -1}`; at a real place the complex conjugation acts on `μ_ℓ` by inversion, so `Hom(μ_ℓ, M)^{τ}` is `M^{c = -1}`, and `H⁰(K_w, M) = M^c`.

- `card_tateQuot_eq_one_of_odd`: For an involution of a group killed by an odd number, `M^σ/(1 + σ)M` is trivial.
- `card_eq_card_fixedSub_mul`: For an involution of a finite group killed by an odd number: `#M = #M^σ · #M^{-σ}`.
- `rootsOfUnity_realConj`: Complex conjugation inverts the roots of unity of `K_S`.
- `card_cohomology_zero_realLocalModule_eq`: `H⁰(K_w, M) = M^c` at a real place.
- `pow_finrank_stabilizer_eq_card`: At a real place, `ℓ^{dim N^{Stab(w̃_w)}} = #M^{c = -1}` (`ℓ` odd).

## Declarations

`card_tateQuot_eq_one_of_odd`, `card_eq_card_fixedSub_mul`, `realConj`, `realConj_mul_self`, `rootsOfUnity_realConj`, `card_cohomology_zero_realLocalModule_eq`, `pow_finrank_stabilizer_eq_card`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (7.3.5) Theorem, p. 396 (the Euler characteristic of ℝ), and proof of (8.7.4), pp. 507–508.
