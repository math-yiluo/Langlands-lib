# Cyclic layers with prescribed local degrees

`Langlands/GaloisCohomology/Global/BrauerSequence/CyclicLayers.lean`, namespace
`Langlands.GaloisCohomology`.

`LocalDegreesDvd K L T m`: the local degrees `[L_w : K_v]` of `L/K` at all finite places `w` above
places `v ∈ T` are multiples of `m`.

- `localDegreesDvd_of_algEquiv`: local degrees are invariant under an isomorphism of extensions of
  `K`.
- `exists_primaryPart`: a finite cyclic Galois extension `L/K` has, for each prime `ℓ`, a cyclic
  Galois subextension `M` of `ℓ`-power degree with `[L : M]` prime to `ℓ`;
  `localDegreesDvd_primaryPart`: divisibility of the local degrees by `ℓ^a` passes from `L` to such
  an `M`.
- `localDegreesDvd_of_le`: divisibility of local degrees passes from `E₁` to `E₂ ⊇ E₁`.
- `isCyclic_sup`: the compositum of two finite cyclic Galois extensions of coprime degrees is cyclic,
  of degree dividing the product.
- `cyclotomicLayer K Ω N = K(μ_N) ⊆ Ω`; `cyclotomicLayer_mono`; `fieldRange_le_cyclotomicLayer`: the
  image of `CyclotomicField N K` lies in `K(μ_N)`.
- `exists_cyclic_layer`: for a finite set `T` of finite places and `m ≠ 0` there is a finite
  Galois `E ⊆ Ω` with cyclic Galois group, contained in some `K(μ_N)`, whose local degrees above `T`
  are multiples of `m`.
- `exists_isCyclic_dvd_localDegree`: the field of the same name of `BrauerSequenceData`.

## Complete types

```lean
Langlands.GaloisCohomology.LocalDegreesDvd : (K : Type u_1) →
  (L : Type u_2) →
    [inst : Field K] →
      [NumberField K] →
        [inst_2 : Field L] →
          [NumberField L] →
            [Algebra K L] → Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → ℕ → Prop

@Langlands.GaloisCohomology.localDegreesDvd_of_algEquiv : ∀ {K : Type u_1} {X : Type u_2} {Y : Type u_3}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field X] [inst_3 : NumberField X] [inst_4 : Field Y]
  [inst_5 : NumberField Y] [inst_6 : Algebra K X] [inst_7 : Algebra K Y] (φ : X ≃ₐ[K] Y)
  {T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {m : ℕ},
  Langlands.GaloisCohomology.LocalDegreesDvd K X T m → Langlands.GaloisCohomology.LocalDegreesDvd K Y T m

@Langlands.GaloisCohomology.exists_primaryPart : ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K]
  [inst_2 : Field L] [NumberField L] [inst_4 : Algebra K L] [IsGalois K L] [IsCyclic Gal(L/K)] {ℓ : ℕ},
  Nat.Prime ℓ →
    ∃ (M : IntermediateField K L),
      IsGalois K ↥M ∧ IsCyclic Gal(↥M/K) ∧ (∃ (b : ℕ), Module.finrank K ↥M = ℓ ^ b) ∧ (Module.finrank (↥M) L).Coprime ℓ

@Langlands.GaloisCohomology.localDegreesDvd_primaryPart : ∀ {K : Type u_1} {L : Type u_2} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L] [IsGalois K L]
  (M : IntermediateField K L) [inst_6 : NumberField ↥M]
  {T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ a : ℕ},
  (Module.finrank (↥M) L).Coprime ℓ →
    Langlands.GaloisCohomology.LocalDegreesDvd K L T (ℓ ^ a) →
      Langlands.GaloisCohomology.LocalDegreesDvd K (↥M) T (ℓ ^ a)

@Langlands.GaloisCohomology.localDegreesDvd_of_le : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  {Ω : Type u_2} [inst_2 : Field Ω] [inst_3 : Algebra K Ω] {E₁ E₂ : IntermediateField K Ω} [inst_4 : NumberField ↥E₁]
  [inst_5 : NumberField ↥E₂],
  E₁ ≤ E₂ →
    ∀ {T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {m : ℕ},
      Langlands.GaloisCohomology.LocalDegreesDvd K (↥E₁) T m → Langlands.GaloisCohomology.LocalDegreesDvd K (↥E₂) T m

@Langlands.GaloisCohomology.isCyclic_sup : ∀ {K : Type u_1} [inst : Field K] {Ω : Type u_2} [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K ↥E₁] [FiniteDimensional K ↥E₂]
  [IsGalois K ↥E₁] [IsGalois K ↥E₂] [IsCyclic Gal(↥E₁/K)] [IsCyclic Gal(↥E₂/K)],
  (Module.finrank K ↥E₁).Coprime (Module.finrank K ↥E₂) →
    IsCyclic Gal(↥(E₁ ⊔ E₂)/K) ∧ Module.finrank K ↥(E₁ ⊔ E₂) ∣ Module.finrank K ↥E₁ * Module.finrank K ↥E₂

Langlands.GaloisCohomology.cyclotomicLayer : (K : Type u_1) →
  [inst : Field K] → (Ω : Type u_1) → [inst_1 : Field Ω] → [inst_2 : Algebra K Ω] → ℕ → IntermediateField K Ω

@Langlands.GaloisCohomology.cyclotomicLayer_mono : ∀ {K : Type u_1} [inst : Field K] {Ω : Type u_1} [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] {N N' : ℕ},
  N ∣ N' → Langlands.GaloisCohomology.cyclotomicLayer K Ω N ≤ Langlands.GaloisCohomology.cyclotomicLayer K Ω N'

@Langlands.GaloisCohomology.fieldRange_le_cyclotomicLayer : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (N : ℕ) [NeZero N] (g : CyclotomicField N K →ₐ[K] Ω),
  g.fieldRange ≤ Langlands.GaloisCohomology.cyclotomicLayer K Ω N

@Langlands.GaloisCohomology.exists_cyclic_layer : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (m : ℕ),
  m ≠ 0 →
    ∃ (E : IntermediateField K Ω) (x : FiniteDimensional K ↥E),
      IsGalois K ↥E ∧
        IsCyclic Gal(↥E/K) ∧
          (∃ (N : ℕ), N ≠ 0 ∧ E ≤ Langlands.GaloisCohomology.cyclotomicLayer K Ω N) ∧
            ∀ v ∈ T,
              ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
                [inst_5 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w

Langlands.GaloisCohomology.exists_isCyclic_dvd_localDegree : ∀ (K Ω : Type u_1) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (m : ℕ),
  m ≠ 0 →
    ∃ (E : IntermediateField K Ω) (x : FiniteDimensional K ↥E),
      IsGalois K ↥E ∧
        IsCyclic Gal(↥E/K) ∧
          ∀ v ∈ T,
            ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
              [inst_5 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w
```

## Outline of the proofs

Local degrees are `e · f` (the Library's `localDegree_eq`). Under `φ : X ≃ₐ[K] Y` the places of `Y`
pull back along `RingOfIntegers.mapAlgEquiv φ` with the same ramification index
(`Ideal.ramificationIdx'_comap_eq`) and inertia degree (`Ideal.Quotient.algEquivOfEqComap`). The
`ℓ`-primary part is the fixed field of the subgroup generated by `g^{ℓ^b}`, `g` a generator and `ℓ^b`
the `ℓ`-part of `[L : K]`; its Galois group is a quotient of a cyclic group, and the local degree of
`L` at `q | w | v` is the product of those of `M` at `w` and of `L/M` at `q`
(`Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_tower`), the latter dividing `[L : M]`
(`localDegree_dvd`). The Galois group of a compositum embeds into the product
(`restrictNormalHomSupProd_injective`), which is cyclic for coprime orders
(`Group.isCyclic_prod_iff`). `exists_cyclic_layer` is proved by induction on `m`
(`Nat.recOnPosPrimePosCoprime`), keeping the prime factors of the degree among those of `m`: the
prime-power case is the `ℓ`-primary part of the Library's `CyclotomicSplitting.exists_cyclic_splitting`
moved into `Ω` along an embedding of the cyclotomic field (`IsSepClosed.lift`); the coprime case is
the compositum, with `localDegree_dvd_localDegree` for the local degrees.

## Declarations

`LocalDegreesDvd`, `localDegreesDvd_of_algEquiv`, `exists_primaryPart`, `localDegreesDvd_primaryPart`,
`localDegreesDvd_of_le`, `isCyclic_sup`, `cyclotomicLayer`, `cyclotomicLayer_mono`,
`fieldRange_le_cyclotomicLayer`, `exists_cyclic_layer`, `exists_isCyclic_dvd_localDegree`
(and the private `CyclicLayer`, `cyclicLayer_one`, `cyclicLayer_primePow`, `cyclicLayer_mul` of the
induction).

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It
replaces the source's cyclotomic layers (`CyclotomicLayer.zhatLayer`,
`exists_cyclic_layer_dvd_localDegree`, `GlobalClassFormation/LocalDegrees.lean`) by a proof from
the Library's `Langlands/Global/Arithmetic/CyclotomicSplitting.lean`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): p. 431 (the cyclotomic `ℤ̂`-extension `k̃|k`: its decomposition groups at
  finite primes are open, so the local degrees of its finite layers become divisible by any `m`) and
  Proposition (8.1.9), p. 431 (cyclic extensions suffice, with a totally imaginary quadratic
  extension at the real places).
