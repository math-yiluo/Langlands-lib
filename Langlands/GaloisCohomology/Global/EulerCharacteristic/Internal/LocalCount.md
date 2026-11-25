# The dual module and the local terms in Tate's base case

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/LocalCount.lean`, namespace `Langlands.GaloisCohomology`.

In the situation of Tate's base case (`L ⊆ K_S` Galois over `K` of degree prime to `ℓ`, `μ_ℓ ⊆ L`,
`M` killed by `ℓ` and trivial on `G_S(L)`), with `N = Hom(μ_ℓ, M)` as a representation of
`Γ = Gal(L/K)`:

* `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)` (`card_cohomology_zero_dual`): `H⁰(G_S, M')` is
  `Hom_Γ(M, μ_ℓ)`, which has the dimension of `Hom_Γ(μ_ℓ, M) = N^Γ` because `#Γ` is prime to `ℓ`
  (`finrank_invariants_linHom_comp_line`);
* `#H²(K_v, M) = ℓ^{dim N^{D_v}}` at a finite place `v` (`card_cohomology_two_localModule`), by
  local duality `#H²(K_v, M) = #H⁰(K_v, M^∨)` (Cartier dual) and the same comparison for the
  decomposition group `D_v`.

```lean
theorem finrank_invariants_linHom_comp_line (q : H₀ →* Γ) (hT1 : finrank k T = 1)
    (hD : ((Nat.card q.range : ℕ) : k) ≠ 0) :
    finrank k (linHom (ρA.comp q) (ρT.comp q)).invariants =
      finrank k (Representation.invariants ((linHom ρT ρA).comp q.range.subtype))
theorem card_hom_res_eq_pow {H₀ : Type u} [Group H₀] (φ : H₀ →* G) :
    Nat.card (Rep.res φ M ⟶ Rep.res φ T) = ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ))
      (Representation.invariants ((twistRep P e ℓ T M hTℓ hMℓ hT hM).comp
        ((quotHom P e).comp φ).range.subtype))
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.finrank_invariants_linHom_comp_line : ∀ {k : Type u} [inst : Field k] {Γ : Type u_1}
  [inst_1 : Group Γ] [Finite Γ] {H₀ : Type u_2} [inst_3 : Group H₀] {T A : Type u} [inst_4 : AddCommGroup T]
  [inst_5 : Module k T] [inst_6 : AddCommGroup A] [inst_7 : Module k A] (ρT : Representation k Γ T)
  (ρA : Representation k Γ A) [FiniteDimensional k T] [FiniteDimensional k A] (q : H₀ →* Γ),
  Module.finrank k T = 1 →
    ↑(Nat.card ↥q.range) ≠ 0 →
      Module.finrank k ↥(Representation.linHom (MonoidHom.comp ρA q) (MonoidHom.comp ρT q)).invariants =
        Module.finrank k ↥(Representation.invariants (MonoidHom.comp (ρT.linHom ρA) q.range.subtype))
@Langlands.GaloisCohomology.card_hom_res_eq_pow : ∀ {G : Type u} [inst : Group G] [inst_1 : TopologicalSpace G]
  (P : OpenSubgroup G) [inst_2 : (↑P).Normal] {Γ : Type u} [inst_3 : Group Γ] [Finite Γ] (e : G ⧸ ↑P ≃* Γ) (ℓ : ℕ)
  [inst_5 : Fact (Nat.Prime ℓ)] (T M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Finite ↑T] [Finite ↑M]
  (hTℓ : ∀ (t : ↑T), ℓ • t = 0) (hMℓ : ∀ (m : ↑M), ℓ • m = 0) (hT : ∀ (g : ↥↑P) (t : ↑T), (T.ρ ↑g) t = t)
  (hM : ∀ (g : ↥↑P) (m : ↑M), (M.ρ ↑g) m = m),
  Module.finrank (ULift.{u, 0} (ZMod ℓ)) ↑(Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ T hTℓ) = 1 →
    (Nat.card Γ).Coprime ℓ →
      ∀ {H₀ : Type u} [inst_8 : Group H₀] (φ : H₀ →* G),
        Nat.card (Rep.res φ M ⟶ Rep.res φ T) =
          ℓ ^
            Module.finrank (ULift.{u, 0} (ZMod ℓ))
              ↥(Representation.invariants
                  (MonoidHom.comp (Langlands.GaloisCohomology.twistRep P e ℓ T M hTℓ hMℓ hT hM)
                    ((Langlands.GaloisCohomology.quotHom P e).comp φ).range.subtype))
```

## Outline of the proofs

A homomorphism `M → T` of modules restricted along `φ` is an invariant vector of `Hom(M, T)` under the image of `φ`; over `𝔽_ℓ` with `T` one-dimensional, `Hom(M, T) ≅ Hom(T, M)^∨`, so its invariants under `D` have dimension `dim Hom(T, M)^D` (`DualDimension`).

- `finrank_invariants_linHom_comp_line`: **Homomorphisms to and from `T` through a finite quotient.** For `q : H₀ → Γ` with image `D` of order invertible in `k` and `T` of dimension one: `dim Hom_{H₀}(A, T) = dim Hom_D(T, A)`.
- `card_hom_res_eq_pow`: **Invariant homomorphisms into `μ_ℓ`.** For a group `H₀` mapping to `G` through `φ` with image `D` in `Γ`: `#Hom_{H₀}(M, T) = ℓ^{dim Hom(T, M)^D}`.

## Declarations

`linHom_comp`, `finrank_invariants_linHom_comp_line`, `zmodLinearOfAddHom`, `zmodLinearOfIntLinear`, `homEquivInvariants`, `quotRepZMod`, `quotHom`, `quotRepZMod_comp`, `zmodRepOfTorsion_res_eq`, `linHom_quotRepZMod`, `card_hom_res_eq_pow`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 506–507 (the local terms).
