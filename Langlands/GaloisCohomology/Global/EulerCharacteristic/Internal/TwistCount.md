# Dimensions of cohomology through an open normal subgroup of index prime to `ℓ`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/TwistCount.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a profinite group, `P` an open normal subgroup with quotient identified with a finite
group `Γ` of order prime to the prime `ℓ` (`e : G ⧸ P ≃* Γ`), `T` a smooth `G`-module killed by `ℓ`
of dimension one over `𝔽_ℓ` on which `P` acts trivially, and `M` a finite smooth `G`-module killed by
`ℓ` on which `P` acts trivially. Then `N = Hom(T, M)` is a representation of `Γ` over `𝔽_ℓ`
(`twistRep`) and `X ↦ dim (X ⊗ N)^Γ` is an additive function `twistFun` on finite
`𝔽_ℓ[Γ]`-modules, and
`dim Hⁱ(G, M) = twistFun(Hⁱ(P, T))`
where `Γ` acts on `Hⁱ(P, T)` by conjugation (`finrank_cohomology_eq_twistFun`). This is the
library's coprime twist `finrank_cohomology_eq_finrank_invariants` written with an additive function
on `𝔽_ℓ[Γ]`-modules; it is the first step of Tate's computation of the global Euler characteristic.

```lean
theorem finrank_cohomology_eq_twistFun
    (hTr : Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ T hTℓ) = 1)
    (hP : (((P : Subgroup G).index : ℕ) : ULift.{u} (ZMod ℓ)) ≠ 0)
    (hΓ : Nat.Coprime (Nat.card Γ) ℓ) (i : ℕ) [Finite M]
    [Finite (cohomology (Rep.res (P : Subgroup G).subtype T) i)] :
    (Module.finrank (ULift.{u} (ZMod ℓ)) (cohomology (zmodRepOfTorsion ℓ M hMℓ) i) : ℤ) =
      (letI
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.finrank_cohomology_eq_twistFun : ∀ {G : Type u} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [CompactSpace G] (P : OpenSubgroup G)
  [inst_4 : (↑P).Normal] [inst_5 : CompactSpace ↥↑P] {Γ : Type u} [inst_6 : Group Γ] [inst_7 : Finite Γ]
  (e : G ⧸ ↑P ≃* Γ) (ℓ : ℕ) [inst_8 : Fact (Nat.Prime ℓ)] (T M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [inst_9 : Langlands.IsSmoothRep T] [inst_10 : Langlands.IsSmoothRep M] (hTℓ : ∀ (t : ↑T), ℓ • t = 0)
  (hMℓ : ∀ (m : ↑M), ℓ • m = 0) (hT : ∀ (g : ↥↑P) (t : ↑T), (T.ρ ↑g) t = t) (hM : ∀ (g : ↥↑P) (m : ↑M), (M.ρ ↑g) m = m)
  [inst_11 :
    Module.Finite (ULift.{u, 0} (ZMod ℓ))
      ↑(Langlands.ProfiniteCohomology.homRep (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ T hTℓ)
          (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ))],
  Module.finrank (ULift.{u, 0} (ZMod ℓ)) ↑(Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ T hTℓ) = 1 →
    ↑(↑P).index ≠ 0 →
      ∀ (hΓ : (Nat.card Γ).Coprime ℓ) (i : ℕ) [Finite ↑M]
        [inst_13 : Finite ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑P).subtype T) i)],
        ↑(Module.finrank (ULift.{u, 0} (ZMod ℓ))
              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ) i)) =
          (Langlands.GaloisCohomology.twistFun P e ℓ T M hTℓ hMℓ hT hM hΓ).toFun
            (Langlands.GaloisCohomology.Local.TorsN
              (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑P).subtype T) i)) ℓ)
            (Langlands.GaloisCohomology.Local.torsNRep Γ
              (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑P).subtype T) i)) ℓ)
```

## Outline of the proofs

The Library's coprime twist identifies `Hⁱ(G, M)` with `(Hⁱ(P, T) ⊗ Hom(T, M))^{G/P}` (restriction to `P` is an isomorphism onto the invariants since `[G:P]` is invertible, and `M ≅ T ⊗ Hom(T, M)` over `P`); the dimension is `twistFun` of `Hⁱ(P, T)`, transported along `G/P ≅ Γ` and from `ℤ`-coefficients to `𝔽_ℓ`-coefficients.

- `finrank_cohomology_eq_twistFun`: **Dimensions through the subgroup `P`.** `dim Hⁱ(G, M) = twistFun(Hⁱ(P, T))`, with `Γ` acting on `Hⁱ(P, T)` by conjugation and `Hⁱ(P, T)` viewed as its own `ℓ`-torsion.

## Declarations

`torsNEquivOfNsmul`, `torsNEquivOfNsmul_apply`, `twistRep`, `twistRep_apply`, `twistFun`, `twistFun_apply`, `conj_torsNEquiv`, `finrank_cohomology_eq_twistFun`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 508 (the claim χ([M]) = [M^∨] χ([μ_p]) and the functional Θ(M) = dim M^G).
