# Additive functions on the Kummer sequence of an open normal subgroup

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/KummerCount.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a profinite group, `N` a closed normal subgroup and `0 → T → O → O → 0` a short exact
sequence of smooth `G`-modules whose second map is multiplication by `n`. Restricted to `N`, its
long exact sequence breaks up into the short exact sequences
`0 → Hⁱ(N, O)/n → Hⁱ⁺¹(N, T) → Hⁱ⁺¹(N, O)[n] → 0` and an isomorphism `H⁰(N, T) ≅ H⁰(N, O)[n]`, and
all these maps commute with the conjugation action of `G` (`kummerModNHom`, `kummerTorsHom`).

When `G/N` is identified with a group `Γ` (`e : G ⧸ N ≃* Γ`), the conjugation action makes the
groups `Hⁱ(N, A)` modules over `Γ` (`conjAction`), and an additive function `d` on finite
`𝔽_n[Γ]`-modules satisfies `d(Hⁱ⁺¹(N, T)) = d(Hⁱ(N, O)/n) + d(Hⁱ⁺¹(N, O)[n])`
(`toFun_eq_modN_add_torsN`) and `d(H⁰(N, T)) = d(H⁰(N, O)[n])` (`toFun_eq_torsN_zero`). With `O` the
`S`-units and `T` the roots of unity this is the Kummer step of Tate's proof of the global Euler
characteristic formula.

```lean
theorem toFun_eq_modN_add_torsN (d : AdditiveFunction.{u} l Γ) (i : ℕ)
    [Finite (ModN (cohomology (Rep.res N.subtype O) i) l)]
    [Finite (TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (φ : X ≃+ cohomology (Rep.res N.subtype T) (i + 1))
    (hφ : ∀ (g : G) (x : X), φ (ρX (e (QuotientGroup.mk g)) x) = (cohomologyConj T N (i + 1) g).hom (φ x)) :
    d.toFun X ρX =
      (letI
theorem toFun_eq_torsN_zero (d : AdditiveFunction.{u} l Γ)
    [Finite (TorsN (cohomology (Rep.res N.subtype O) 0) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (φ : X ≃+ cohomology (Rep.res N.subtype T) 0)
    (hφ : ∀ (g : G) (x : X), φ (ρX (e (QuotientGroup.mk g)) x) = (cohomologyConj T N 0 g).hom (φ x)) :
    d.toFun X ρX =
      (letI
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.toFun_eq_modN_add_torsN : ∀ {G : Type u} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] (N : Subgroup G) [inst_3 : N.Normal] [inst_4 : CompactSpace ↥N] {Γ : Type u_1}
  [inst_5 : Group Γ] (e : G ⧸ N ≃* Γ) {T O : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} [inst_6 : Langlands.IsSmoothRep T]
  [inst_7 : Langlands.IsSmoothRep O] {l : ℕ} {f : T ⟶ O}
  {w : CategoryTheory.CategoryStruct.comp f (l • CategoryTheory.CategoryStruct.id O) = 0},
  { X₁ := T, X₂ := O, X₃ := O, f := f, g := l • CategoryTheory.CategoryStruct.id O, zero := w }.ShortExact →
    ∀ (d : Langlands.GaloisCohomology.Local.AdditiveFunction l Γ) (i : ℕ)
      [inst_8 : Finite (ModN (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) i)) l)]
      [inst_9 :
        Finite
          (Langlands.GaloisCohomology.Local.TorsN
            (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) (i + 1))) l)]
      {X : Type u} [inst_10 : AddCommGroup X] [inst_11 : Module (ZMod l) X] [inst_12 : Finite X]
      (ρX : Representation (ZMod l) Γ X)
      (φ : X ≃+ ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype T) (i + 1))),
      (∀ (g : G) (x : X),
          φ ((ρX (e ↑g)) x) = (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.cohomologyConj T N (i + 1) g)) (φ x)) →
        d.toFun X ρX =
          d.toFun (ModN (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) i)) l)
              (Langlands.GaloisCohomology.Local.modNRep Γ
                (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) i)) l) +
            d.toFun
              (Langlands.GaloisCohomology.Local.TorsN
                (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) (i + 1))) l)
              (Langlands.GaloisCohomology.Local.torsNRep Γ
                (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) (i + 1))) l)
@Langlands.GaloisCohomology.toFun_eq_torsN_zero : ∀ {G : Type u} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] (N : Subgroup G) [inst_3 : N.Normal] [inst_4 : CompactSpace ↥N] {Γ : Type u_1}
  [inst_5 : Group Γ] (e : G ⧸ N ≃* Γ) {T O : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} [inst_6 : Langlands.IsSmoothRep T]
  [inst_7 : Langlands.IsSmoothRep O] {l : ℕ} {f : T ⟶ O}
  {w : CategoryTheory.CategoryStruct.comp f (l • CategoryTheory.CategoryStruct.id O) = 0},
  { X₁ := T, X₂ := O, X₃ := O, f := f, g := l • CategoryTheory.CategoryStruct.id O, zero := w }.ShortExact →
    ∀ (d : Langlands.GaloisCohomology.Local.AdditiveFunction l Γ)
      [inst_8 :
        Finite
          (Langlands.GaloisCohomology.Local.TorsN (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) 0))
            l)]
      {X : Type u} [inst_9 : AddCommGroup X] [inst_10 : Module (ZMod l) X] [inst_11 : Finite X]
      (ρX : Representation (ZMod l) Γ X) (φ : X ≃+ ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype T) 0)),
      (∀ (g : G) (x : X),
          φ ((ρX (e ↑g)) x) = (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.cohomologyConj T N 0 g)) (φ x)) →
        d.toFun X ρX =
          d.toFun
            (Langlands.GaloisCohomology.Local.TorsN
              (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) 0)) l)
            (Langlands.GaloisCohomology.Local.torsNRep Γ
              (↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype O) 0)) l)
```

## Outline of the proofs

The long exact sequence of `0 → T → O → O → 0` over `N`, with multiplication by `n` on `O`, breaks into `0 → Hⁱ(N,O)/n → Hⁱ⁺¹(N,T) → Hⁱ⁺¹(N,O)[n] → 0`; all maps commute with conjugation by `G` (naturality of the connecting map under `cohomologyConj`), so additivity of `d` gives the formula.

- `toFun_eq_modN_add_torsN`: **Kummer in degree `i + 1`.** For an additive function `d` on `𝔽_l[Γ]`-modules and a model `X` of `Hⁱ⁺¹(N, T)` as a `Γ`-module, `d(X) = d(Hⁱ(N, O)/l) + d(Hⁱ⁺¹(N, O)[l])`.
- `toFun_eq_torsN_zero`: **Kummer in degree `0`.** `d(H⁰(N, T)) = d(H⁰(N, O)[l])`.

## Declarations

`coeffMap_res_nsmul_id_apply`, `nsmul_coeffMap_res_f_apply`, `δ_res_nsmul_apply`, `kummerTorsHom`, `coe_kummerTorsHom_apply`, `range_lsmul_le_ker_δ`, `kummerModNHom`, `kummerModNHom_mk`, `range_lsmul_eq_ker_δ`, `kummerModNHom_injective`, `kummerTorsHom_surjective`, `kummerTorsHom_eq_zero_iff`, `kummerTorsHom_bijective_zero`, `kummerTorsHom_cohomologyConj`, `kummerModNHom_cohomologyConj`, `conjAction`, `conjAction_smul`, `toFun_eq_modN_add_torsN`, `toFun_eq_torsN_zero`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 (the classes (i)–(iii) of H^i(k_S|K, μ_p) in K₀(F_p[G]) from the Kummer sequence); (8.3.4), p. 453 (the Kummer sequence of the S-units).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/KummerSeq.lean` lines 1–275, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/Kummer.lean` lines 1–218. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `cohomologyMap_res_nsmul_apply` → `coeffMap_res_nsmul_id_apply`, `nsmul_cohomologyMap_res_f_apply` → `nsmul_coeffMap_res_f_apply`, `conjActionOf` → `conjAction`, `conjActionOf_smul` → `conjAction_smul`.
