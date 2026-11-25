# Tate–Shafarevich classes of a family and their descent to an open subgroup

`Langlands/GaloisCohomology/Global/EulerCharacteristic/ShaDescent.lean`, namespace `Langlands.GaloisCohomology`.

For a family of continuous homomorphisms `φ_v : H_v → G`, `shaSubmodule φ A n` (of the module
`Langlands.GaloisCohomology.Global.Localization`) is the submodule of the classes of `Hⁿ(G, A)` that
vanish on every `H_v`; it is preserved by the maps of coefficients
(`coeffMap_mem_shaSubmodule`).

For an open normal subgroup `V` whose index is invertible on `A`, the family of `V` is the Mackey
family `mackeyFamily V φ` (the local groups `{h ∈ H_v | x φ_v(h) x⁻¹ ∈ V}` for the double cosets
`V x φ_v(H_v)`), and a class vanishes on every `H_v` exactly when its restriction to `V` vanishes on
the Mackey family (`mem_shaSubmodule_iff_res`): restriction along `h ↦ x φ_v(h) x⁻¹` has the kernel
of restriction along `φ_v` to the open subgroup `{h | x φ_v(h) x⁻¹ ∈ V}` (`map_conj_apply_eq_zero_iff`),
which is injective on `Hⁿ(H_v, A)` since its index divides that of `V`.

```lean
theorem mem_shaSubmodule_iff_res (hA : Function.Bijective fun a : A => (V : Subgroup G).index • a)
    (n : ℕ) (y : cohomology A n) :
    y ∈ shaSubmodule φ A n ↔
      (res A (V : Subgroup G) n).hom y ∈
        shaSubmodule (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.mem_shaSubmodule_iff_res : ∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [CompactSpace G] {ι : Type u} {Hv : ι → Type u}
  [inst_5 : (v : ι) → Group (Hv v)] [inst_6 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  (V : OpenSubgroup G) (A : Rep.{u, u, u} k G) [inst_9 : Langlands.IsSmoothRep A] [(↑V).Normal],
  (Function.Bijective fun (a : ↑A) => (↑V).index • a) →
    ∀ (n : ℕ) (y : ↑(Langlands.ProfiniteCohomology.cohomology A n)),
      y ∈ Langlands.GaloisCohomology.shaSubmodule φ A n ↔
        (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.res A (↑V) n)) y ∈
          Langlands.GaloisCohomology.shaSubmodule (Langlands.GaloisCohomology.mackeyFamily V φ) (Rep.res (↑V).subtype A)
            n
```

## Outline of the proofs

Restriction along `h ↦ x φ_v(h) x⁻¹` equals restriction along `φ_v` to the Mackey subgroup followed by an isomorphism of coefficients (`map_conj_apply_eq_zero_iff`); restriction to an open subgroup of index invertible on `A` is injective (`cohomologyRes_injective_of_bijective`), and the index of a Mackey subgroup divides `[G:V]`.

- `mem_shaSubmodule_iff_res`: **Descent to an open normal subgroup.** If multiplication by `[G : V]` is bijective on `A`, a class of `Hⁿ(G, A)` vanishes on every `H_v` exactly when its restriction to `V` vanishes on the Mackey family of `V`.

## Declarations

`map_coeffMap_apply`, `coeffMap_mem_shaSubmodule`, `mackeyLocalHom`, `isSmoothRep_res_mackeyFamily`, `map_mackeyFamily_res`, `map_mackeyFamily_res_eq_zero_iff`, `index_mackeySubgroup_dvd`, `mem_shaSubmodule_iff_res`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 508 (H^i(k_S|k, A) ≅ H^i(k_S|K, A)^G for [K:k] prime to p).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShaDescent.lean` lines 1–215. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `cohomologyMap_mem_shaSubmodule` → `coeffMap_mem_shaSubmodule`, `cohomologyMapAlong_mackeyFamily_cohomologyRes` → `map_mackeyFamily_res`, `mem_shaSubmodule_iff_cohomologyRes` → `mem_shaSubmodule_iff_res`.
