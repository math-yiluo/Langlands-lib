# Tate–Shafarevich classes through the coprime twist

`Langlands/GaloisCohomology/Global/EulerCharacteristic/ShaTwist.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a profinite group, `P` an open normal subgroup of index invertible in the field `k`, `T`
a smooth `G`-module of dimension one on which `P` acts trivially, `M` a finite-dimensional smooth
`G`-module on which `P` acts trivially, `N = Hom(T, M)`, and `(φ_v : H_v → G)` a family of continuous
homomorphisms. The coprime twist `coprimeTwistEquiv` identifies `Hⁿ(G, M)` with
`(Hⁿ(P, T) ⊗ N)^{G/P}`. Under it:

* a class of `Hⁿ(G, M)` vanishes on every `H_v` exactly when each coordinate of its image in
  `Hⁿ(P, T) ⊗ N` (for a basis of `N`) vanishes on the Mackey family of `P`
  (`mem_shaSubmodule_iff_coprimeTwistEquiv`): the twist commutes with the coordinate forms of `N`
  (`coeffMap_resTensorFormMor_coord_twistResMap`), and the descent to `P` of `ShaDescent.lean`;
* so if a representation `X` of `G/P` embeds equivariantly into `Hⁿ(P, T)` with image the classes
  vanishing on the Mackey family, the classes of `Hⁿ(G, M)` vanishing on every `H_v` have dimension
  `dim (X ⊗ N)^{G/P}` (`finrank_shaSubmodule_eq_finrank_invariants`).

```lean
theorem mem_shaSubmodule_iff_coprimeTwistEquiv {ιb : Type*} [Fintype ιb]
    (b : Module.Basis ιb k (homRep T M)) (n : ℕ) (x : cohomology M n) :
    x ∈ shaSubmodule φ M n ↔
      ∀ i, coordTensor b i (coprimeTwistEquiv P T M hT hM hTr hP n x : TensorProduct k
        (cohomology (Rep.res (P : Subgroup G).subtype T) n) (homRep T M)) ∈
          shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n
theorem finrank_shaSubmodule_eq_finrank_invariants (n : ℕ) {X : Type u} [AddCommGroup X]
    [Module k X] (ρX : Representation k (G ⧸ (P : Subgroup G)) X)
    (e : X →ₗ[k] cohomology (Rep.res (P : Subgroup G).subtype T) n)
    (he : ρX.IsIntertwiningMap (cohomologyConjRep T (P : Subgroup G) n) e)
    (hinj : Function.Injective e)
    (hrange : ∀ y, y ∈ shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n ↔
      y ∈ LinearMap.range e) :
    Module.finrank k (shaSubmodule φ M n) = Module.finrank k
      (ρX.tprod (quotientRep (P : Subgroup G) (homRep T M)
        (homRep_ρ_of_mem P T M hT hM))).invariants
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.mem_shaSubmodule_iff_coprimeTwistEquiv : ∀ {k G : Type u} [inst : Field k]
  [inst_1 : Group G] [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [inst_5 : (v : ι) → Group (Hv v)] [inst_6 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  (P : OpenSubgroup G) [inst_9 : (↑P).Normal] (T M : Rep.{u, u, u} k G) [inst_10 : Langlands.IsSmoothRep T]
  [inst_11 : Langlands.IsSmoothRep M] (hT : ∀ (g : ↥↑P) (t : ↑T), (T.ρ ↑g) t = t)
  (hM : ∀ (g : ↥↑P) (m : ↑M), (M.ρ ↑g) m = m) [inst_12 : Module.Finite k ↑M] (hTr : Module.finrank k ↑T = 1)
  (hP : ↑(↑P).index ≠ 0) {ιb : Type u_1} [Fintype ιb]
  (b : Module.Basis ιb k ↑(Langlands.ProfiniteCohomology.homRep T M)) (n : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)),
  x ∈ Langlands.GaloisCohomology.shaSubmodule φ M n ↔
    ∀ (i : ιb),
      (Langlands.GaloisCohomology.coordTensor b i)
          ↑((Langlands.ProfiniteCohomology.coprimeTwistEquiv P T M hT hM hTr hP n) x) ∈
        Langlands.GaloisCohomology.shaSubmodule (Langlands.GaloisCohomology.mackeyFamily P φ) (Rep.res (↑P).subtype T) n
@Langlands.GaloisCohomology.finrank_shaSubmodule_eq_finrank_invariants : ∀ {k G : Type u} [inst : Field k]
  [inst_1 : Group G] [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [inst_5 : (v : ι) → Group (Hv v)] [inst_6 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  (P : OpenSubgroup G) [inst_9 : (↑P).Normal] (T M : Rep.{u, u, u} k G) [inst_10 : Langlands.IsSmoothRep T]
  [inst_11 : Langlands.IsSmoothRep M] (hT : ∀ (g : ↥↑P) (t : ↑T), (T.ρ ↑g) t = t)
  (hM : ∀ (g : ↥↑P) (m : ↑M), (M.ρ ↑g) m = m) [Module.Finite k ↑M],
  Module.finrank k ↑T = 1 →
    ↑(↑P).index ≠ 0 →
      ∀ (n : ℕ) {X : Type u} [inst_13 : AddCommGroup X] [inst_14 : Module k X] (ρX : Representation k (G ⧸ ↑P) X)
        (e : X →ₗ[k] ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑P).subtype T) n)),
        ρX.IsIntertwiningMap (Langlands.ProfiniteCohomology.cohomologyConjRep T (↑P) n) e →
          Function.Injective ⇑e →
            (∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑P).subtype T) n)),
                y ∈
                    Langlands.GaloisCohomology.shaSubmodule (Langlands.GaloisCohomology.mackeyFamily P φ)
                      (Rep.res (↑P).subtype T) n ↔
                  y ∈ e.range) →
              Module.finrank k ↥(Langlands.GaloisCohomology.shaSubmodule φ M n) =
                Module.finrank k
                  ↥(ρX.tprod
                        (Langlands.ProfiniteCohomology.quotientRep (↑P) (Langlands.ProfiniteCohomology.homRep T M)
                          ⋯)).invariants
```

## Outline of the proofs

Write the twist `Hⁿ(P, T) ⊗ N → Hⁿ(P, T ⊗ N)` in coordinates for a basis of `N`; maps of coefficients preserve vanishing on the family, and the coordinate forms `T ⊗ N → T` recover the coordinates (`coeffMap_resTensorFormMor_coord_twistResMap`). With the descent of `ShaDescent`, the classes of `Hⁿ(G, M)` vanishing on the family correspond to the invariants of `W ⊗ N`, `W` the classes of `Hⁿ(P, T)` vanishing on the Mackey family; flatness of `N` gives the dimension.

- `mem_shaSubmodule_iff_coprimeTwistEquiv`: **Vanishing on the family through the twist.** A class of `Hⁿ(G, M)` vanishes on every `H_v` exactly when every coordinate of its twist vanishes on the Mackey family of `P`.
- `finrank_shaSubmodule_eq_finrank_invariants`: **Dimension of the classes vanishing on the family.** If `e : X → Hⁿ(P, T)` is an injective `G/P`-equivariant map whose image is the set of classes vanishing on the Mackey family of `P`, the classes of `Hⁿ(G, M)` vanishing on every `H_v` have dimension `dim (X ⊗ N)^{G/P}`, `N = Hom(T, M)`.

## Declarations

`coordTensor`, `coordTensor_tmul`, `sum_coordTensor_tmul`, `coordTensor_rTensor`, `mem_range_rTensor_iff`, `resTensorFormMor`, `coeffMap_resTensorFormMor_twistResMap`, `coeffMap_resTensorFormMor_coord_twistResMap`, `twistResMap_mem_shaSubmodule_iff`, `twistResEquiv_coprimeTwistEquiv`, `mem_shaSubmodule_iff_coprimeTwistEquiv`, `finrank_shaSubmodule_eq_finrank_invariants`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 508 (the claim, through the cup product with Hom(M, F_p)).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShaTwist.lean` lines 1–216. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `cohomologyMap_resTensorFormMor_twistResMap` → `coeffMap_resTensorFormMor_twistResMap`, `cohomologyMap_resTensorFormMor_coord_twistResMap` → `coeffMap_resTensorFormMor_coord_twistResMap`, `coe_coprimeTwistEquiv` → `twistResEquiv_coprimeTwistEquiv`.
