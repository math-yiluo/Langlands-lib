# The Mackey formula in cohomology

`Langlands/Cohomology/Profinite/Mackey/Cohomology.lean`, namespace
`Langlands.ProfiniteCohomology`.

Let `V` be an open subgroup of a compact group `G`, `ι : H → G` a continuous homomorphism from a
compact group and `N` a smooth `V`-module. Then

`Hⁿ(H, Res_ι Coind_V^G N) ≅ ∏_{x ∈ V\G/ι(H)} Hⁿ(H_x, N^x)`, with `H_x = ι⁻¹(x⁻¹ V x)`,

and the component at `x` of the restriction from `G` (through Shapiro's lemma
`Hⁿ(G, Coind N) ≅ Hⁿ(V, N)`) is the map along the conjugation `H_x → V`, `h ↦ x ι(h) x⁻¹`. The
second statement needs a homotopy on cochains: conjugation by `g` on the cochains of `Γ` is
homotopic to the identity, by the classical prism operator.

## Declarations

Cohomology of the Mackey decomposition.

- `mackeyConjₜ V ι x`: `mackeyConj` as a continuous homomorphism (`mackeyConjₜ_toMonoidHom`).
- Instances: `isSmoothRep_res_coind`, `isSmoothRep_mackeyRep_continuousMonoidHom`,
  `isSmoothRep_mackeySummand`, `fintype_mackeyDoubleCoset`.
- `mackeyCohomologyMap V ι N x n`: the projection to the summand `x` followed by Shapiro's map
  `Hⁿ(H, Res Coind N) → Hⁿ(H_x, N^x)`. `isIso_shapiroMap_mackey`.
- `mackeyCohomology_bijective`, `mackeyCohomologyPi`, `mackeyCohomologyPi_apply`,
  `mackeyCohomologyPi_bijective`, `mackeyCohomologyEquiv` (`mackeyCohomologyEquiv_apply`): the
  family of these maps is a linear isomorphism onto the product over double cosets.
- `map_comp_mackeyCohomologyMap`: restriction along `ι` followed by `mackeyCohomologyMap x`
  equals Shapiro's map followed by the map along `mackeyConjₜ V ι x`; `mackeyCohomologyEquiv_map`:
  the same, evaluated.

The conjugation homotopy.

- Index bookkeeping: `seqTuple`, `tupleSeq` (finite tuples and sequences),
  `seqTuple_tupleSeq`, `seqTuple_congr`, `tupleSeq_seqTuple_of_lt`; `prismSeq g i`,
  `contractSeq j`, `prismTuple g i` and their laws (`prismTuple_seqTuple`, `prismSeq_zero_zero`,
  `prismSeq_zero_succ`, `prismSeq_succ_zero`, `prismSeq_succ_succ`, `contractSeq_prismSeq_of_lt`,
  `contractSeq_prismSeq_self`, `contractSeq_prismSeq_of_gt`, `contractSeq_prismSeq_last`);
  `prism_double_sum_eq` (the cancellation of the double sum).
- `conjHomotopyFun A g n`: the prism operator `Cⁿ⁺¹ → Cⁿ` on inhomogeneous cochains;
  `conjCochainFun A g`: the cochain map of conjugation by `g`; `conjHomotopyFun_seqTuple`,
  `d_seqTuple`, and `conjHomotopyFun_spec`, `conjHomotopyFun_spec_zero`:
  `d h + h d = conj_g - id`.
- `continuous_tupleSeq_apply`, `continuous_prismTuple`, `isLocallyConstant_conjHomotopyFun`: the
  prism operator preserves locally constant cochains; `conjHomotopyLinear`, `conjHomotopyHom`.
- `cochains_d_hom_apply_coe`; `cochainsMap_innerConj_sub_id`: the cochain map of
  `(innerConjHom g, innerConjMor A g)` minus the identity is null-homotopic; `conjHomotopy`: the
  homotopy.
- `shapiroCochains V N` (cochain-level Shapiro map, `homologyMap_shapiroCochains`),
  `mackeyCochainsMap V ι N x` (`homologyMap_mackeyCochainsMap`),
  `innerConj_comp_mackeyCochainsMap`, and `mackeyHomotopy V ι N x`: the homotopy behind
  `map_comp_mackeyCohomologyMap`.

- `bijective_mackey_iff_top ψ V N hn htriv`: for a family `ψ_w : F_w → G`, an open subgroup `V` and a
  smooth `V`-module `N`, in positive degree, if the Mackey subgroups `F_w ∩ x⁻¹ V x` other than `F_w`
  are trivial, the maps `Hⁿ(V, N) → Hⁿ(F_w ∩ x⁻¹ V x, N)` along the conjugations over all double
  cosets form a bijection exactly when those over the double cosets with Mackey subgroup `F_w` do.

Complete type of `bijective_mackey_iff_top`, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.bijective_mackey_iff_top.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {κ : Type u} {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)]
  [∀ (w : κ), IsTopologicalGroup (F w)] (ψ : (w : κ) → F w →ₜ* G) (V : OpenSubgroup G) (N : Rep.{u, u, u} k ↥↑V)
  [Langlands.IsSmoothRep N] {n : ℕ} (hn : n ≠ 0)
  (htriv :
    ∀ (w : κ) (d : Langlands.ProfiniteCohomology.MackeyDoubleCoset (↑V) (ψ w).toMonoidHom),
      Langlands.ProfiniteCohomology.mackeySubgroup (↑V) (ψ w).toMonoidHom (Quotient.out d) ≠ ⊤ →
        Subsingleton ↥(Langlands.ProfiniteCohomology.mackeySubgroup (↑V) (ψ w).toMonoidHom (Quotient.out d))) :
  (Function.Bijective fun c w d =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ w) (Quotient.out d))
            (CategoryTheory.CategoryStruct.id
              (Rep.res (↑(Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ w) (Quotient.out d))) N))
            n))
        c) ↔
    Function.Bijective fun c p =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map
            (Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ (↑p).fst) (Quotient.out (↑p).snd))
            (CategoryTheory.CategoryStruct.id
              (Rep.res (↑(Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ (↑p).fst) (Quotient.out (↑p).snd))) N))
            n))
        c
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/MackeyFormula/Cohomology.lean`,
`src/GroundTheory/ProfiniteCohomology/MackeyFormula/ConjHomotopy.lean` and
`src/GroundTheory/ProfiniteCohomology/MackeyFormula/Homotopy.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's. The source's
`MackeyFormula/CompactSupport.lean` and `MackeyFormula/ConeHomotopy.lean` (cohomology with
compact support) belong to the global theory and are not taken here. The source passed
homomorphisms and their continuity separately; here they are bundled as `H →ₜ* G`.

`bijective_mackey_iff_top` is from `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackey.lean`
of the same repository, where it is two statements, `injective_mackeyRealRes_iff` and
`surjective_mackeyRealRes_iff`, combined here into one statement on bijectivity.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, Proposition (1.5.6), p. 51 (double coset formula), and
  §6, Proposition (1.6.3), p. 61 (conjugation).
- K. S. Brown, *Cohomology of Groups* (Springer GTM 87, 1982), chapter III, §8, Proposition (8.3),
  p. 80: `hz = z` for `h ∈ H` and `z ∈ H*(H, M)`. Brown's proof uses no explicit homotopy: with a
  projective resolution `F` of `ℤ` over `ℤG`, conjugation by `g` is induced by
  `f ↦ [x ↦ g f(g⁻¹x)]` on `Hom_H(F, M)`, which is the identity for `g ∈ H`.
