# Duality by dévissage

`Langlands/Cohomology/Profinite/Duality/Devissage.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a compact group `Γ`, a module `D ≅ ℤ/n` and `t : H²(Γ, D) → ℤ/n` satisfying hypotheses on
all open subgroups (finiteness of `H²` and vanishing of `H³` for finite modules killed by `n`,
`t ∘ cor` bijective on `H²(W, D)`, perfect cup product pairing on `H¹(W, ℤ/n) × H¹(W, D)`), the
duality map `Hʳ(Γ, M) → Hom(H^{2-r}(Γ, M*), ℤ/n)` is bijective for every finite smooth module `M`
killed by `n` and `r = 0, 1, 2`. The proof treats the coinduced modules `Coind_W ℤ/n` by
Shapiro's lemma, then embeds a general `M` into a finite sum of them and runs the five lemma on
the long exact sequences, degree by degree.

## Declarations

Duals of coinduced modules.

- `coind_trivial_apply_mul`, `coindSingleFun`, `coindSingle` (`coindSingleFun_apply`,
  `coindSingle_hom_apply`), `coindDualPairingFun`, `coindDualPairing` (`coindDualPairing_tmul`,
  `res_coindDualPairing_comp_coindEvalOne`), `coindDualRestrict`, `coindDualInv`,
  `res_coindDualInv_comp_coindEvalOne`, `sum_ite_mul_out_mem`, `sum_coindSingle`,
  `coindDualHom`, `tensorHom_coindDualHom_evalPairing`, `coindDualInv_comp_coindDualHom`,
  `coindDualHom_comp_coindDualInv`, and `coindDualIso`: for `W` of finite index, the dual of
  `Coind_W^Γ V` is `Coind_W^Γ` of the dual of `V`, compatibly with the evaluation pairings.
- Instances `finite_coind_trivial`, `isSmoothRep_coind_trivial`, `isSmoothRep_dualRep_res_trivial`,
  `isSmoothRep_coind_dualRep_res_trivial`, `isSmoothRep_dualRep_coind_trivial`;
  `cupPairing_evalPairing_coindDualHom`.

Degree `0` against degree `2`, and the coinduced case.

- `unitHom A a ha` (the morphism from the unit object to an invariant vector, `unitHom_hom_apply`),
  `zmodRep_ρ_apply`, `zmodH0Class` (`H⁰(H, ℤ/n) = ℤ/n`, `zmodH0Class_surjective`),
  `unitHom_tensorHom_zmodMulPairing`, `cupPairing_zmodH0Class`, `bijective_zmodMulPairing_zero`.
- `bijective_of_bijective_comp`, `bijective_of_transport` (bijectivity of `x ↦ T ∘ B(·, x)` is
  preserved by isomorphisms compatible with the pairings and by a unit multiple of the trace),
  `bijective_cohomologyMap_of_comp_eq_id`; instances
  `finite_uliftZMod`, `finite_coind_zmodRep`, `isSmoothRep_coind_zmodRep`,
  `isSmoothRep_dualRep_coind_zmodRep`; `nsmul_coind_zmodRep_eq_zero`.
- `bijective_dualityMap_coind`: for `Coind_W^Γ ℤ/n` the duality maps of degree `r ≤ 1` are
  bijective (by Shapiro's lemma, from the hypotheses on `W`).

Dévissage.

- `injective_cohomologyMap_zero`, `dualityMap_δ` (compatibility of the duality maps with
  connecting maps, with the sign of `cupPairing_δ_eq`).
- `GroupDualityHypotheses n D t` (structure, fields `nonempty_addEquiv`, `finite_two`,
  `subsingleton_three`, `bijective_cores`, `isPerfectPairing`), with `finite_D`, `nsmul_D`, and
  `exists_devissage` (an embedding of `M` into a finite sum of coinduced modules with cokernel
  again finite and killed by `n`).
- `GroupDualityHypotheses.injective_zero`, `surjective_zero`, `bijective_zero`,
  `injective_one`, `surjective_one`, `bijective_one`: degrees `0` and `1`.
- `tensorHom_toDualDual_evalPairing`, `cupPairing_toDualDual`, `dualityMap_two_eq`: degree `2`
  from degree `0` by biduality; `GroupDualityHypotheses.bijective_two`.
- `GroupDualityHypotheses.bijective_dualityMap`: the duality map is bijective for every finite
  smooth `M` killed by `n` and `r + s = 2`.

Finite modules killed by `2`.

- `exists_ne_zero_forall_ρ_eq N h2 hN`: a group acting on a nonzero finite module `N` killed by `2`
  through elements of `2`-power order fixes a nonzero vector (`#N ≡ #N^R (mod 2)` for the `2`-group
  `R`, the image of the action).
- `zmodTwoAddHom m hm : ℤ/2 →+ N` for `m` with `2m = 0` (`zmodTwoAddHom_intCast`,
  `zmodTwoAddHom_one`, `zmodTwoAddHom_injective`); `zmodTwoHom N m hm hfix : ℤ/2 ⟶ N`, the morphism of
  `W`-modules sending `1` to a fixed vector `m` (`zmodTwoHom_hom_apply`).

Complete types of `bijective_of_transport` and of the declarations on modules killed by `2`, as printed by
`PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.bijective_of_transport.{u_1, u_2, u_3, u_4, u_5, u_6} {n : ℕ} {X : Type u_1}
  {X' : Type u_2} {Y : Type u_3} {Y' : Type u_4} {W : Type u_5} {W' : Type u_6} [AddCommGroup X] [AddCommGroup X']
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup W] [AddCommGroup W'] (B : Y →+ X →+ W) (B' : Y' →+ X' →+ W')
  (T : W →+ ZMod n) (f : W' →+ ZMod n) (eX : X ≃+ X') (eY : Y ≃+ Y') (eW : W ≃+ W')
  (hcup : ∀ (y : Y) (x : X), (B' (eY y)) (eX x) = eW ((B y) x)) (c : ZMod n) (hc : IsUnit c)
  (hf : ∀ (w : W), f (eW w) = c * T w) (hbij : Function.Bijective fun x => T.comp (B.flip x)) :
  Function.Bijective fun x' => f.comp (B'.flip x')
Langlands.ProfiniteCohomology.exists_ne_zero_forall_ρ_eq.{u} {W : Type u} [Group W]
  (N : Rep.{u, u, u} (ULift.{u, 0} ℤ) W) [Finite ↑N] [Nontrivial ↑N] (h2 : ∀ (m : ↑N), 2 • m = 0)
  (hN : ∀ (w : W), ∃ k, N.ρ (w ^ 2 ^ k) = 1) : ∃ m, m ≠ 0 ∧ ∀ (w : W), (N.ρ w) m = m
Langlands.ProfiniteCohomology.zmodTwoAddHom.{u_1} {N : Type u_1} [AddCommGroup N] (m : N) (hm : 2 • m = 0) : ZMod 2 →+ N
Langlands.ProfiniteCohomology.zmodTwoAddHom_injective.{u_1} {N : Type u_1} [AddCommGroup N] {m : N} (hm : 2 • m = 0)
  (hm0 : m ≠ 0) : Function.Injective ⇑(Langlands.ProfiniteCohomology.zmodTwoAddHom m hm)
Langlands.ProfiniteCohomology.zmodTwoAddHom_intCast.{u_1} {N : Type u_1} [AddCommGroup N] (m : N) (hm : 2 • m = 0)
  (k : ℤ) : (Langlands.ProfiniteCohomology.zmodTwoAddHom m hm) ↑k = k • m
Langlands.ProfiniteCohomology.zmodTwoAddHom_one.{u_1} {N : Type u_1} [AddCommGroup N] (m : N) (hm : 2 • m = 0) :
  (Langlands.ProfiniteCohomology.zmodTwoAddHom m hm) 1 = m
Langlands.ProfiniteCohomology.zmodTwoHom.{u} {W : Type u} [Group W] (N : Rep.{u, u, u} (ULift.{u, 0} ℤ) W) (m : ↑N)
  (hm : 2 • m = 0) (hfix : ∀ (w : W), (N.ρ w) m = m) : Langlands.ProfiniteCohomology.zmodRep W 2 ⟶ N
Langlands.ProfiniteCohomology.zmodTwoHom_hom_apply.{u} {W : Type u} [Group W] (N : Rep.{u, u, u} (ULift.{u, 0} ℤ) W)
  (m : ↑N) (hm : 2 • m = 0) (hfix : ∀ (w : W), (N.ρ w) m = m) (a : ↑(Langlands.ProfiniteCohomology.zmodRep W 2)) :
  (Rep.Hom.hom (Langlands.ProfiniteCohomology.zmodTwoHom N m hm hfix)) a =
    (Langlands.ProfiniteCohomology.zmodTwoAddHom m hm) a.down
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/InducedDual.lean`,
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/Induced.lean` and
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/Devissage.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's (`cohomologyCores` → `cores`,
`H0Iso` → `zeroIso`). `exists_ne_zero_forall_ρ_eq` and the declarations on `ℤ/2`
(`zmodTwoAddHom`, …, `zmodTwoHom_hom_apply`) are from
`src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingIndex.lean`, with the source's names;
`bijective_of_transport` contains no text of the source.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter II, §5.2, Theorem 2, pp. 91–92 (Tate's local duality theorem for
  finite `G_k`-modules, `k` a `p`-adic field). Serre deduces it from the dualizing module of chapter
  I, §3.5, and an embedding argument in degree 1; the proof by dévissage, due to Poitou, is only
  mentioned (Remark 1, p. 92).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §4, Theorem (3.4.1) and its proof, p. 182 (reduction by an
  exact sequence of free `ℤ[G/U]`-modules and Shapiro's lemma), and Duality Theorem (3.4.6), p. 186.
