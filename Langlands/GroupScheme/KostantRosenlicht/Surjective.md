# Translation-stable subalgebras of a unipotent coordinate algebra

Worker 1497.

The algebraic core of the proof of the Kostant–Rosenlicht theorem
(`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement`; Milne,
*Algebraic Groups* (2017), Theorem 17.64). The setting is that of
`KostantRosenlicht.Hopf`: `B` is the coordinate algebra of the corepresented
group `Corepresented.groupScheme F e` over an algebraically closed field `k`,
finitely generated and reduced, and the group is unipotent.

The route differs from Milne's. Milne passes to the orbit closure and its
reduced boundary; here the orbit map is replaced by an algebra map
`φ : A → B` whose image is stable under right translations, and the
boundary is handled through Chevalley's constructibility theorem and the
Jacobson property instead of reduced subschemes.

## Results

- `algHom_eq_of_ker_eq`: two `K`-points `A → K` with the same kernel are equal
  (`a - χ(a)` lies in both kernels).
- `exists_comp_val_eq`: let `C` be a subalgebra of `B` and `y : C → k` a
  `k`-point whose kernel is `C ∩ P` for some prime `P` of `B`. Then `y` is
  the restriction of a `k`-point of `B`. Proof: enlarge `P` to a maximal ideal
  `M = ker χ` (`exists_algHom_ker_eq`); `C ∩ M` is a proper ideal containing
  the maximal ideal `ker y`, so equals it, and `algHom_eq_of_ker_eq` gives
  `χ|_C = y`.
- `range_comap_val_eq_univ`: if `C ⊆ B` is a finitely generated subalgebra
  stable under every `charTranslate e v`, then every prime of `C` is
  `C ∩ P` for a prime `P` of `B`, i.e. `Spec B → Spec C` is surjective.

  Proof. Let `Y` be the image. Since `C` is Noetherian and `B` is of finite
  type over `C`, the inclusion is of finite presentation and `Y` is
  constructible (`PrimeSpectrum.isConstructible_range_comap`), hence so is
  `Yᶜ`, which is then the image of `Spec S → Spec C` for some ring map
  `g : C → S` (`PrimeSpectrum.exists_range_eq_of_isConstructible`). The map
  `g` is not injective: otherwise a minimal prime of `C` would be contracted
  both from `S` and from `B`
  (`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`), so would lie
  in `Y` and in `Yᶜ`. Pick `f ≠ 0` in `C` with `g f = 0`.

  Let `Zc` be the set of `k`-points of `C` that are not restrictions of
  `k`-points of `B`. For `y ∈ Zc`, `ker y ∉ Y` by `exists_comp_val_eq`, so
  `ker y` is contracted from `S` and contains `ker g ∋ f`; thus `f` vanishes
  on `Zc`. If `y ∈ Zc` then `y ∘ τ_v ∈ Zc` for every translation `τ_v` of
  `C`: were `y ∘ τ_v = χ|_C`, then
  `y = (χ ∘ charTranslate e (charInv e v))|_C` by
  `charTranslate_charTranslate_charInv`. Hence the subspace
  `W = {c ∈ C | y c = 0 for all y ∈ Zc}` of `B` is stable under all
  `charTranslate e v` and contains `f ≠ 0`. By
  `rightAct_mem_of_charTranslate_mem` and `one_mem_of_rightAct_mem`
  (unipotence), `1 ∈ W`; since `y 1 = 1`, `Zc` is empty.

  So every `k`-point of `C` is a restriction, and by the Nullstellensatz
  every maximal ideal of `C` lies in `Y`. The constructible set `Yᶜ` has no
  maximal ideal, and `C` is Jacobson (`isJacobsonRing_of_finiteType`), so
  `Yᶜ = ∅` by `eq_empty_of_isConstructible`.

- `range_comap_eq_zeroLocus` (the exported result): let `A` be a finitely
  generated `k`-algebra and `φ : A →ₐ[k] B` such that every right translate
  `charTranslate e v (φ a)` is again of the form `φ a'`. Then the image of
  `PrimeSpectrum.comap φ : Spec B → Spec A` is the closed set
  `zeroLocus (ker φ)`. Proof: apply the previous result to `C = φ.range`
  (finitely generated as the image of `A`); `φ` factors as the surjection
  `A → C` followed by the inclusion, the inclusion is surjective on spectra,
  and the image for the surjection is `zeroLocus (ker φ)`
  (`range_comap_of_surjective`, `AlgHom.ker_rangeRestrict`).

In the application, `φ` is the coordinate map of the orbit morphism of a
rational point and the stability hypothesis expresses equivariance of the
orbit map for right translations.
