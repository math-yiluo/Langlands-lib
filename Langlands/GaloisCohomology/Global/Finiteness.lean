import Langlands.GaloisCohomology.Global.Dimension.Proof
import Langlands.Global.Arithmetic.SUnitIndex

/-!
# Finiteness of the cohomology of `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` the Galois group of the maximal extension of `K` in `Ω` unramified outside `S`, and
`n ≠ 0` such that every finite place above `n` lies in `S`.

* `finite_cohomology_one_rootsOfUnityModule`, `finite_cohomology_two_rootsOfUnityModule`: for a prime
  `ℓ` with the places above `ℓ` in `S`, `H¹(G_S, μ_ℓ)` and `H²(G_S, μ_ℓ)` are finite (Kummer sequence of
  `S`-units: the `S`-units of `K` are finitely generated, `Pic(𝒪_S)` is finite, and the `ℓ`-torsion of
  `H²(G_S, 𝒪_Sˣ)` embeds into the local Brauer groups at `S` and the real places).
* `finite_cohomology_res_of_le_two`: for an open subgroup `U` of `G_S` and a finite smooth module `M`
  of `U` killed by `n`, `Hʳ(U, M)` is finite for `r ≤ 2` (dévissage to trivial modules over an open
  subgroup fixing `μ_n`, then to `ℤ/ℓ ≅ μ_ℓ`).
* `finite_cohomology_of_le_two`: the same for `G_S`; `finite_cohomology_of_odd_or_isTotallyComplex`:
  all degrees when `n` is odd or `K` totally complex.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain Langlands.ClassFieldTheory.Local

universe u

noncomputable section

section Torsion

/-- An element of `ℚ/ℤ` killed by `m ≠ 0` is the class of `k / m` with `0 ≤ k < m`. -/
theorem exists_fin_eq_rationalClass_of_nsmul_eq_zero {m : ℕ} (hm : m ≠ 0) {q : RationalModIntegers}
    (hq : m • q = 0) : ∃ k : Fin m, q = rationalClass (((k : ℕ) : ℚ) / m) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) q
  have hmr : rationalClass ((m : ℚ) * r) = 0 := by
    rw [← nsmul_eq_mul, map_nsmul]
    exact hq
  obtain ⟨n, hn⟩ :=
    (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).1 hmr
  have hm' : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmod := Int.emod_nonneg n hm'.ne'
  have hlt := Int.emod_lt_of_pos n hm'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hmod
  have hkm : k < m := by omega
  refine ⟨⟨k, hkm⟩, ?_⟩
  change rationalClass r = rationalClass ((k : ℚ) / m)
  have hmq0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnm : (n : ℚ) = (m : ℚ) * ((n / m : ℤ) : ℚ) + (k : ℚ) := by
    have e' : n = (m : ℤ) * (n / m) + (k : ℤ) := by rw [← hk, Int.emod_def]; ring
    exact_mod_cast e'
  have hr : r = ((n / m : ℤ) : ℚ) + (k : ℚ) / m := by
    field_simp
    linarith [hn, hnm]
  rw [hr, map_add,
    (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).2 ⟨n / m, rfl⟩,
    zero_add]

/-- The elements of `ℚ/ℤ` killed by `m ≠ 0` are finitely many. -/
theorem finite_nsmul_eq_zero_rationalModIntegers {m : ℕ} (hm : m ≠ 0) :
    Finite {q : RationalModIntegers // m • q = 0} := by
  choose k hk using fun q : {q : RationalModIntegers // m • q = 0} =>
    exists_fin_eq_rationalClass_of_nsmul_eq_zero hm q.2
  refine Finite.of_injective k fun q q' h => Subtype.ext ((hk q).trans ?_)
  rw [hk q', h]

variable {K : Type u} [Field K] [NumberField K]

/-- The elements of a local Brauer group killed by `m ≠ 0` are finitely many. -/
theorem finite_nsmul_eq_zero_localBrauerGroup (v : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : m ≠ 0) :
    Finite {a : LocalBrauerGroup v // m • a = 0} :=
  have := finite_nsmul_eq_zero_rationalModIntegers hm
  Finite.of_injective
    (fun a => (⟨finiteInvariant v a.1, by rw [← map_nsmul, a.2, map_zero]⟩ :
      {q : RationalModIntegers // m • q = 0}))
    fun a b h => Subtype.ext ((finiteInvariant v).injective (congrArg Subtype.val h))

/-- The elements of the local Brauer group at an infinite place killed by `m ≠ 0` are finitely
many. -/
theorem finite_nsmul_eq_zero_realBrauerGroup (w : InfinitePlace K) {m : ℕ} (hm : m ≠ 0) :
    Finite {b : RealBrauerGroup w // m • b = 0} :=
  have := finite_nsmul_eq_zero_rationalModIntegers hm
  Finite.of_injective
    (fun b => (⟨realInvariantHom w b.1, by rw [← map_nsmul, b.2, map_zero]⟩ :
      {q : RationalModIntegers // m • q = 0}))
    fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [realInvariantHom_apply] at h'
      exact Subtype.ext (realInvariant_injective w h')

end Torsion

section Arithmetic

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- **The `ℓ`-torsion of `H²(G_S, 𝒪_Sˣ)` is finite** for finite `S`: it embeds into the `ℓ`-torsion of
the local Brauer groups at the places of `S` and at the infinite places. -/
theorem finite_nsmul_eq_zero_cohomology_two_maximalSUnits [Finite S] :
    Finite {y : cohomology (maximalSUnitsModule K Ω S) 2 // ℓ • y = 0} := by
  classical
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  have := fun v : S => finite_nsmul_eq_zero_localBrauerGroup v.1 hℓ.ne_zero
  have := fun w : InfinitePlace K => finite_nsmul_eq_zero_realBrauerGroup w hℓ.ne_zero
  let Φ : {y : cohomology (maximalSUnitsModule K Ω S) 2 // ℓ • y = 0} →
      (∀ v : S, {a : LocalBrauerGroup v.1 // ℓ • a = 0}) ×
        (∀ w : InfinitePlace K, {b : RealBrauerGroup w // ℓ • b = 0}) :=
    fun y => (fun v => ⟨brauerLocalization ι v.1 2 (maximalSUnitsInflation K Ω S 2 y.1), by
        rw [← map_nsmul, ← map_nsmul, y.2, map_zero, map_zero]⟩,
      fun w => ⟨realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y.1), by
        rw [← map_nsmul, ← map_nsmul, y.2, map_zero, map_zero]⟩)
  refine Finite.of_injective Φ fun y y' h => Subtype.ext ?_
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine sub_eq_zero.1 (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ hS _ (k := 1) ?_ ?_)
  · rw [pow_one, smul_sub, y.2, y'.2, sub_zero]
  · refine eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_)
    · by_cases hv : v ∈ S
      · rw [map_sub, map_sub, sub_eq_zero]
        exact congrArg Subtype.val (congrFun h1 ⟨v, hv⟩)
      · exact brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv _
    · rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg Subtype.val (congrFun h2 w)

include hℓ hS in
/-- **`H¹(G_S, μ_ℓ)` is finite** for finite `S` containing the places above `ℓ`. -/
theorem finite_cohomology_one_rootsOfUnityModule [Finite S] :
    Finite (cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 1) := by
  classical
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hnS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  have hfg : AddGroup.FG (Additive (S.unit K)) := by
    obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)), (T : Set _) = S :=
      ⟨(Set.toFinite S).toFinset, Set.Finite.coe_toFinset _⟩
    rw [← hT]
    exact Module.Finite.iff_addGroup_fg.1
      (inferInstanceAs (Module.Finite ℤ (Additive (Langlands.Global.Arithmetic.SUnitIndex.sUnits K T))))
  let f := kummerSUnitsHom (Ω := Ω) S ℓ hnS
  have htors : ∀ y : cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 1,
      ℓ • y = 0 :=
    nsmul_cohomology_eq_zero _ (nsmul_rootsOfUnityModule_eq_zero ℓ) 1
  have hran : Finite f.range := by
    have : AddGroup.FG f.range := AddGroup.fg_of_surjective f.rangeRestrict_surjective
    exact AddCommGroup.finite_of_fg_isAddTorsion _ fun y =>
      isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ, hℓ.pos, Subtype.ext (htors y.1)⟩
  refine (AddMonoidHom.finite_iff_finite_ker_range (kummerPicHom (Ω := Ω) S ℓ)).2
    ⟨?_, inferInstance⟩
  refine Finite.of_injective (fun y : (kummerPicHom (Ω := Ω) S ℓ).ker =>
    (⟨y.1, AddMonoidHom.mem_range.2 ((kummerPicHom_eq_zero_iff S ℓ hnS y.1).1 y.2)⟩ : f.range)) ?_
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

include hℓ hS in
/-- **`H²(G_S, μ_ℓ)` is finite** for finite `S` containing the places above `ℓ`. -/
theorem finite_cohomology_two_rootsOfUnityModule [Finite S] :
    Finite (cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 2) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hnS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  have hX := sUnitsKummerSequence_shortExact S ℓ hnS (Ω := Ω)
  have h1 : Finite (cohomology (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) ℓ).X₃ 1) :=
    Finite.of_injective _ (cohomologyOneSUnitsToSPicard_injective (Ω := Ω) S)
  have htors : ∀ y : cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 2,
      ℓ • y = 0 :=
    nsmul_cohomology_eq_zero _ (nsmul_rootsOfUnityModule_eq_zero ℓ) 2
  let P := (nsmulAddMonoidHom ℓ : cohomology (maximalSUnitsModule K Ω S) 2 →+
    cohomology (maximalSUnitsModule K Ω S) 2).ker
  have hP : Finite P := by
    have := finite_nsmul_eq_zero_cohomology_two_maximalSUnits (Ω := Ω) S hℓ hS
    exact Finite.of_injective (fun y : P =>
      (⟨y.1, AddMonoidHom.mem_ker.1 y.2⟩ : {y : cohomology (maximalSUnitsModule K Ω S) 2 // ℓ • y = 0}))
      fun a b h => Subtype.ext (congrArg Subtype.val h)
  let g : cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 2 →+ P :=
    (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) ℓ) 2).hom.toAddMonoidHom.codRestrict
      P fun y => by
        rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
        change ℓ • (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) ℓ) 2).hom y = 0
        rw [← map_nsmul, htors, map_zero]
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (cohomology_exact₁ hX 1 2 rfl)
  exact Local.finite_of_exact (δ hX 1 2 rfl).hom.toAddMonoidHom g fun y =>
    Subtype.ext_iff.trans (hex y)

end Arithmetic

section Open

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- `Hʳ(U, μ_ℓ)` is finite for `r ≤ 2` and every open subgroup `U` of `G_S`: `U` is `G_{S_L}` of a
finite extension `L ⊆ K_S` of `K`. -/
theorem finite_cohomology_res_rootsOfUnityModule [Finite S]
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) (r : ℕ) (hr : r ≤ 2) :
    Finite (cohomology (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) r) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have : Finite (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))))
    exact finite_cohomology_zero _
  obtain ⟨L, _, hL, rfl⟩ := GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq U
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((ℓ : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have : Finite (finitePlacesAbove L S) := (finite_finitePlacesAbove (Set.toFinite S)).to_subtype
  have hμ : Finite (cohomology (rootsOfUnityModule L
      (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) ℓ) r) := by
    rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
    · exact finite_cohomology_one_rootsOfUnityModule (Ω := Ω) (finitePlacesAbove L S) hℓ hSL
    · exact finite_cohomology_two_rootsOfUnityModule (Ω := Ω) (finitePlacesAbove L S) hℓ hSL
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  let ψ := MulEquiv.restrictRootsOfUnity (maximalUnramifiedOutsideEquiv hL).toRingEquiv.toMulEquiv ℓ
  let f : Rep.res e.symm.toMulEquiv.toMonoidHom
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) ⟶
      rootsOfUnityModule L (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) ℓ :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm (MulEquiv.toAdditive ψ).toAddMonoidHom,
      fun τ => LinearMap.ext fun x => by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        apply Subtype.ext
        exact (GaloisGroupUnramifiedOutside.coe_fixingOpenSubgroupEquiv_symm_apply hL τ _)⟩
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous f
    (MulEquiv.toAdditive ψ).bijective r
  have hinj : Function.Injective
      (map ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩ f r).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact Finite.of_injective _ hinj

variable {S} in
/-- Finiteness in degrees `≤ 2` for finite `n`-torsion modules with trivial action of an open
subgroup `V` of `G_S` that fixes the `n`-th roots of unity: by induction on the order, through a
submodule `ℤ/ℓ ≅ μ_ℓ`. -/
theorem finite_cohomology_of_trivial_maximal [Finite S] {n : ℕ} (hn : n ≠ 0)
    (hSn : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (V : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (hV : ∀ σ ∈ V, ∀ ζ : maximalUnramifiedOutside K Ω S, ζ ^ n = 1 → σ ζ = ζ) :
    ∀ (A : Rep.{u} (ULift.{u} ℤ) (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
      [IsSmoothRep A] [Finite A],
      (∀ (g : (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) (a : A), A.ρ g a = a) →
      (∀ a : A, n • a = 0) → ∀ r ≤ 2, Finite (cohomology A r) := by
  intro A
  induction hN : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  intro _ _ htriv hA r hr
  by_cases hsub : Subsingleton A
  · have := subsingleton_cohomology_of_subsingleton A r
    exact Finite.of_subsingleton
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
    rw [not_subsingleton_iff_nontrivial] at hsub
    exact exists_ne 0
  have hdn : addOrderOf a ∣ n := addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  have hd0 : addOrderOf a ≠ 0 := fun h0 => hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hdn))
  have hd1 : addOrderOf a ≠ 1 := fun h1 =>
    ha (by rw [← one_nsmul a, ← h1, addOrderOf_nsmul_eq_zero])
  set d := addOrderOf a with hd
  set p := d.minFac
  have hp : p.Prime := Nat.minFac_prime hd1
  have : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ d := Nat.minFac_dvd d
  set b := (d / p) • a
  have hpb : p • b = 0 := by
    rw [smul_smul, Nat.mul_div_cancel' hpd, hd, addOrderOf_nsmul_eq_zero]
  have hb : b ≠ 0 := by
    intro hb0
    have h1 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd) hp.pos)
      (addOrderOf_dvd_of_nsmul_eq_zero hb0)
    exact absurd h1 (not_le.2 (Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.one_lt))
  have hpn : p ∣ n := hpd.trans hdn
  have hSp : ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hSn v (by
      obtain ⟨c, hc⟩ := hpn
      rw [hc, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_maximal (Ω := Ω) S hp hSp
  let i : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A b, by simp [hpb]⟩
  have hi : Function.Injective i := zmod_lift_zmultiplesHom_injective hb hpb
  have hfix : ∀ (σ : (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
      (x : Additive (rootsOfUnity p (maximalUnramifiedOutside K Ω S))),
      (Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) p)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine hV σ σ.2 _ ?_
    obtain ⟨c, hc⟩ := hpn
    have hxp : (((Additive.toMul x : rootsOfUnity p (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p _).1 (Additive.toMul x).2, Units.val_one]
    rw [hc, pow_mul, hxp, one_pow]
  let ι : Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) p) ⟶ A :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom (Rep.res (V : Subgroup
      (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) p)) A).symm
        (i.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change i (e.symm ((Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
          (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) p)).ρ σ x)) =
            A.ρ σ (i (e.symm x))
        rw [hfix, htriv]⟩
  have hι : Function.Injective ι.hom := fun x y h => e.symm.injective (hi h)
  let X := cokerShortComplex ι
  have hX : X.ShortExact := cokerShortComplex_shortExact ι hι
  have : IsSmoothRep X.X₁ := inferInstanceAs
    (IsSmoothRep (Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) p)))
  have : IsSmoothRep X.X₂ := (inferInstance : IsSmoothRep A)
  have : Finite X.X₂ := (inferInstance : Finite A)
  have : IsSmoothRep X.X₃ := isSmoothRep_quotient _ _ _
  have hsurj : Function.Surjective X.g.hom := Submodule.mkQ_surjective _
  have : Finite X.X₃ := Finite.of_surjective _ hsurj
  have htrivQ : ∀ (g : (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) (q : X.X₃),
      X.X₃.ρ g q = q := by
    intro g q
    obtain ⟨a', rfl⟩ := hsurj q
    exact (Rep.hom_comm_apply X.g g a').symm.trans (congrArg X.g.hom (htriv g a'))
  have hQ : ∀ q : X.X₃, n • q = 0 := by
    intro q
    obtain ⟨a', rfl⟩ := hsurj q
    rw [← map_nsmul]
    exact (congrArg X.g.hom (hA a')).trans (map_zero _)
  have hlt : Nat.card X.X₃ < N := by
    rw [← hN]
    have := Fintype.ofFinite X.X₃
    have := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective _ hsurj fun hinj => hb ?_
    have h0 : X.g.hom (ι.hom (e 1)) = 0 :=
      congrArg (fun φ => φ.hom (e 1)) X.zero
    have h1 : ι.hom (e 1) = b := by
      change i (e.symm (e 1)) = b
      rw [AddEquiv.symm_apply_apply,
        show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from Int.cast_one.symm, ZMod.lift_coe]
      exact one_zsmul b
    rw [← h1]
    exact hinj (h0.trans (map_zero _).symm)
  have h3 : Finite (cohomology X.X₃ r) := ih _ hlt X.X₃ rfl htrivQ hQ r hr
  have h1 : Finite (cohomology X.X₁ r) :=
    finite_cohomology_res_rootsOfUnityModule (Ω := Ω) S hp hSp V r hr
  exact Local.finite_of_exact (coeffMap X.f r).hom.toAddMonoidHom
    (coeffMap X.g r).hom.toAddMonoidHom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (cohomology_exact₂ hX r))

variable {S} in
/-- **Finiteness in degrees `≤ 2`, open subgroups.** For finite `S`, `n ≠ 0` with the places above
`n` in `S`, an open subgroup `U` of `G_S` and a finite smooth module `M` of `U` killed by `n`,
`Hʳ(U, M)` is finite for `r ≤ 2`. -/
theorem finite_cohomology_res_of_le_two [Finite S] {n : ℕ} (hn : n ≠ 0)
    (hSn : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) [IsSmoothRep M]
    [Finite M] (hM : ∀ m : M, n • m = 0) (r : ℕ) (hr : r ≤ 2) : Finite (cohomology M r) := by
  have : NeZero n := ⟨hn⟩
  exact finite_cohomology_of_forall_trivial n 2
    (rootsOfUnityFixing K (maximalUnramifiedOutside K Ω S) n)
    (fun V hV A _ _ htriv hA r hr => finite_cohomology_of_trivial_maximal hn hSn V
      (fun σ hσ ζ hζ => apply_eq_of_mem_rootsOfUnityFixing (hV hσ) hζ) A htriv hA r hr)
    U M hM r hr

variable {S} in
/-- **Finiteness in degrees `≤ 2`.** For finite `S` and a finite smooth module `M` of `G_S` such that
the places above `#M` lie in `S`, `Hʳ(G_S, M)` is finite for `r ≤ 2`. -/
theorem finite_cohomology_of_le_two [Finite S]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hSM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (r : ℕ)
    (hr : r ≤ 2) : Finite (cohomology M r) := by
  have hn : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have : Finite (Rep.res ((⊤ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) := inferInstanceAs (Finite M)
  have := finite_cohomology_res_of_le_two hn hSM ⊤
    (Rep.res ((⊤ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) (fun _ => card_nsmul_eq_zero') r hr
  exact Finite.of_injective _ (bijective_res_top M r).1

variable {S} in
/-- **Finiteness in all degrees, `#M` odd or `K` totally complex.** -/
theorem finite_cohomology_of_odd_or_isTotallyComplex [Finite S]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hSM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd (Nat.card M) ∨ IsTotallyComplex K) (r : ℕ) : Finite (cohomology M r) := by
  rcases le_or_gt r 2 with hr | hr
  · exact finite_cohomology_of_le_two M hSM r hr
  · have := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S
      Nat.card_pos.ne' hSM hK M (fun _ => card_nsmul_eq_zero') hr
    exact Finite.of_subsingleton

end Open

end

end Langlands.GaloisCohomology
