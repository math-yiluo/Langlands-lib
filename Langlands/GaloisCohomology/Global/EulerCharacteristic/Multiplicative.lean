import Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio
import Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof
import Langlands.Cohomology.Profinite.Cup.Corestriction

/-!
# Multiplicativity of the Euler characteristic ratio of `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K` and
`ι : PlaceEmbeddings K Ω`. For a short exact sequence `0 → A → B → C → 0` of finite smooth
`G_S`-modules, the long exact cohomology sequence, cut after `H²`, gives

`χ(A) · χ(C) = χ(B) · #ker(H³(G_S, A) → H³(G_S, B))`
(`eulerCharacteristic_mul_eq_mul_card_ker`),

and at a real place `w`, where `χ(K_w, ·) = #H⁰(K_w, ·)` for finite modules,

`#H⁰(K_w, A) · #H⁰(K_w, C) = #H⁰(K_w, B) · #ker(H³(K_w, A) → H³(K_w, B))`.

When the localization `H³(G_S, ·) → ∏_{w real} H³(K_w, ·)` is bijective for `A` and injective for
`B`, the two kernels correspond, and the ratio `globalEulerRatio` of
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio` is multiplicative
(`globalEulerRatio_shortExact_of_bijective`). Tate's theorem on the real places in degree three
(`realLocalizationDegreeThreeStatement` of `Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`)
provides this for every finite module with the places above its order in `S`
(`globalEulerRatio_shortExact`).

Consequences proved here:

* `globalEulerRatio_eq_one_of_primary`: if the ratio is `1` for every finite module killed by a prime
  `ℓ` (with the places above `ℓ` in `S`), it is `1` for every finite module killed by a power of `ℓ`
  (dévissage `0 → M[ℓ] → M → ℓM → 0`).
* `IsMultiplicativeOn` (functions of finite modules multiplicative on short exact sequences whose
  middle term has order in a class `P`) and `IsMultiplicativeOn.coind_res_eq_pow`: for an open normal
  subgroup `H` with cyclic quotient of order `p^a` and a module killed by `p`, the value on
  `Ind_H^G Res_H M` is the `p^a`-th power of the value on `M`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u w

noncomputable section

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃]

/-- The long exact sequence cut after `H²`: `χ(A) · χ(C) = χ(B) · #im(H²(C) → H³(A))`. -/
theorem eulerCharacteristic_mul_eq_mul_card_range_δ (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)] :
    eulerCharacteristic S.X₁ * eulerCharacteristic S.X₃ =
      eulerCharacteristic S.X₂ * Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (map (.id G) S.f i).hom) =
      Nat.card (LinearMap.ker (map (.id G) S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)
  have e30 : Nat.card (LinearMap.range (map (.id G) S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (map (.id G) S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (map (.id G) S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (map (.id G) S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (map (.id G) S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (map (.id G) S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (map (.id G) S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (coeffCochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (map (.id G) S.f 1), ← e10] at hA1
  rw [hk (map (.id G) S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerCharacteristic_eq, eulerCharacteristic_eq, eulerCharacteristic_eq,
    hk (map (.id G) S.f 0), hk (map (.id G) S.f 1), hk (map (.id G) S.f 2),
    hk (map (.id G) S.g 0), hk (map (.id G) S.g 1), hk (map (.id G) S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

/-- The long exact sequence cut after `H²`: `χ(A) · χ(C) = χ(B) · #ker(H³(A) → H³(B))`. -/
theorem eulerCharacteristic_mul_eq_mul_card_ker (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)] :
    eulerCharacteristic S.X₁ * eulerCharacteristic S.X₃ =
      eulerCharacteristic S.X₂ * Nat.card (LinearMap.ker (map (.id G) S.f 3).hom) := by
  rw [eulerCharacteristic_mul_eq_mul_card_range_δ hS,
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 2 3 rfl)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] in
/-- In a short exact sequence of finite modules, `#B = #A · #C`. -/
theorem card_X₂_eq_of_shortExact (hS : S.ShortExact) [Finite S.X₂] :
    Nat.card S.X₂ = Nat.card S.X₁ * Nat.card S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := (hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap, LinearMap.range_eq_top.2 hsurj]
  congr 1
  · have hex' : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap := hex
    rw [← hex']
    exact (Nat.card_congr (LinearEquiv.ofInjective S.f.hom.toLinearMap hinj).toEquiv).symm
  · exact Nat.card_congr (Submodule.topEquiv).toEquiv

end Generic

section Kernels

variable {M N ι : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι] {Mv Nv : ι → Type*}
  [∀ v, AddCommGroup (Mv v)] [∀ v, AddCommGroup (Nv v)]

/-- If `rA : M → ∏ Mv` is bijective, `rB : N → ∏ Nv` injective and they intertwine `f` with the
`fv`, then `#ker f = ∏ #ker fv`. -/
theorem card_ker_eq_prod_card_ker (f : M →+ N) (fv : ∀ v, Mv v →+ Nv v)
    (rA : M → ∀ v, Mv v) (rB : N → ∀ v, Nv v)
    (hcomm : ∀ x v, rB (f x) v = fv v (rA x v)) (hA : Function.Bijective rA)
    (hB : Function.Injective rB) (hrB0 : ∀ v, rB 0 v = 0) :
    Nat.card f.ker = ∏ v, Nat.card (fv v).ker := by
  let ψ : f.ker → ∀ v, (fv v).ker := fun x v =>
    ⟨rA x.1 v, by
      rw [AddMonoidHom.mem_ker, ← hcomm, AddMonoidHom.mem_ker.1 x.2, hrB0]⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y hxy => Subtype.ext (hA.1 (funext fun v => ?_)), fun y => ?_⟩
    · exact congrArg Subtype.val (congrFun hxy v)
    · obtain ⟨x, hx⟩ := hA.2 (fun v => (y v).1)
      have hfx : f x = 0 := hB (by
        funext v
        rw [hcomm, hx, hrB0]
        exact (y v).2)
      exact ⟨⟨x, hfx⟩, funext fun v => Subtype.ext (congrFun hx v)⟩
  rw [Nat.card_congr (Equiv.ofBijective ψ hψ), Nat.card_pi]

end Kernels

section Arithmetic

theorem ratio_mul_eq {a b c nA nB nC PA PB PC κ : ℚ} (r : ℕ) (hPA : PA ≠ 0) (hPB : PB ≠ 0)
    (hPC : PC ≠ 0) (hn : nB = nA * nC) (hχ : a * c = b * κ) (hP : PA * PC = PB * κ) :
    b * nB ^ r / PB = a * nA ^ r / PA * (c * nC ^ r / PC) := by
  rw [div_mul_div_comm, div_eq_div_iff hPB (mul_ne_zero hPA hPC), hP, hn, mul_pow]
  linear_combination (-(nA ^ r * nC ^ r * PB)) * hχ

end Arithmetic

section Ratio

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)

variable {T : ShortComplex (Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))}
  [IsSmoothRep T.X₁] [IsSmoothRep T.X₂] [IsSmoothRep T.X₃]

/-- At a real place, `#H⁰(K_w, A) · #H⁰(K_w, C) = #H⁰(K_w, B) · #ker(H³(K_w, A) → H³(K_w, B))`. -/
theorem card_realLocal_mul_eq (hT : T.ShortExact) [Finite T.X₁] [Finite T.X₂] [Finite T.X₃]
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Nat.card (cohomology (realLocalModule ι T.X₁ w.1) 0) : ℚ) *
        Nat.card (cohomology (realLocalModule ι T.X₃ w.1) 0) =
      Nat.card (cohomology (realLocalModule ι T.X₂ w.1) 0) * Nat.card (LinearMap.ker
        (coeffMap ((Rep.resFunctor (k := ULift.{u} ℤ) (realLocalizationHom ι S w.1 :
          Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
            GaloisGroupUnramifiedOutside K Ω S)).map T.f) 3).hom) := by
  let F := Rep.resFunctor (k := ULift.{u} ℤ) (realLocalizationHom ι S w.1 :
    Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →* GaloisGroupUnramifiedOutside K Ω S)
  have hTw : (T.map F).ShortExact := (Rep.shortExact_res _).2 hT
  have : IsSmoothRep (T.map F).X₁ := inferInstanceAs (IsSmoothRep (realLocalModule ι T.X₁ w.1))
  have : IsSmoothRep (T.map F).X₂ := inferInstanceAs (IsSmoothRep (realLocalModule ι T.X₂ w.1))
  have : IsSmoothRep (T.map F).X₃ := inferInstanceAs (IsSmoothRep (realLocalModule ι T.X₃ w.1))
  have : Finite (cohomology (T.map F).X₁ 1) :=
    finite_cohomology_of_isReal w.1 w.2 (realLocalModule ι T.X₁ w.1) 1 (by norm_num)
  have : Finite (cohomology (T.map F).X₂ 1) :=
    finite_cohomology_of_isReal w.1 w.2 (realLocalModule ι T.X₂ w.1) 1 (by norm_num)
  have : Finite (cohomology (T.map F).X₃ 1) :=
    finite_cohomology_of_isReal w.1 w.2 (realLocalModule ι T.X₃ w.1) 1 (by norm_num)
  have h := eulerCharacteristic_mul_eq_mul_card_ker hTw
  have e1 : eulerCharacteristic (T.map F).X₁ =
      (Nat.card (cohomology (realLocalModule ι T.X₁ w.1) 0) : ℚ) :=
    eulerCharacteristic_realLocalModule ι T.X₁ w
  have e2 : eulerCharacteristic (T.map F).X₂ =
      (Nat.card (cohomology (realLocalModule ι T.X₂ w.1) 0) : ℚ) :=
    eulerCharacteristic_realLocalModule ι T.X₂ w
  have e3 : eulerCharacteristic (T.map F).X₃ =
      (Nat.card (cohomology (realLocalModule ι T.X₃ w.1) 0) : ℚ) :=
    eulerCharacteristic_realLocalModule ι T.X₃ w
  exact ((congrArg₂ (· * ·) e1 e3).symm.trans h).trans (congrArg (· * _) e2)

variable [Finite S]

/-- **Multiplicativity of the ratio**, assuming that the localization to the real places in degree
three is bijective for `A` and injective for `B`. -/
theorem globalEulerRatio_shortExact_of_bijective (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₂ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hA : Function.Bijective fun (x : cohomology T.X₁ 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι T.X₁ w.1 3 x)
    (hB : Function.Injective fun (x : cohomology T.X₂ 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι T.X₂ w.1 3 x) :
    globalEulerRatio ι T.X₂ = globalEulerRatio ι T.X₁ * globalEulerRatio ι T.X₃ := by
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have hsurj : Function.Surjective T.g.hom := (Rep.epi_iff_surjective _).1 hT.epi_g
  have : Finite T.X₁ := Finite.of_injective _ hinj
  have : Finite T.X₃ := Finite.of_surjective _ hsurj
  have hcard := card_X₂_eq_of_shortExact hT
  have hn1 : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₁ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => hn v (by rw [hcard, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  have hn3 : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₃ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => hn v (by rw [hcard, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hv)
  have : Finite (cohomology T.X₁ 1) := finite_cohomology_of_le_two T.X₁ hn1 1 (by norm_num)
  have : Finite (cohomology T.X₂ 1) := finite_cohomology_of_le_two T.X₂ hn 1 (by norm_num)
  have : Finite (cohomology T.X₃ 1) := finite_cohomology_of_le_two T.X₃ hn3 1 (by norm_num)
  have hglob := eulerCharacteristic_mul_eq_mul_card_ker hT
  have hker := card_ker_eq_prod_card_ker (map (.id _) T.f 3).hom.toAddMonoidHom
    (fun w : {w : InfinitePlace K // w.IsReal} =>
      (coeffMap ((Rep.resFunctor (k := ULift.{u} ℤ) (realLocalizationHom ι S w.1 :
        Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
          GaloisGroupUnramifiedOutside K Ω S)).map T.f) 3).hom.toAddMonoidHom)
    _ _ (fun x w => realLocalization_coeffMap ι T.f w.1 3 x) hA hB
    (fun w => map_zero _)
  have hloc := fun w => card_realLocal_mul_eq ι hT w
  have hPA := prod_card_cohomology_zero_realLocalModule_ne_zero ι T.X₁
  have hPB := prod_card_cohomology_zero_realLocalModule_ne_zero ι T.X₂
  have hPC := prod_card_cohomology_zero_realLocalModule_ne_zero ι T.X₃
  have hprod : (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι T.X₁ w.1) 0) : ℚ)) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι T.X₃ w.1) 0) : ℚ) =
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι T.X₂ w.1) 0) : ℚ)) *
        (Nat.card (LinearMap.ker (map (.id _) T.f 3).hom) : ℚ) := by
    refine Finset.prod_mul_distrib.symm.trans
      ((Finset.prod_congr rfl (fun w _ => hloc w)).trans (Finset.prod_mul_distrib.trans ?_))
    exact congrArg (_ * ·) ((Nat.cast_prod _ _).symm.trans (congrArg Nat.cast hker.symm))
  exact ratio_mul_eq (Fintype.card (InfinitePlace K)) hPA hPB hPC (by exact_mod_cast hcard)
    hglob hprod

end Ratio

section RealDegreeThree

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
  {T : ShortComplex (Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))}
  [IsSmoothRep T.X₁] [IsSmoothRep T.X₂] [IsSmoothRep T.X₃]

/-- **Multiplicativity of the ratio** on a short exact sequence of finite smooth `G_S`-modules with the
places above the order of the middle term in `S`, by Tate's theorem on the real places in degree three
(`realLocalizationDegreeThreeStatement`). -/
theorem globalEulerRatio_shortExact (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₂ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    globalEulerRatio ι T.X₂ = globalEulerRatio ι T.X₁ * globalEulerRatio ι T.X₃ := by
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have : Finite T.X₁ := Finite.of_injective _ hinj
  have hcard := card_X₂_eq_of_shortExact hT
  have hn1 : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₁ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => hn v (by rw [hcard, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  exact globalEulerRatio_shortExact_of_bijective ι hT hn
    (bijective_realLocalization ι S T.X₁ hn1 le_rfl)
    (bijective_realLocalization ι S T.X₂ hn le_rfl).1

end RealDegreeThree

section Primary

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

theorem exists_card_eq_pow_of_nsmul {ℓ : ℕ} (hℓ : ℓ.Prime) {X : Type*} [AddCommGroup X] [Finite X]
    {r : ℕ} (h : ∀ m : X, (ℓ ^ r) • m = 0) : ∃ n : ℕ, Nat.card X = ℓ ^ n := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hp : IsPGroup ℓ (Multiplicative X) := fun g => ⟨r, by
    change Multiplicative.toAdd (g ^ (ℓ ^ r)) = Multiplicative.toAdd 1
    rw [toAdd_pow]; exact h _⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [← hn]; rfl⟩

omit [NumberField K] [Finite S] in
/-- If the places above a prime `ℓ` lie in `S`, they contain the places above the order of a finite
group killed by a power of `ℓ`. -/
theorem mem_of_natCard_mem_of_nsmul {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {X : Type*} [AddCommGroup X] [Finite X] {r : ℕ} (h : ∀ m : X, (ℓ ^ r) • m = 0) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card X : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
  obtain ⟨n, hn⟩ := exists_card_eq_pow_of_nsmul hℓ h
  intro v hv
  rw [hn, Nat.cast_pow] at hv
  exact hS v (v.isPrime.mem_of_pow_mem n hv)

/-- **Dévissage to modules killed by `ℓ`.** If the ratio is `1` for every finite module killed by
the prime `ℓ`, it is `1` for every finite module killed by a power of `ℓ`. -/
theorem globalEulerRatio_eq_one_of_primary {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (h : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, ℓ • m = 0) → globalEulerRatio ι M = 1)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) : globalEulerRatio ι M = 1 := by
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact globalEulerRatio_eq_one_of_subsingleton ι M
  | succ r ih =>
    let T : Module.End (ULift.{u} ℤ) M := (ℓ : Module.End (ULift.{u} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ M) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₁ := isSmoothRep_subrepresentation _ _ _
    have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₂ := isSmoothRep_subrepresentation _ _ _
    have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₃ := isSmoothRep_subrepresentation _ _ _
    have : Finite (rangeStepComplex T hT ⊤ hD).X₂ :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h =>
        Subtype.ext h
    have : Finite (rangeStepComplex T hT ⊤ hD).X₁ :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) =>
        (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (rangeStepComplex T hT ⊤ hD).X₃ :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) =>
        (x.1 : M)) fun _ _ h => Subtype.ext h
    have hl : ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ (r + 1)) • m = 0 :=
      fun m => Subtype.ext (hr m.1)
    have hmul := globalEulerRatio_shortExact ι hSE
      (mem_of_natCard_mem_of_nsmul hℓ hS hl)
    have h1 : globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₁ = 1 := by
      refine h _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3' : globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₃ = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : globalEulerRatio ι M = globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₂ :=
      (globalEulerRatio_eq_of_iso ι _ (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3', mul_one]

end Primary

section MultiplicativeOn

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] {R : Type w} [CommMonoid R]

/-- A function `χ` of smooth modules with values in a commutative monoid is multiplicative on the
finite modules whose order satisfies `P`: it is invariant under isomorphisms, and
`χ(B) = χ(A) χ(C)` for a short exact sequence `0 → A → B → C → 0` with `P(#B)`. -/
structure IsMultiplicativeOn [IsTopologicalGroup G] (P : ℕ → Prop)
    (χ : (A : Rep.{u} k G) → [IsSmoothRep A] → R) : Prop where
  /-- Invariance under isomorphisms. -/
  iso : ∀ {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [Finite A],
    P (Nat.card A) → (A ≅ B) → χ A = χ B
  /-- Multiplicativity on short exact sequences. -/
  shortExact : ∀ {T : ShortComplex (Rep.{u} k G)} [IsSmoothRep T.X₁] [IsSmoothRep T.X₂]
    [IsSmoothRep T.X₃] [Finite T.X₂], T.ShortExact → P (Nat.card T.X₂) →
    χ T.X₂ = χ T.X₁ * χ T.X₃

omit [CommMonoid R] in
theorem apply_subrepresentation_congr [IsTopologicalGroup G]
    (χ : (A : Rep.{u} k G) → [IsSmoothRep A] → R)
    {A : Rep.{u} k G} [IsSmoothRep A] {W W' : Submodule k A} (h : W = W')
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) (hW' : ∀ g, W' ≤ W'.comap (A.ρ g)) :
    χ (Rep.subrepresentation A W hW) = χ (Rep.subrepresentation A W' hW') := by
  subst h
  rfl

namespace IsMultiplicativeOn

variable [IsTopologicalGroup G] {P : ℕ → Prop} {χ : (A : Rep.{u} k G) → [IsSmoothRep A] → R}

theorem rangeStep (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    {A : Rep.{u} k G} [IsSmoothRep A] [Finite A] (T : Module.End k A)
    (hT : ∀ g : G, Commute T (A.ρ g)) (D : Submodule k A) (hD : ∀ g : G, D ≤ D.comap (A.ρ g))
    (hA : P (Nat.card A)) :
    χ (Rep.subrepresentation A D hD) =
      χ (Rep.subrepresentation A _ (inf_ker_le_comap T hT D hD)) *
        χ (Rep.subrepresentation A _ (map_le_comap T hT D hD)) := by
  have hdvd : Nat.card D ∣ Nat.card A :=
    AddSubgroup.card_addSubgroup_dvd_card D.toAddSubgroup
  have : Finite (rangeStepComplex T hT D hD).X₂ :=
    Finite.of_injective (fun x : Rep.subrepresentation A D hD => (x.1 : A)) fun _ _ h =>
      Subtype.ext h
  have : IsSmoothRep (rangeStepComplex T hT D hD).X₁ := isSmoothRep_subrepresentation _ _ _
  have : IsSmoothRep (rangeStepComplex T hT D hD).X₂ := isSmoothRep_subrepresentation _ _ _
  have : IsSmoothRep (rangeStepComplex T hT D hD).X₃ := isSmoothRep_subrepresentation _ _ _
  exact hχ.shortExact (rangeStepComplex_shortExact T hT D hD) (hPdvd _ _ hdvd hA)

variable [CompactSpace G]

/-- For an open normal subgroup `H` with cyclic quotient of order `p^a` and a finite module `M`
killed by `p`, `χ(Ind_H^G Res_H M) = χ(M)^{p^a}`: the induced module has a filtration of length `p^a`
by the powers of `s - 1` (`s` a generator of `G/H`) with all quotients isomorphic to `M`. -/
theorem coind_res_eq_pow (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    (hPmul : ∀ m n, P m → P n → P (m * n)) (H : OpenSubgroup G)
    [hN : (H : Subgroup G).Normal] [IsCyclic (G ⧸ (H : Subgroup G))] {p a : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card (G ⧸ (H : Subgroup G)) = p ^ a) (M : Rep.{u} k G) [IsSmoothRep M]
    [Finite M] (hM : P (Nat.card M)) (hpM : ∀ m : M, p • m = 0)
    [IsSmoothRep (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M))] :
    χ (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M)) =
      χ M ^ (p ^ a) := by
  have hQ : Finite (G ⧸ (H : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ (H : Subgroup G))
  have hmk : (QuotientGroup.mk (Quotient.out q) : G ⧸ (H : Subgroup G)) = q :=
    QuotientGroup.out_eq' q
  set s : G := Quotient.out q
  have hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G) := by
    intro g
    have hc : (QuotientGroup.mk (g * s) : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s * g) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact (IsCyclic.commGroup (α := G ⧸ (H : Subgroup G))).mul_comm _ _
    have h2 := hN.conj_mem _ (QuotientGroup.eq.1 hc) (g * s)
    have e : s * g * s⁻¹ * g⁻¹ = g * s * ((g * s)⁻¹ * (s * g)) * (g * s)⁻¹ := by group
    rw [e]
    exact h2
  have hsN : s ^ (p ^ a) ∈ (H : Subgroup G) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← hcard]
    exact pow_card_eq_one'
  have hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G) := by
    intro x
    obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hq (QuotientGroup.mk x))
    refine ⟨i, ?_⟩
    have h1 : (QuotientGroup.mk x : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s ^ i) := by
      rw [QuotientGroup.mk_pow, hmk]
      exact hi.symm
    have h3 := hN.conj_mem _ (inv_mem (QuotientGroup.eq.1 h1)) x
    have e : x * (s ^ i)⁻¹ = x * (x⁻¹ * s ^ i)⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3
  set T : Module.End k (coindRes H M) := coindT (H := H) (M := M) s with hT_def
  have hT : ∀ g : G, Commute T ((coindRes H M).ρ g) := commute_coindShift_sub_one hs
  have hCp : ∀ f : coindRes H M, p • f = 0 := fun f =>
    Subtype.ext (funext fun x => hpM (f.1 x))
  have hTN : T ^ (p ^ a) = 0 :=
    sub_one_pow_prime_pow_eq_zero hCp (coindShift (H := H) (M := M) s) a
      (coindShift_pow_eq_one hsN)
  let D : ℕ → Submodule k (coindRes H M) := fun j => LinearMap.range (T ^ j)
  have hD : ∀ j (g : G), D j ≤ (D j).comap ((coindRes H M).ρ g) := by
    rintro j g _ ⟨y, rfl⟩
    exact ⟨(coindRes H M).ρ g y, by
      rw [← Module.End.mul_apply, ((hT g).pow_left j).eq, Module.End.mul_apply]⟩
  have hDsucc : ∀ j, (D j).map T = D (j + 1) := fun j => by
    simp only [D]
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  have hD0 : D 0 = ⊤ := by
    change LinearMap.range (T ^ 0) = ⊤
    rw [pow_zero]
    exact LinearMap.range_eq_top.2 fun x => ⟨x, rfl⟩
  have hDN : D (p ^ a) = ⊥ := by simp [D, hTN]
  have hK : ∀ g : G, LinearMap.ker T ≤ (LinearMap.ker T).comap ((coindRes H M).ρ g) :=
    ker_le_comap T hT
  have : Finite (Rep.res (H : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have : Finite (coindRes H M) := finite_coind H (Rep.res (H : Subgroup G).subtype M)
  have : IsSmoothRep (coindRes H M) := isSmoothRep_coind_res H M
  set c := Nat.card (LinearMap.ker T) with hc
  have hcM : c = Nat.card M := Nat.card_congr (kerShiftEquiv (H := H) (M := M) hgen).toEquiv.symm
  have hstep : ∀ j, Nat.card (D j) =
      Nat.card ↥(D j ⊓ LinearMap.ker T) * Nat.card (D (j + 1)) := fun j => by
    rw [card_rangeStep T (D j), hDsucc]
  have hle : ∀ j, Nat.card ↥(D j ⊓ LinearMap.ker T) ≤ c := fun j =>
    Nat.card_le_card_of_injective _
      (Submodule.inclusion_injective (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T))
  have hcpos : 0 < c := Nat.card_pos
  have hup : ∀ m j, j + m = p ^ a → Nat.card (D j) ≤ c ^ m := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      rw [hDN]
      simp
    | succ m ih =>
      intro j hj
      rw [hstep j, pow_succ']
      exact Nat.mul_le_mul (hle j) (ih (j + 1) (by omega))
  have hlow : c ^ (p ^ a) ≤ Nat.card (D 0) := by
    rw [hD0, Nat.card_congr (Submodule.topEquiv).toEquiv, hcM, ← hcard]
    exact card_pow_le_card_coindRes
  have hexact : ∀ j ≤ p ^ a, Nat.card (D j) = c ^ (p ^ a - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact le_antisymm (hup _ 0 (by simp)) (by simpa using hlow)
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [hstep j] at h1
      have h2 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at h1
      exact (eq_and_eq_of_mul_eq_mul_of_le (hle j) (hup _ (j + 1) (by omega)) h1 hcpos
        (pow_pos hcpos _)).2
  have hfull : ∀ j < p ^ a, D j ⊓ LinearMap.ker T = LinearMap.ker T := by
    intro j hj
    have h1 := hexact j hj.le
    rw [hstep j, hexact (j + 1) hj] at h1
    have h3 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3] at h1
    have hcard' : Nat.card ↥(D j ⊓ LinearMap.ker T) = c :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) h1
    apply Submodule.toAddSubgroup_injective
    refine AddSubgroup.eq_of_le_of_card_ge
      ((Submodule.toAddSubgroup_le _ _).2
        (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T)) ?_
    change Nat.card (LinearMap.ker T) ≤ Nat.card ↥(D j ⊓ LinearMap.ker T)
    rw [hcard']
  have hpa : 0 < p ^ a := pow_pos hp.out.pos a
  have hlast : D (p ^ a - 1) = LinearMap.ker T := by
    refine le_antisymm ?_ ((hfull _ (by omega)).symm.le.trans inf_le_left)
    intro x hx
    have hx' : T x ∈ D (p ^ a - 1 + 1) := hDsucc (p ^ a - 1) ▸ Submodule.mem_map_of_mem hx
    rw [show p ^ a - 1 + 1 = p ^ a by omega, hDN] at hx'
    exact LinearMap.mem_ker.2 ((Submodule.mem_bot k).1 hx')
  have hP : P (Nat.card (coindRes H M)) := by
    have hpow : ∀ n, P (Nat.card M ^ n) := fun n => by
      induction n with
      | zero => exact hPdvd 1 _ (one_dvd _) hM
      | succ n ih =>
        rw [pow_succ]
        exact hPmul _ _ ih hM
    exact hPdvd _ _ (card_coind_dvd H (Rep.res (H : Subgroup G).subtype M)) (hpow _)
  have : ∀ j, IsSmoothRep (Rep.subrepresentation (coindRes H M) (D j) (hD j)) := fun j =>
    isSmoothRep_subrepresentation _ _ _
  have : IsSmoothRep (Rep.subrepresentation (coindRes H M) (LinearMap.ker T) hK) :=
    isSmoothRep_subrepresentation _ _ _
  have hchain : ∀ j ≤ p ^ a - 1, χ (Rep.subrepresentation _ (D 0) (hD 0)) =
      χ (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ j *
        χ (Rep.subrepresentation _ (D j) (hD j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      rw [ih (by omega), hχ.rangeStep hPdvd T hT (D j) (hD j) hP,
        apply_subrepresentation_congr χ (hfull j (by omega)) _ hK,
        apply_subrepresentation_congr χ (hDsucc j) _ (hD (j + 1)), pow_succ, mul_assoc]
  have : IsSmoothRep (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
    isSmoothRep_subrepresentation (coindRes H M) ⊤ (fun _ => le_top)
  have htop : χ (coindRes H M) =
      χ (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
    hχ.iso hP (subrepresentationTopIso (coindRes H M) (fun _ => le_top)).symm
  calc χ (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M))
      = χ (coindRes H M) := rfl
    _ = χ (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) := htop
    _ = χ (Rep.subrepresentation _ (D 0) (hD 0)) :=
        apply_subrepresentation_congr χ hD0.symm _ _
    _ = χ (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ (p ^ a) := by
        rw [hchain (p ^ a - 1) le_rfl, apply_subrepresentation_congr χ hlast _ hK, ← pow_succ,
          show p ^ a - 1 + 1 = p ^ a by omega]
    _ = χ M ^ (p ^ a) := by
        rw [hχ.iso hM (kerShiftIso (H := H) (M := M) hs hgen)]

end IsMultiplicativeOn

end MultiplicativeOn

end

end Langlands.GaloisCohomology
