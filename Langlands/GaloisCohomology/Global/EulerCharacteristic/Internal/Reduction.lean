import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Cyclic

/-!
# Reduction of the Euler characteristic formula to extensions of degree prime to `ℓ`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places containing the
places above a prime `ℓ`, and `G_S` the Galois group of `K_S ⊆ Ω`. For an open subgroup
`W = G_S(L')` let `χ_W(X) = globalEulerRatio ι (Ind_W^{G_S} X)` for finite smooth `W`-modules `X`.

* `χ_W` is multiplicative on `ℓ`-primary modules (`isMultiplicativeOn_ratio_coind`), so for an open
  normal subgroup `V ⊆ W` with `W/V` cyclic of order `ℓ^a` and `M` killed by `ℓ`,
  `ratio(Ind_V M) = ratio(Ind_W M)^{ℓ^a}` (`globalEulerRatio_coind_stage_pow`), by
  `IsMultiplicativeOn.coind_res_eq_pow` and transitivity of induction (`nonempty_coind_coind_iso`).
* A cyclic quotient `W/U` splits as an `ℓ`-part `W/V` and a part `V/U` of order prime to `ℓ`
  (`exists_coprime_part`).
* Hence, with Shapiro's lemma (`globalEulerRatio_coind`), the formula for `Ind_W M`, `W/U` cyclic,
  follows from the formula over the fixed field `K''` of `V` for `M` viewed as a `G_S(K'')`-module, where
  now `[L : K'']` is prime to `ℓ` (`globalEulerRatio_coind_eq_one`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Stages

variable {k G : Type u} [CommRing k] [Group G]

/-- Induction in stages: `Ind_W^G Ind_{U}^W Res^W_U Res^G_W A ≅ Ind_U^G Res^G_U A` for `U ≤ W`. -/
def coindStagesEquiv (U W : Subgroup G) (hUW : U ≤ W) (A : Rep.{u} k G) :
    (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A)))).ρ.Equiv
      (Rep.coind U.subtype (Rep.res U.subtype A)).ρ where
  toFun F := ⟨fun g => (F.1 g).1 1, by
    intro u g
    have h3 : (F.1 (u.1 * g)).1 1 = (F.1 g).1 (1 * ⟨u.1, hUW u.2⟩) :=
      congrArg (fun x => x.1 (1 : W)) (F.2 ⟨u.1, hUW u.2⟩ g)
    have h2 := (F.1 g).2 ⟨⟨u.1, hUW u.2⟩, by simp [Subgroup.mem_subgroupOf]⟩ 1
    rw [one_mul] at h3
    rw [mul_one] at h2
    exact h3.trans h2⟩
  map_add' F F' := Subtype.ext (funext fun g => rfl)
  map_smul' c F := Subtype.ext (funext fun g => rfl)
  invFun f := ⟨fun g => ⟨fun w => f.1 (w.1 * g), by
      intro u' w
      have := f.2 ⟨u'.1.1, u'.2⟩ (w.1 * g)
      simpa [mul_assoc] using this⟩, by
    intro w g
    apply Subtype.ext
    funext x
    change f.1 (x.1 * (w.1 * g)) = f.1 ((x * w).1 * g)
    rw [Subgroup.coe_mul, mul_assoc]⟩
  left_inv F := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext w
    have h := congrArg (fun x => x.1 (1 : W)) (F.2 w g)
    change (F.1 (w.1 * g)).1 1 = (F.1 g).1 (1 * w) at h
    rw [one_mul] at h
    exact h
  right_inv f := by
    apply Subtype.ext
    funext g
    change f.1 ((1 : W).1 * g) = f.1 g
    rw [OneMemClass.coe_one, one_mul]
  isIntertwining' h := LinearMap.ext fun F => Subtype.ext (funext fun g => rfl)

theorem nonempty_coind_coind_iso (U W : Subgroup G) (hUW : U ≤ W) (A : Rep.{u} k G) :
    Nonempty (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A))) ≅
      Rep.coind U.subtype (Rep.res U.subtype A)) :=
  ⟨Rep.mkIso (coindStagesEquiv U W hUW A)⟩

end Stages

section PrimeToPart

variable {G : Type*} [Group G]

/-- **The `ℓ`-part of a cyclic quotient.** For open subgroups `U ≤ W` of finite index with `U` normal
and `W/U` cyclic, there is `U ≤ V ≤ W` with `V/U` cyclic of order prime to `ℓ`, `V` normal in `W` and
`W/V` cyclic of order a power of `ℓ`. -/
theorem exists_coprime_part (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (U W : Subgroup G) [hN : U.Normal]
    (hUi : U.index ≠ 0) (hle : U ≤ W) (hcyc : IsCyclic (W ⧸ U.subgroupOf W)) :
    ∃ V : Subgroup G, U ≤ V ∧ V ≤ W ∧ IsCyclic (V ⧸ U.subgroupOf V) ∧
      Nat.Coprime (U.subgroupOf V).index ℓ ∧
      ∃ hnorm : (V.subgroupOf W).Normal,
      (haveI := hnorm; IsCyclic (W ⧸ V.subgroupOf W)) ∧ ∃ a : ℕ, Nat.card (W ⧸ V.subgroupOf W) = ℓ ^ a := by
  classical
  have : U.FiniteIndex := ⟨hUi⟩
  have : (U.subgroupOf W).FiniteIndex := inferInstance
  have : Finite (W ⧸ U.subgroupOf W) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcomm : ∀ x y : W ⧸ U.subgroupOf W, x * y = y * x := fun x y =>
    (IsCyclic.commGroup (α := W ⧸ U.subgroupOf W)).mul_comm x y
  obtain ⟨n, hndef⟩ : ∃ n, n = Nat.card (W ⧸ U.subgroupOf W) := ⟨_, rfl⟩
  have hn : n ≠ 0 := hndef ▸ Nat.card_pos.ne'
  have hog : orderOf g = n := hndef ▸ orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨a, hadef⟩ : ∃ a, a = n.factorization ℓ := ⟨_, rfl⟩
  have hdvd : ℓ ^ a ∣ n := hadef ▸ Nat.ordProj_dvd n ℓ
  let C : Subgroup (W ⧸ U.subgroupOf W) := Subgroup.zpowers (g ^ (ℓ ^ a))
  have hCcard : Nat.card C = n / ℓ ^ a := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ hℓ.out.ne_zero) (hog ▸ hdvd), hog]
  have hCN : C.Normal := ⟨fun c hc q => by rw [hcomm q c, mul_assoc, mul_inv_cancel, mul_one]; exact hc⟩
  clear_value C
  let D : Subgroup W := C.comap (QuotientGroup.mk' (U.subgroupOf W))
  have hDN : D.Normal := hCN.comap _
  let V : Subgroup G := D.map W.subtype
  have hUV : U ≤ V := by
    intro u hu
    refine ⟨⟨u, hle hu⟩, ?_, rfl⟩
    change QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ ∈ C
    have h1 : QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨u, hle hu⟩ : W)).2 hu
    rw [h1]
    exact C.one_mem
  have hVW : V ≤ W := Subgroup.map_subtype_le D
  refine ⟨V, hUV, hVW, ?_⟩
  have hVD : V.subgroupOf W = D :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective W) D
  let ψ0 : V →* W ⧸ U.subgroupOf W :=
    (QuotientGroup.mk' (U.subgroupOf W)).comp (Subgroup.inclusion hVW)
  have hψ0 : ∀ v : V, ψ0 v ∈ C := by
    intro v
    obtain ⟨w, hw, hwv⟩ := v.2
    have h1 : Subgroup.inclusion hVW v = w := Subtype.ext hwv.symm
    change QuotientGroup.mk' (U.subgroupOf W) (Subgroup.inclusion hVW v) ∈ C
    rw [h1]
    exact hw
  let ψ : V →* C := ψ0.codRestrict C hψ0
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H w =>
      refine ⟨⟨w.1, ⟨w, hq, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hker : ψ.ker = U.subgroupOf V := by
    ext v
    constructor
    · intro h
      have h1 : ψ0 v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 h)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).1 h1
    · intro h
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).2 h
  let e : V ⧸ U.subgroupOf V ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hcardVU : Nat.card (V ⧸ U.subgroupOf V) = n / ℓ ^ a := (Nat.card_congr e.toEquiv).trans hCcard
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_, ?_⟩
  · change Nat.Coprime (Nat.card (V ⧸ U.subgroupOf V)) ℓ
    rw [hcardVU, hadef]
    exact (Nat.coprime_ordCompl hℓ.out hn).symm
  · rw [hVD]
    refine ⟨hDN, ?_, a, ?_⟩
    · let f : (W ⧸ U.subgroupOf W) →* W ⧸ D :=
        QuotientGroup.map (U.subgroupOf W) D (MonoidHom.id W) (by
          intro w hw
          change QuotientGroup.mk' (U.subgroupOf W) w ∈ C
          have h1 : QuotientGroup.mk' (U.subgroupOf W) w = 1 := (QuotientGroup.eq_one_iff w).2 hw
          rw [h1]
          exact C.one_mem)
      refine isCyclic_of_surjective f ?_
      intro x
      induction x using QuotientGroup.induction_on with
      | H w => exact ⟨QuotientGroup.mk w, rfl⟩
    · change D.index = ℓ ^ a
      have h1 : D.index = C.index :=
        Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h2 : Nat.card C * C.index = n := hndef ▸ Subgroup.card_mul_index C
      have h3 : ℓ ^ a * (n / ℓ ^ a) = n := hadef ▸ Nat.ordProj_mul_ordCompl_eq_self n ℓ
      have hpos : 0 < n / ℓ ^ a :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (pow_pos hℓ.out.pos _)
      rw [hCcard] at h2
      rw [h1]
      have : (n / ℓ ^ a) * C.index = (n / ℓ ^ a) * ℓ ^ a := by rw [h2, mul_comm, h3]
      exact Nat.eq_of_mul_eq_mul_left hpos this

end PrimeToPart

section GS

-- A separable closure of a number field is Galois over it; found first, before the search for
-- other ways to prove `IsGalois`.
attribute [local instance 2000] IsSepClosure.isGalois

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

theorem exists_card_eq_pow_of_nsmul_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {X : Type*} [AddCommGroup X]
    [Finite X] (h : ∀ m : X, ℓ • m = 0) : ∃ k, Nat.card X = ℓ ^ k :=
  exists_card_eq_pow_of_nsmul hℓ (r := 1) fun m => by rw [pow_one]; exact h m

/-- `X ↦ ratio(Ind_W^{G_S} X)` is multiplicative on `ℓ`-primary modules of an open subgroup `W`. -/
theorem isMultiplicativeOn_ratio_coind {ℓ : ℕ}
    [Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    IsMultiplicativeOn (fun n => ∃ k, n = ℓ ^ k)
      (fun (X : Rep.{u} (ULift.{u} ℤ) (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
        [IsSmoothRep X] => globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype X)) where
  iso {A B} _ _ _ _ e :=
    globalEulerRatio_eq_of_iso ι _
      ((Rep.coindFunctor (ULift.{u} ℤ) (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).mapIso e)
  shortExact {T} _ _ _ _ hT hP := by
    have hT' := shortExact_coindShortComplexOf (G := GaloisGroupUnramifiedOutside K Ω S)
      (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) hT
    obtain ⟨k, hk⟩ := hP
    have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸ (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :=
      Subgroup.finite_quotient_of_finiteIndex
    have hcc := card_coind (W : OpenSubgroup _) T.X₂
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) T).X₁ :=
      isSmoothRep_coind W T.X₁
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) T).X₂ :=
      isSmoothRep_coind W T.X₂
    have : IsSmoothRep (coindShortComplexOf (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) T).X₃ :=
      isSmoothRep_coind W T.X₃
    have : Finite (coindShortComplexOf (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) T).X₂ :=
      finite_coind W T.X₂
    have hn : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card (coindShortComplexOf
        (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) T).X₂ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
      intro v hv
      change ((Nat.card (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype T.X₂) :
        ℕ) : 𝓞 K) ∈ v.asIdeal at hv
      rw [hcc, hk, ← pow_mul, Nat.cast_pow] at hv
      exact hS v (v.isPrime.mem_of_pow_mem _ hv)
    have key := globalEulerRatio_shortExact ι hT' hn
    exact key

/-- **The `ℓ`-part of an induction.** For `V ⊆ W` open with `W/V` cyclic of order `ℓ^a` and `M` killed
by `ℓ`, `ratio(Ind_V M) = ratio(Ind_W M)^{ℓ^a}`. -/
theorem globalEulerRatio_coind_stage_pow {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W V : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) (hle : V ≤ W)
    [hN : ((V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W).Normal]
    [hc : IsCyclic (W ⧸ (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W)] {a : ℕ}
    (hcard : Nat.card (W ⧸ (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W) = ℓ ^ a)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0) :
    globalEulerRatio ι (Rep.coind (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) =
      globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) ^
        (ℓ ^ a) := by
  classical
  let H : OpenSubgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
    ⟨(V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W,
      V.isOpen.preimage continuous_subtype_val⟩
  have : (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).Normal := hN
  have : IsCyclic ((W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
      (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))) := hc
  have hχ := isMultiplicativeOn_ratio_coind ι hS W
  have hPdvd : ∀ m n, m ∣ n → (∃ k, n = ℓ ^ k) → (∃ k, m = ℓ ^ k) := by
    rintro m n hmn ⟨k, rfl⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hℓ.out).1 hmn
    exact ⟨j, rfl⟩
  have hPmul : ∀ m n, (∃ k, m = ℓ ^ k) → (∃ k, n = ℓ ^ k) → (∃ k, m * n = ℓ ^ k) := by
    rintro m n ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (pow_add ℓ i j).symm⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_nsmul_prime hℓ.out hℓM
  have : Finite (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) :=
    inferInstanceAs (Finite M)
  have : IsSmoothRep (Rep.coind (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).subtype
      (Rep.res (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).subtype
        (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M))) :=
    isSmoothRep_coind_res H _
  have hpow := hχ.coind_res_eq_pow hPdvd hPmul H (p := ℓ) hcard
    (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) ⟨k, hk⟩ (fun m => hℓM m)
  obtain ⟨e⟩ := nonempty_coind_coind_iso (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
    (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) hle M
  have : IsSmoothRep (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.coind (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).subtype
        (Rep.res (H : Subgroup (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).subtype
          (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)))) :=
    isSmoothRep_coind W _
  rw [← hpow]
  exact (globalEulerRatio_eq_of_iso ι _ e).symm

/-- **Induction from a cyclic quotient.** Let `U = G_S(L) ⊆ W = G_S(L')` with `U` normal and `W/U`
cyclic, and `M` killed by `ℓ`. If the formula holds over every field `K''` with `U ⊆ G_S(K'')`,
`G_S(K'')/U` cyclic of order prime to `ℓ`, for `M` viewed as a `G_S(K'')`-module, then it holds for
`Ind_W M`. -/
theorem globalEulerRatio_coind_eq_one {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    [(U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0)
    (hK : ∀ (K'' : IntermediateField K Ω) [NumberField K'']
      (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S),
      (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
        GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' →
      IsCyclic ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
        (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S))) →
      Nat.Coprime ((U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S))).index ℓ →
      ∀ ιK'' : PlaceEmbeddings K'' Ω, globalEulerRatio ιK'' (resToFixedField hK'' M) = 1)
    (W : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (hle : (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤ W)
    [((U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
      (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).Normal]
    (hcyc : IsCyclic ((W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
      (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))) :
    globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) = 1 := by
  classical
  let W' : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S) := W
  have hUi : (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨V, hUV, hVW, hcycV, hcop, hnorm, hcycW, a, hcard⟩ :=
    exists_coprime_part ℓ (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) W hUi hle hcyc
  let V' : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S) := ⟨V, Subgroup.isOpen_mono hUV U.isOpen⟩
  obtain ⟨K'', hK''f, hK'', hV⟩ := GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq (S := S) V'
  have hVeq : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) = V := by rw [hV]
  have : IsGalois K'' Ω := IsSepClosure.isGalois
  -- the prime-to-`ℓ` part: Shapiro and the hypothesis
  have : IsSmoothRep (Rep.coind (V' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (V' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) :=
    isSmoothRep_coind_res V' M
  have h1 : globalEulerRatio ι (Rep.coind (V' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (V' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) = 1 := by
    have ιK'' : PlaceEmbeddings K'' Ω := Classical.choice inferInstance
    have := hK K'' hK'' (hVeq ▸ hUV) (by rw [hVeq]; exact hcycV) (by rw [hVeq]; exact hcop) ιK''
    rw [← this, ← globalEulerRatio_coind_res hK'' ι ιK'' M]
    rw [hV]
  -- the `ℓ`-part: a power
  have h2 := globalEulerRatio_coind_stage_pow ι hS W' V' hVW (hN := hnorm) (hc := hcycW) hcard M hℓM
  have he : globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) ^ (ℓ ^ a) = 1 :=
    h2.symm.trans h1
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_nsmul_prime hℓ.out hℓM
  have : Finite (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) :=
    inferInstanceAs (Finite M)
  have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸ (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :=
    Subgroup.finite_quotient_of_finiteIndex
  have hcc := card_coind W' (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)
  have : Finite (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) := finite_coind W' _
  have hpos := globalEulerRatio_pos ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
    (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) (fun v hv => by
      rw [hcc] at hv
      change (((Nat.card M) ^ _ : ℕ) : 𝓞 K) ∈ v.asIdeal at hv
      rw [hk, ← pow_mul, Nat.cast_pow] at hv
      exact hS v (v.isPrime.mem_of_pow_mem _ hv))
  exact (pow_eq_one_iff_of_nonneg hpos.le (pow_ne_zero _ hℓ.out.ne_zero)).1 he

end GS

end

end Langlands.GaloisCohomology
