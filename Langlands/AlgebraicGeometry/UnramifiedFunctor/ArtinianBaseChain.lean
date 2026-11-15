import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseTools

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Step

variable {C X : Type u} [CommRing C] [CommRing X] [Algebra C X] [Algebra R C] [Algebra R X]
  [IsScalarTower R C X]

/-- The subalgebra `N + N y` of `X`, for an element `y` with `y² ∈ N + N y`. -/
def adjoinStep (N : Subalgebra C X) (y : X) (hy : ∃ a ∈ N, ∃ b ∈ N, y * y = a + b * y) :
    Subalgebra C X where
  carrier := {x | ∃ a ∈ N, ∃ b ∈ N, x = a + b * y}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    obtain ⟨a₀, ha₀, b₀, hb₀, h⟩ := hy
    refine ⟨a * a' + b * b' * a₀, ?_, a * b' + a' * b + b * b' * b₀, ?_, ?_⟩
    · exact N.add_mem (N.mul_mem ha ha') (N.mul_mem (N.mul_mem hb hb') ha₀)
    · exact N.add_mem (N.add_mem (N.mul_mem ha hb') (N.mul_mem ha' hb))
        (N.mul_mem (N.mul_mem hb hb') hb₀)
    · linear_combination (b * b') * h
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a + a', N.add_mem ha ha', b + b', N.add_mem hb hb', by ring⟩
  algebraMap_mem' c := ⟨algebraMap C X c, N.algebraMap_mem c, 0, N.zero_mem, by simp⟩

variable (N : Subalgebra C X) (y : X) (hy : ∃ a ∈ N, ∃ b ∈ N, y * y = a + b * y)

lemma le_adjoinStep : N ≤ adjoinStep N y hy := fun x hx ↦ ⟨x, hx, 0, N.zero_mem, by simp⟩

lemma mem_adjoinStep_self : y ∈ adjoinStep N y hy := ⟨0, N.zero_mem, 1, N.one_mem, by simp⟩

/-- One step of the chain: with (F4′), an element over `η` on `N + N y` gives one on `N`, when
`m_N y ⊆ N` and `y ∉ N`. -/
lemma step (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F)
    [IsLocalRing C] {ℓ : Type u} [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ))) [IsLocalRing N] [IsArtinianRing N]
    (hres : Function.Surjective ((residue N).comp (IsScalarTower.toAlgHom R C N).toRingHom))
    (hyN : y ∉ N) (hmy : ∀ n : N, n ∈ maximalIdeal N → (n : X) * y ∈ N)
    (w' : F.obj (op (ovR R (adjoinStep N y hy))))
    (hw' : IsOver (IsScalarTower.toAlgHom R C (adjoinStep N y hy)) π η w') :
    ∃ w : F.obj (op (ovR R N)), IsOver (IsScalarTower.toAlgHom R C N) π η w := by
  let N' := adjoinStep N y hy
  let ι := Subalgebra.inclusion (le_adjoinStep N y hy)
  let : Algebra N N' := ι.toRingHom.toAlgebra
  have : IsScalarTower R N N' := IsScalarTower.of_algebraMap_eq (fun r ↦ rfl)
  let y' : N' := ⟨y, mem_adjoinStep_self N y hy⟩
  have hsmul : ∀ (n : N) (z : N'), ((n • z : N') : X) = (n : X) * (z : X) := fun n z ↦ rfl
  have hdec : ∀ z : N', ∃ a b : N, z = a • (1 : N') + b • y' := by
    rintro ⟨z, a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    simp only [Subalgebra.coe_add, hsmul, Subalgebra.coe_one, mul_one]
    rfl
  have hfin : Module.Finite N N' := by
    classical
    refine ⟨⟨{1, y'}, eq_top_iff.mpr fun z _ ↦ ?_⟩⟩
    obtain ⟨a, b, rfl⟩ := hdec z
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hinj : Function.Injective (algebraMap N N') := Subalgebra.inclusion_injective _
  have hlen : Module.length N (N' ⧸ LinearMap.range (Algebra.linearMap N N')) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
    let q : N' →ₗ[N] N' ⧸ LinearMap.range (Algebra.linearMap N N') :=
      Submodule.mkQ _
    have hq1 : q 1 = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, by rw [Algebra.linearMap_apply, map_one]⟩
    have hqy : q y' ≠ 0 := by
      rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
      rintro ⟨n, hn⟩
      apply hyN
      have : (n : X) = y := congrArg Subtype.val hn
      exact this ▸ n.2
    have hgen : ∀ z, ∃ b : N, z = b • q y' := by
      intro z
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
      obtain ⟨a, b, rfl⟩ := hdec z
      exact ⟨b, by rw [map_add, map_smul, map_smul, hq1, smul_zero, zero_add]⟩
    have hkill : ∀ n : N, n ∈ maximalIdeal N → n • q y' = 0 := by
      intro n hn
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨_, hmy n hn⟩, Subtype.ext rfl⟩
    refine ⟨⟨q y', 0, hqy⟩, fun x hx z ↦ ?_⟩
    obtain ⟨n₀, rfl⟩ := hgen x
    have hu : IsUnit n₀ := by
      by_contra hu
      exact hx (hkill n₀ ((mem_maximalIdeal n₀).mpr hu))
    obtain ⟨b, rfl⟩ := hgen z
    refine ⟨b * hu.unit⁻¹, ?_⟩
    simp only [LinearMap.toSpanSingleton_apply, smul_smul, mul_assoc, IsUnit.val_inv_mul,
      mul_one]
  exact artLift h4 hZ h5 π hπ η N N' (IsScalarTower.toAlgHom R C N) hres hinj hlen w' hw'

end Step


section Chain

variable {C X : Type u} [CommRing C] [CommRing X] [Algebra C X] [Algebra R C] [Algebra R X]
  [IsScalarTower R C X]

/-- The subalgebra `C + J` of `X`. -/
def subD (J : Ideal X) : Subalgebra C X where
  carrier := {x | ∃ c : C, x - algebraMap C X c ∈ J}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    have : x * y - algebraMap C X (c * d) =
        (x - algebraMap C X c) * y + algebraMap C X c * (y - algebraMap C X d) := by
      rw [map_mul]; ring
    rw [this]
    exact J.add_mem (J.mul_mem_right _ hc) (J.mul_mem_left _ hd)
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    have : x + y - algebraMap C X (c + d) = (x - algebraMap C X c) + (y - algebraMap C X d) := by
      rw [map_add]; ring
    rw [this]
    exact J.add_mem hc hd
  algebraMap_mem' c := ⟨c, by simp⟩

variable [IsLocalRing C] [IsArtinianRing C] (J : Ideal X) (hJ : IsNilpotent J)
  (hmJ : ∀ c ∈ maximalIdeal C, algebraMap C X c ∈ J) (hinj : Function.Injective (algebraMap C X))

omit [IsLocalRing C] [IsArtinianRing C] in
include hJ in
lemma isNilpotent_of_mem {x : X} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  rw [hn] at this
  simpa using this

omit [IsArtinianRing C] in
include hJ hinj in
lemma one_notMem : (1 : X) ∉ J := by
  intro h
  obtain ⟨n, hn⟩ := isNilpotent_of_mem J hJ h
  rw [one_pow] at hn
  exact zero_ne_one (hinj (by rw [map_zero, map_one, hn]))

omit [IsArtinianRing C] in
include hJ hmJ in
lemma isUnit_or_mem {N : Subalgebra C X} (hN : N ≤ subD J) (n : N) :
    IsUnit n ∨ (n : X) ∈ J := by
  obtain ⟨c, hc⟩ := hN n.2
  by_cases hu : IsUnit c
  · left
    let u : N := algebraMap C N (hu.unit⁻¹ : Cˣ)
    let t : N := u * n - 1
    have ht : (t : X) = algebraMap C X (hu.unit⁻¹ : Cˣ) * ((n : X) - algebraMap C X c) := by
      simp only [t, u, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
        Subalgebra.coe_one, mul_sub, ← map_mul]
      rw [show (hu.unit⁻¹ : Cˣ).val * c = 1 from hu.val_inv_mul, map_one]
    have htn : IsNilpotent t := by
      obtain ⟨k, hk⟩ := isNilpotent_of_mem J hJ (ht ▸ J.mul_mem_left _ hc)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have h1 : IsUnit (u * n) := by
      have := htn.isUnit_one_add
      simpa [t] using this
    exact isUnit_of_mul_isUnit_right h1
  · right
    have := J.add_mem hc (hmJ c ((mem_maximalIdeal c).mpr hu))
    simpa using this

omit [IsArtinianRing C] in
include hJ hinj in
lemma not_isUnit_of_mem {N : Subalgebra C X} {n : N} (h : (n : X) ∈ J) : ¬ IsUnit n := by
  rintro ⟨u, rfl⟩
  apply one_notMem J hJ hinj
  have := J.mul_mem_right (((u⁻¹ : Nˣ) : N) : X) h
  rw [← Subalgebra.coe_mul, Units.mul_inv] at this
  simpa using this

omit [IsArtinianRing C] in
include hJ hmJ hinj in
lemma isLocalRing_of_le {N : Subalgebra C X} (hN : N ≤ subD J) : IsLocalRing N := by
  have : Nontrivial N := ⟨⟨0, 1, fun h ↦ one_notMem J hJ hinj (by
    have := congrArg Subtype.val h
    simp only [Subalgebra.coe_zero, Subalgebra.coe_one] at this
    rw [← this]; exact J.zero_mem)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun n ↦ ?_
  rcases isUnit_or_mem J hJ hmJ hN n with h | h
  · exact Or.inl h
  · right
    rcases isUnit_or_mem J hJ hmJ hN (1 - n) with h' | h'
    · exact h'
    · exfalso
      apply one_notMem J hJ hinj
      have := J.add_mem h h'
      simpa using this

omit [IsArtinianRing C] in
include hJ hmJ hinj in
lemma mem_maximalIdeal_iff {N : Subalgebra C X} (hN : N ≤ subD J) [IsLocalRing N] (n : N) :
    n ∈ maximalIdeal N ↔ (n : X) ∈ J := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ↦ ?_, not_isUnit_of_mem J hJ hinj⟩
  rcases isUnit_or_mem J hJ hmJ hN n with h' | h'
  · exact absurd h' h
  · exact h'

include hJ hmJ hinj in
lemma isArtinianRing_of_le [Module.Finite C X] {N : Subalgebra C X} (hN : N ≤ subD J)
    [IsLocalRing N] : IsArtinianRing N := by
  have : IsNoetherian C N := inferInstanceAs (IsNoetherian C (Subalgebra.toSubmodule N))
  have : IsNoetherianRing N := isNoetherian_of_tower C inferInstance
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  obtain ⟨k, hk⟩ := id hJ
  refine ⟨k, ?_⟩
  have hle : maximalIdeal N ≤ J.comap N.val.toRingHom := fun n hn ↦
    (mem_maximalIdeal_iff J hJ hmJ hinj hN n).mp hn
  refine le_bot_iff.mp ((Ideal.pow_right_mono hle k).trans ((Ideal.le_comap_pow _ k).trans ?_))
  intro n hn
  simp only [Ideal.mem_comap, hk, Ideal.zero_eq_bot, Ideal.mem_bot] at hn
  exact Subtype.ext hn

omit [IsArtinianRing C] in
include hJ hmJ hinj in
lemma residue_comp_surjective {N : Subalgebra C X} (hN : N ≤ subD J) [IsLocalRing N] :
    Function.Surjective ((residue N).comp (IsScalarTower.toAlgHom R C N).toRingHom) := by
  intro z
  obtain ⟨n, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨c, hc⟩ := hN n.2
  refine ⟨c, ?_⟩
  change Ideal.Quotient.mk _ (algebraMap C N c) = Ideal.Quotient.mk _ n
  rw [Ideal.Quotient.eq, mem_maximalIdeal_iff J hJ hmJ hinj hN]
  have := J.neg_mem hc
  simpa using this

include hJ hmJ hinj in
/-- The chain argument: an element over `η` on `C + J` gives one on every subalgebra between `C`
and `C + J`, by descending induction with (F4′) at each step. -/
lemma chain [Module.Finite C X] (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (h5 : NilpotentInjective F) {ℓ : Type u} [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ)))
    (hD : ∃ w : F.obj (op (ovR R (subD (C := C) J))),
      IsOver (IsScalarTower.toAlgHom R C (subD (C := C) J)) π η w) :
    ∀ N : Subalgebra C X, N ≤ subD J →
      ∃ w : F.obj (op (ovR R N)), IsOver (IsScalarTower.toAlgHom R C N) π η w := by
  have hwf : WellFounded (fun A B : Subalgebra C X ↦ B < A) :=
    Subrelation.wf (fun {A B} h ↦ Subalgebra.toSubmodule.strictMono h)
      (InvImage.wf (fun N : Subalgebra C X ↦ Subalgebra.toSubmodule N) wellFounded_gt)
  intro N
  induction N using hwf.induction with
  | h N ih =>
  intro hND
  by_cases hN : N = subD J
  · subst hN
    exact hD
  classical
  obtain ⟨n₀, hn₀⟩ := id hJ
  have hPn : ∃ k, ∀ x ∈ J ^ k, x ∈ N := ⟨n₀, fun x hx ↦ by
    rw [hn₀, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
    rw [hx]
    exact N.zero_mem⟩
  have hk : ∀ x ∈ J ^ Nat.find hPn, x ∈ N := Nat.find_spec hPn
  have hP1 : ¬ ∀ x ∈ J ^ 1, x ∈ N := by
    intro h
    apply hN
    refine le_antisymm hND fun x ⟨c, hc⟩ ↦ ?_
    have h1 := h _ (by rw [pow_one]; exact hc)
    have := N.add_mem h1 (N.algebraMap_mem c)
    simpa using this
  have hk2 : 2 ≤ Nat.find hPn := by
    by_contra hlt
    push Not at hlt
    exact hP1 fun x hx ↦ hk x (Ideal.pow_le_pow_right (by omega) hx)
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hPn = i + 1 := ⟨Nat.find hPn - 1, by omega⟩
  have hPi : ¬ ∀ x ∈ J ^ i, x ∈ N := Nat.find_min hPn (by omega)
  have hPi1 : ∀ x ∈ J ^ (i + 1), x ∈ N := hi ▸ hk
  push Not at hPi
  obtain ⟨y, hyJ, hyN⟩ := hPi
  have hyJ1 : y ∈ J := Ideal.pow_le_self (by omega) hyJ
  have hy : ∃ a ∈ N, ∃ b ∈ N, y * y = a + b * y := by
    refine ⟨y * y, hPi1 _ ?_, 0, N.zero_mem, by simp⟩
    have := Ideal.mul_mem_mul hyJ hyJ
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this
  have := isLocalRing_of_le J hJ hmJ hinj hND
  have := isArtinianRing_of_le J hJ hmJ hinj hND
  have hmy : ∀ n : N, n ∈ maximalIdeal N → (n : X) * y ∈ N := fun n hn ↦
    hPi1 _ (by
      rw [pow_succ']
      exact Ideal.mul_mem_mul ((mem_maximalIdeal_iff J hJ hmJ hinj hND n).mp hn) hyJ)
  have hN'D : adjoinStep N y hy ≤ subD J := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (subD J).add_mem (hND ha) ((subD J).mul_mem (hND hb) ⟨0, by simpa using hyJ1⟩)
  have hlt : N < adjoinStep N y hy := lt_of_le_of_ne (le_adjoinStep N y hy) (fun h ↦ hyN (by
    rw [h]
    exact mem_adjoinStep_self N y hy))
  obtain ⟨w', hw'⟩ := ih _ hlt hN'D
  exact step N y hy h4 hZ h5 π hπ η (residue_comp_surjective J hJ hmJ hinj hND) hyN hmy w' hw'

include hJ hmJ hinj in
/-- The bottom of the chain: an element over `η` on `C + J` gives an element of `F(Spec C)`
restricting to `η`. -/
lemma descend [Module.Finite C X] (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (h5 : NilpotentInjective F) {ℓ : Type u} [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ)))
    (hD : ∃ w : F.obj (op (ovR R (subD (C := C) J))),
      IsOver (IsScalarTower.toAlgHom R C (subD (C := C) J)) π η w) :
    ∃ w : F.obj (op (ovR R C)), res π w = η := by
  obtain ⟨w, hw⟩ := chain J hJ hmJ hinj h4 hZ h5 π hπ η hD ⊥ bot_le
  let e : (⊥ : Subalgebra C X) ≃ₐ[R] C := (Algebra.botEquivOfInjective hinj).restrictScalars R
  refine ⟨res e.toAlgHom w, IsOver.res_eq ?_⟩
  have h := hw.restrict e.toAlgHom
  have he : e.toAlgHom.comp (IsScalarTower.toAlgHom R C (⊥ : Subalgebra C X)) = AlgHom.id R C := by
    ext c
    exact e.apply_symm_apply c
  rwa [he] at h

end Chain


section Factor

/-- An `R`-algebra map killing the kernel of a surjection factors through it. -/
lemma exists_factor {A B K : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing K] [Algebra R K] (f : A →ₐ[R] B) (hf : Function.Surjective f) (ψ : A →ₐ[R] K)
    (h : ∀ a, f a = 0 → ψ a = 0) : ∃ ψ' : B →ₐ[R] K, ψ'.comp f = ψ := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) ψ (fun a ha ↦ h a ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom, ?_⟩
  ext a
  have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) =
      Ideal.Quotient.mk (RingHom.ker f) a :=
    (AlgEquiv.symm_apply_eq _).mpr rfl
  change (Ideal.Quotient.liftₐ (RingHom.ker f) ψ (fun a ha ↦ h a ha))
    ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a)) = ψ a
  rw [this]
  rfl

/-- A map from a product to a field factors through one of the projections. -/
lemma prod_field_cases {A B K : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Field K] [Algebra R K] (ψ : A × B →ₐ[R] K) :
    (∃ ψ₁ : A →ₐ[R] K, ψ₁.comp (AlgHom.fst R A B) = ψ) ∨
      (∃ ψ₂ : B →ₐ[R] K, ψ₂.comp (AlgHom.snd R A B) = ψ) := by
  have he : ψ (1, 0) * ψ (1, 0) = ψ (1, 0) := by rw [← map_mul]; simp
  have he' : ψ (1, 0) + ψ (0, 1) = 1 := by
    have : ((1, 0) : A × B) + (0, 1) = 1 := by ext <;> simp
    rw [← map_add, this, map_one]
  have hz : ψ (1, 0) * (ψ (1, 0) - 1) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · right
    refine exists_factor _ Prod.snd_surjective ψ fun x hx ↦ ?_
    have : x = x * (1, 0) := by ext <;> simp [show x.2 = 0 from hx]
    rw [this, map_mul, h0, mul_zero]
  · left
    refine exists_factor _ Prod.fst_surjective ψ fun x hx ↦ ?_
    have : x = x * (0, 1) := by ext <;> simp [show x.1 = 0 from hx]
    rw [sub_eq_zero] at h1
    rw [this, map_mul, show ψ (0, 1) = 0 by rw [h1] at he'; linear_combination he', mul_zero]

/-- `IsOver` along a surjection `q` from `IsOver` along the identity. -/
lemma isOver_of_surjective {P Q ℓ : Type u} [CommRing P] [Algebra R P] [CommRing Q] [Algebra R Q]
    [CommRing ℓ] [Algebra R ℓ] (q : P →ₐ[R] Q) (hq : Function.Surjective q) (π' : Q →ₐ[R] ℓ)
    {η : F.obj (op (ovR R ℓ))} {w : F.obj (op (ovR R Q))} (hw : res π' w = η) :
    IsOver q (π'.comp q) η w := fun K _ _ ψ ψ₀ hψ ↦ by
  have : ψ₀.comp π' = ψ := by
    ext x
    obtain ⟨p, rfl⟩ := hq x
    exact congrArg (fun f ↦ f p) hψ
  rw [← this, ← res_res, hw]

end Factor

section Apps

/-- Same residue field: let `C ⊆ A` be local artinian rings, `A` finite over `C`, with the residue
field of `A` reached from `C`. An element of `F(Spec A)` over `η` gives an element of `F(Spec C)`
restricting to `η`. -/
lemma descend_local (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F)
    {C A : Type u} [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Algebra R C] [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    [Module.Finite C A] (hinj : Function.Injective (algebraMap C A))
    (hloc : ∀ c ∈ maximalIdeal C, algebraMap C A c ∈ maximalIdeal A)
    (hres : Function.Surjective ((residue A).comp (algebraMap C A)))
    {ℓ : Type u} [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ) (hπ : Function.Surjective π)
    (η : F.obj (op (ovR R ℓ))) (v : F.obj (op (ovR R A)))
    (hv : IsOver (IsScalarTower.toAlgHom R C A) π η v) :
    ∃ w : F.obj (op (ovR R C)), res π w = η := by
  let J := maximalIdeal A
  have hJ : IsNilpotent J := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have htop : ∀ x : A, x ∈ subD (C := C) J := fun x ↦ by
    obtain ⟨c, hc⟩ := hres (residue A x)
    refine ⟨c, ?_⟩
    have : residue A x = residue A (algebraMap C A c) := hc.symm
    rw [← Ideal.Quotient.eq]
    exact this
  let φ : A →ₐ[R] subD (C := C) J :=
    { toFun := fun x ↦ ⟨x, htop x⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  refine descend J hJ hloc hinj h4 hZ h5 π hπ η ⟨res φ v, ?_⟩
  have := hv.restrict φ
  have hφ : φ.comp (IsScalarTower.toAlgHom R C A) = IsScalarTower.toAlgHom R C (subD (C := C) J) := by
    ext
    rfl
  rwa [hφ] at this

/-- Intersection closure: if `η` lifts to `P/I` and to `P/I'` (`P` local artinian), it lifts to
`P/(I ∩ I')`. The ring `P/(I ∩ I')` sits in `P/I × P/I'`; the chain argument descends from
`C + J` to `C`, after one more length-one step from the product down to `C + J`. -/
lemma inter_closed (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F)
    {P ℓ : Type u} [CommRing P] [IsLocalRing P] [IsArtinianRing P] [Algebra R P] [Field ℓ]
    [Algebra R ℓ] (π : P →ₐ[R] ℓ) (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ)))
    (I I' : Ideal P)
    (hI : ∃ w : F.obj (op (ovR R (P ⧸ I))), IsOver (Ideal.Quotient.mkₐ R I) π η w)
    (hI' : ∃ w : F.obj (op (ovR R (P ⧸ I'))), IsOver (Ideal.Quotient.mkₐ R I') π η w) :
    ∃ w : F.obj (op (ovR R (P ⧸ (I ⊓ I')))), IsOver (Ideal.Quotient.mkₐ R (I ⊓ I')) π η w := by
  by_cases hIt : I = ⊤
  · rw [hIt, top_inf_eq]
    exact hI'
  by_cases hI't : I' = ⊤
  · rw [hI't, inf_top_eq]
    exact hI
  obtain ⟨wI, hwI⟩ := hI
  obtain ⟨wI', hwI'⟩ := hI'
  have hkerπ : RingHom.ker π = maximalIdeal P :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
  have hIm : I ≤ maximalIdeal P := le_maximalIdeal hIt
  have hI'm : I' ≤ maximalIdeal P := le_maximalIdeal hI't
  have hle : I ⊓ I' ≤ maximalIdeal P := inf_le_left.trans hIm
  have hnil : IsNilpotent (I ⊓ I') := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal P).mp inferInstance
    exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans (by rw [hn]; rfl))⟩
  let Q := P ⧸ (I ⊓ I')
  have : IsLocalRing Q := Charts.isLocalRing_quotient hnil
  obtain ⟨πQ, hπQ⟩ := exists_factor (Ideal.Quotient.mkₐ R (I ⊓ I'))
    Ideal.Quotient.mk_surjective π (fun a ha ↦ by
      rw [← RingHom.mem_ker, hkerπ]
      exact hle ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  have hπQs : Function.Surjective πQ := fun z ↦ by
    obtain ⟨p, rfl⟩ := hπ z
    exact ⟨Ideal.Quotient.mk _ p, congrArg (fun f ↦ f p) hπQ⟩
  obtain ⟨πI, hπI⟩ := exists_factor (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective π
    (fun a ha ↦ by
      rw [← RingHom.mem_ker, hkerπ]
      exact hIm ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  obtain ⟨πI', hπI'⟩ := exists_factor (Ideal.Quotient.mkₐ R I') Ideal.Quotient.mk_surjective π
    (fun a ha ↦ by
      rw [← RingHom.mem_ker, hkerπ]
      exact hI'm ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  let X := (P ⧸ I) × (P ⧸ I')
  let f : Q →+* X := RingHom.prod (Ideal.Quotient.factor inf_le_left)
    (Ideal.Quotient.factor inf_le_right)
  let : Algebra Q X := f.toAlgebra
  have : IsScalarTower R Q X := IsScalarTower.of_algebraMap_eq (fun r ↦ rfl)
  have hf : ∀ p : P, algebraMap Q X (Ideal.Quotient.mk _ p) =
      (Ideal.Quotient.mk I p, Ideal.Quotient.mk I' p) := fun p ↦ rfl
  have hinj : Function.Injective (algebraMap Q X) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hf, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ⟨hq.1, hq.2⟩
  have hdec : ∀ x : X, ∃ a b : P, x = algebraMap Q X (Ideal.Quotient.mk _ b) +
      (algebraMap Q X (Ideal.Quotient.mk _ a) - algebraMap Q X (Ideal.Quotient.mk _ b)) *
        ((1, 0) : X) := by
    rintro ⟨x₁, x₂⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    refine ⟨a, b, ?_⟩
    rw [hf, hf]
    refine Prod.ext ?_ ?_
    · show Ideal.Quotient.mk I a = Ideal.Quotient.mk I b +
        (Ideal.Quotient.mk I a - Ideal.Quotient.mk I b) * 1
      ring
    · show Ideal.Quotient.mk I' b = Ideal.Quotient.mk I' b +
        (Ideal.Quotient.mk I' a - Ideal.Quotient.mk I' b) * 0
      ring
  have : Module.Finite Q X := by
    classical
    refine ⟨⟨{1, (1, 0)}, eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
    obtain ⟨a, b, rfl⟩ := hdec x
    have e1 : algebraMap Q X (Ideal.Quotient.mk _ b) = (Ideal.Quotient.mk _ b : Q) • (1 : X) :=
      Algebra.algebraMap_eq_smul_one _
    have e2 : (algebraMap Q X (Ideal.Quotient.mk _ a) - algebraMap Q X (Ideal.Quotient.mk _ b)) *
        ((1, 0) : X) = (Ideal.Quotient.mk _ a : Q) • ((1, 0) : X) -
          (Ideal.Quotient.mk _ b : Q) • ((1, 0) : X) := by
      rw [sub_mul, Algebra.smul_def, Algebra.smul_def]
    rw [e2, e1]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  let J : Ideal X := (maximalIdeal Q).map (algebraMap Q X)
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal Q).mp inferInstance
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  have hmJ : ∀ c ∈ maximalIdeal Q, algebraMap Q X c ∈ J := fun c hc ↦ Ideal.mem_map_of_mem _ hc
  let D := subD (C := Q) J
  have := isLocalRing_of_le J hJ hmJ hinj (le_refl D)
  have := isArtinianRing_of_le J hJ hmJ hinj (le_refl D)
  let y : X := (1, 0)
  have hy : ∃ a ∈ D, ∃ b ∈ D, y * y = a + b * y :=
    ⟨0, D.zero_mem, 1, D.one_mem, by
      simp only [zero_add, one_mul]
      exact Prod.ext (mul_one _) (mul_zero _)⟩
  -- the two maps `X → ℓ` killing `J`
  let χ₁ : X →+* ℓ := πI.toRingHom.comp (RingHom.fst _ _)
  let χ₂ : X →+* ℓ := πI'.toRingHom.comp (RingHom.snd _ _)
  have hχ₁ : ∀ q : Q, χ₁ (algebraMap Q X q) = πQ q := fun q ↦ by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hf]
    exact (congrArg (fun g ↦ g p) hπI).trans (congrArg (fun g ↦ g p) hπQ).symm
  have hχ₂ : ∀ q : Q, χ₂ (algebraMap Q X q) = πQ q := fun q ↦ by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hf]
    exact (congrArg (fun g ↦ g p) hπI').trans (congrArg (fun g ↦ g p) hπQ).symm
  have hkerQ : RingHom.ker πQ = maximalIdeal Q :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπQs)
  have hJχ : ∀ (χ : X →+* ℓ), (∀ q : Q, χ (algebraMap Q X q) = πQ q) → ∀ z ∈ J, χ z = 0 := by
    intro χ hχ z hz
    have : J ≤ RingHom.ker χ := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker, hχ, ← RingHom.mem_ker, hkerQ]
      exact hc
    exact this hz
  have hyD : y ∉ D := by
    rintro ⟨c, hc⟩
    have h1 := hJχ χ₁ hχ₁ _ hc
    have h2 := hJχ χ₂ hχ₂ _ hc
    rw [map_sub, hχ₁] at h1
    rw [map_sub, hχ₂] at h2
    have e1 : χ₁ y = 1 := show πI (1 : P ⧸ I) = 1 from map_one _
    have e2 : χ₂ y = 0 := show πI' (0 : P ⧸ I') = 0 from map_zero _
    rw [e1] at h1
    rw [e2] at h2
    exact one_ne_zero (by linear_combination h1 - h2)
  have hmy : ∀ n : D, n ∈ maximalIdeal D → (n : X) * y ∈ D := fun n hn ↦
    ⟨0, by simpa using J.mul_mem_right y ((mem_maximalIdeal_iff J hJ hmJ hinj le_rfl n).mp hn)⟩
  have htop : ∀ x : X, x ∈ adjoinStep D y hy := fun x ↦ by
    obtain ⟨a, b, hx⟩ := hdec x
    exact ⟨_, D.algebraMap_mem _, _, D.sub_mem (D.algebraMap_mem _) (D.algebraMap_mem _), hx⟩
  obtain ⟨wX, hwX₁, hwX₂⟩ := exists_prod hZ (P ⧸ I) (P ⧸ I') wI wI'
  have hwX : IsOver (IsScalarTower.toAlgHom R Q X) πQ η wX := by
    intro K _ _ ψ ψ₀ hψ
    rcases prod_field_cases ψ with ⟨ψ₁, rfl⟩ | ⟨ψ₂, rfl⟩
    · rw [← res_res, hwX₁]
      refine hwI K ψ₁ ψ₀ ?_
      ext p
      have h1 : ψ₀ (π p) = ψ₀ (πQ (Ideal.Quotient.mk (I ⊓ I') p)) := by rw [← hπQ]; rfl
      have h2 := congrArg (fun g ↦ g (Ideal.Quotient.mk (I ⊓ I') p)) hψ
      show ψ₀ (π p) = ψ₁ (Ideal.Quotient.mk I p)
      rw [h1]
      exact h2
    · rw [← res_res, hwX₂]
      refine hwI' K ψ₂ ψ₀ ?_
      ext p
      have h1 : ψ₀ (π p) = ψ₀ (πQ (Ideal.Quotient.mk (I ⊓ I') p)) := by rw [← hπQ]; rfl
      have h2 := congrArg (fun g ↦ g (Ideal.Quotient.mk (I ⊓ I') p)) hψ
      show ψ₀ (π p) = ψ₂ (Ideal.Quotient.mk I' p)
      rw [h1]
      exact h2
  let φ : X →ₐ[R] adjoinStep D y hy :=
    { toFun := fun x ↦ ⟨x, htop x⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  have hw' := hwX.restrict φ
  have hφ : φ.comp (IsScalarTower.toAlgHom R Q X) =
      IsScalarTower.toAlgHom R Q (adjoinStep D y hy) :=
    AlgHom.ext fun _ ↦ rfl
  rw [hφ] at hw'
  obtain ⟨wD, hwD⟩ := step D y hy h4 hZ h5 πQ hπQs η
    (residue_comp_surjective J hJ hmJ hinj le_rfl) hyD hmy _ hw'
  obtain ⟨wQ, hwQ⟩ := descend J hJ hmJ hinj h4 hZ h5 πQ hπQs η ⟨wD, hwD⟩
  refine ⟨wQ, ?_⟩
  have := isOver_of_surjective (Ideal.Quotient.mkₐ R (I ⊓ I')) Ideal.Quotient.mk_surjective πQ hwQ
  rwa [hπQ] at this

end Apps

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
