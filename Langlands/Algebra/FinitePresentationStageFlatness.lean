import Langlands.Algebra.FinitePresentationStages
import Langlands.Algebra.LocalApproximationFlatnessDescent
import Langlands.Algebra.RingAdditiveColimit
import Langlands.Algebra.PrimeLocalizationCriterion
import Langlands.Algebra.EssFinitePresentationTransportProof
import Langlands.Algebra.EssFinitePresentationTowerCancellationProof

/-! # Flatness at a prime descends to a finite stage -/

open TensorProduct

namespace Langlands.Algebra.FinitePresentationStages

section LocalizedSystem

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  (f : ∀ i j, i ≤ j → G i →+* G j) {R : Type*} [CommRing R] (g : ∀ i, G i →+* R)
  (hg : ∀ i j h x, g j (f i j h x) = g i x) (p : Ideal R) [p.IsPrime]
  (P : ∀ i, Ideal (G i)) [∀ i, (P i).IsPrime] (hP : ∀ i, P i = p.comap (g i))

omit [p.IsPrime] [∀ i, (P i).IsPrime] in
include hg hP in
theorem comap_locPrime (i j : ι) (h : i ≤ j) : P i = (P j).comap (f i j h) := by
  ext x
  rw [hP, hP, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, hg]

/-- The transition maps of a directed system localized at compatible primes. -/
noncomputable def locMap (i j : ι) (h : i ≤ j) :
    Localization.AtPrime (P i) →+* Localization.AtPrime (P j) :=
  Localization.localRingHom (P i) (P j) (f i j h) (comap_locPrime f g hg p P hP i j h)

/-- The cocone maps of a directed system localized at compatible primes. -/
noncomputable def locι (i : ι) : Localization.AtPrime (P i) →+* Localization.AtPrime p :=
  Localization.localRingHom (P i) p (g i) (hP i)

omit [p.IsPrime] in
theorem locMap_algebraMap (i j : ι) (h : i ≤ j) (x : G i) :
    locMap f g hg p P hP i j h (algebraMap _ _ x) = algebraMap _ _ (f i j h x) :=
  Localization.localRingHom_to_map _ _ _ _ x

omit [Preorder ι] in
theorem locι_algebraMap (i : ι) (x : G i) :
    locι g p P hP i (algebraMap _ _ x) = algebraMap _ _ (g i x) :=
  Localization.localRingHom_to_map _ _ _ _ x

theorem locι_locMap (i j : ι) (h : i ≤ j) (x : Localization.AtPrime (P i)) :
    locι g p P hP j (locMap f g hg p P hP i j h x) = locι g p P hP i x := by
  have : (locι g p P hP j).comp (locMap f g hg p P hP i j h) = locι g p P hP i :=
    IsLocalization.ringHom_ext (P i).primeCompl <| RingHom.ext fun y ↦ by
      simp only [RingHom.comp_apply, locMap_algebraMap, locι_algebraMap, hg]
  exact DFunLike.congr_fun this x

omit [p.IsPrime] in
theorem directedSystem_locMap [hG : DirectedSystem G fun i j h ↦ f i j h] :
    DirectedSystem (fun i ↦ Localization.AtPrime (P i))
      fun i j h ↦ locMap f g hg p P hP i j h where
  map_self := by
    intro i x
    have : locMap f g hg p P hP i i le_rfl = RingHom.id _ :=
      IsLocalization.ringHom_ext (P i).primeCompl <| RingHom.ext fun y ↦ by
        simp only [RingHom.comp_apply, RingHom.id_apply, locMap_algebraMap]
        exact congrArg _ (hG.map_self y)
    exact DFunLike.congr_fun this x
  map_map := by
    intro k j i hij hjk x
    have : (locMap f g hg p P hP j k hjk).comp (locMap f g hg p P hP i j hij) =
        locMap f g hg p P hP i k (hij.trans hjk) :=
      IsLocalization.ringHom_ext (P i).primeCompl <| RingHom.ext fun y ↦ by
        simp only [RingHom.comp_apply, locMap_algebraMap]
        exact congrArg _ (hG.map_map hij hjk y)
    exact DFunLike.congr_fun this x

/-- If every element of `R` comes from a stage and every element killed in `R` is killed at
a later stage, then the localized system has colimit `R_p`. -/
theorem bijective_lift_locι [Nonempty ι] [IsDirectedOrder ι]
    [hG : DirectedSystem G fun i j h ↦ f i j h]
    (hsurj : ∀ r : R, ∃ i, ∃ x : G i, g i x = r)
    (hker : ∀ i (x : G i), g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) :
    Function.Bijective (Ring.DirectLimit.lift (fun i ↦ Localization.AtPrime (P i))
      (fun i j h ↦ locMap f g hg p P hP i j h) (Localization.AtPrime p) (locι g p P hP)
      (locι_locMap f g hg p P hP)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    rw [Ring.DirectLimit.lift_of] at hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P i).primeCompl x
    rw [locι, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨u, hu⟩, hua⟩ := hz
    obtain ⟨j, v, rfl⟩ := hsurj u
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have h0 : g k (f j k hjk v * f i k hik a) = 0 := by
      rw [map_mul, hg, hg]
      exact hua
    obtain ⟨l, hkl, hl⟩ := hker k _ h0
    have hv : f k l hkl (f j k hjk v) ∈ (P l).primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hP, Ideal.mem_comap, hg, hg]
      exact hu
    have hloc : locMap f g hg p P hP i l (hik.trans hkl) (IsLocalization.mk' _ a s) = 0 := by
      rw [locMap, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff]
      refine ⟨⟨_, hv⟩, ?_⟩
      change f k l hkl (f j k hjk v) * f i l _ a = 0
      rw [← hG.map_map hik hkl a, ← map_mul, hl]
    rw [← Ring.DirectLimit.of_f (hik.trans hkl), hloc, map_zero]
  · intro y
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    obtain ⟨i, x, hx⟩ := hsurj r
    obtain ⟨j, w, hw⟩ := hsurj s
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hs : f j k hjk w ∈ (P k).primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hP, Ideal.mem_comap, hg, hw]
      exact Ideal.mem_primeCompl_iff.mp s.2
    refine ⟨Ring.DirectLimit.of _ _ k (IsLocalization.mk' _ (f i k hik x) ⟨_, hs⟩), ?_⟩
    rw [Ring.DirectLimit.lift_of, locι, Localization.localRingHom_mk']
    congr 1
    · rw [hg, hx]
    · exact Subtype.ext (show g k (f j k hjk w) = s by rw [hg, hw])

end LocalizedSystem

section Inclusion

variable {R C κ : Type*} [CommRing R] [CommRing C] [Algebra R C]

theorem algebraMap_inclusion {S T : Subalgebra R C} (h : S ≤ T) (x : S) :
    algebraMap T C (Subalgebra.inclusion h x) = algebraMap S C x :=
  rfl

theorem directedSystem_inclusion [Preorder κ] (S : κ → Subalgebra R C) (hS : Monotone S) :
    DirectedSystem (fun i ↦ S i) fun _ _ h ↦ (Subalgebra.inclusion (hS h)).toRingHom where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

end Inclusion

section PushoutLocalization

variable {R S R' S' Rp Sq Rp' Sq' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [CommRing Rp] [CommRing Sq] [CommRing Rp'] [CommRing Sq'] [IsLocalRing Sq']
  [Algebra R S] [Algebra R R'] [Algebra R Rp] [Algebra Rp Sq] [Algebra Rp Rp']
  [Algebra S Sq] [Algebra R' Rp'] [Algebra S' Sq']

/-- Let `E : S ⊗[R] R' ≃ S'` identify `S'` with a pushout, and let `S_M`, `R'_N` and `S'_M'` be
localizations of `S`, `R'` and `S'` compatible with ring maps `R_p → S_M` and `R_p → R'_N` over
`R`, where `M` and `N` map into `M'`. Then any map `S_M ⊗[R_p] R'_N → S'_M'` given on pure
tensors by the induced maps makes the local ring `S'_M'` the localization of `S_M ⊗[R_p] R'_N`
at the prime under its maximal ideal. -/
theorem isLocalization_tensor_of_isPushout (M : Submonoid S) [IsLocalization M Sq]
    (N : Submonoid R') [IsLocalization N Rp'] (M' : Submonoid S') [IsLocalization M' Sq']
    (α : S →+* S') (β : R' →+* S') (E : S ⊗[R] R' ≃+* S') (hE : ∀ x c, E (x ⊗ₜ c) = α x * β c)
    (hM : ∀ s ∈ M, α s ∈ M') (hN : ∀ d ∈ N, β d ∈ M')
    (HS : (algebraMap S Sq).comp (algebraMap R S) = (algebraMap Rp Sq).comp (algebraMap R Rp))
    (HT : (algebraMap R' Rp').comp (algebraMap R R') = (algebraMap Rp Rp').comp (algebraMap R Rp))
    (f : Sq ⊗[Rp] Rp' →+* Sq') (μ : Sq →+* Sq') (ν : Rp' →+* Sq')
    (hf : ∀ s r, f (s ⊗ₜ r) = μ s * ν r)
    (hμ : ∀ x, μ (algebraMap S Sq x) = algebraMap S' Sq' (α x))
    (hν : ∀ c, ν (algebraMap R' Rp' c) = algebraMap S' Sq' (β c)) :
    letI := f.toAlgebra
    IsLocalization.AtPrime Sq' ((IsLocalRing.maximalIdeal Sq').comap f) := by
  let _ := f.toAlgebra
  let ψ : S ⊗[R] R' →+* Sq ⊗[Rp] Rp' := Algebra.TensorProduct.mapRingHom _ _ _ HS HT
  have hψ (x c) : ψ (x ⊗ₜ c) = algebraMap S Sq x ⊗ₜ algebraMap R' Rp' c :=
    Algebra.TensorProduct.mapRingHom_tmul _ _ _ HS HT x c
  let φ : S' →+* Sq ⊗[Rp] Rp' := ψ.comp E.symm.toRingHom
  have hφ (z) : φ (E z) = ψ z := congrArg ψ (E.symm_apply_apply z)
  have K1 (m : S') : f (φ m) = algebraMap S' Sq' m := by
    obtain ⟨z, rfl⟩ := E.surjective m
    rw [hφ]
    induction z with
    | tmul x c => rw [hψ, hf, hμ, hν, hE, map_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have K2 (a : Sq ⊗[Rp] Rp') : ∃ y w, w ∈ M' ∧ a * φ w = φ y := by
    induction a with
    | tmul x c =>
      obtain ⟨⟨x₀, s₀⟩, rfl⟩ := IsLocalization.mk'_surjective M x
      obtain ⟨⟨c₀, d₀⟩, rfl⟩ := IsLocalization.mk'_surjective N c
      refine ⟨E (x₀ ⊗ₜ c₀), E ((s₀ : S) ⊗ₜ (d₀ : R')), ?_, ?_⟩
      · rw [hE]
        exact mul_mem (hM _ s₀.2) (hN _ d₀.2)
      · rw [hφ, hφ, hψ, hψ, Algebra.TensorProduct.tmul_mul_tmul, IsLocalization.mk'_spec,
          IsLocalization.mk'_spec]
    | add a₁ a₂ h₁ h₂ =>
      obtain ⟨y₁, w₁, hw₁, e₁⟩ := h₁
      obtain ⟨y₂, w₂, hw₂, e₂⟩ := h₂
      refine ⟨y₁ * w₂ + y₂ * w₁, w₁ * w₂, mul_mem hw₁ hw₂, ?_⟩
      rw [map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
      ring
  refine isLocalization_atPrime_of_fractions (fun b ↦ ?_) (fun a ha ↦ ?_)
  · obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalization.mk'_surjective M' b
    refine ⟨φ m, φ s, ?_, ?_⟩
    · rw [RingHom.algebraMap_toAlgebra, K1]
      exact IsLocalization.map_units _ s
    · rw [RingHom.algebraMap_toAlgebra, K1, K1, IsLocalization.mk'_spec]
  · rw [RingHom.algebraMap_toAlgebra] at ha
    obtain ⟨y, w, hw, e⟩ := K2 a
    have hy : algebraMap S' Sq' y = 0 := by
      rw [← K1, ← e, map_mul, ha, zero_mul]
    obtain ⟨⟨c, hc⟩, hcy⟩ := (IsLocalization.map_eq_zero_iff M' _ _).mp hy
    refine ⟨φ (c * w), ?_, ?_⟩
    · rw [RingHom.algebraMap_toAlgebra, K1]
      exact IsLocalization.map_units Sq' (⟨c * w, mul_mem hc hw⟩ : M')
    · rw [map_mul, mul_assoc, mul_comm (φ w), e, ← map_mul]
      change φ (c * y) = 0
      rw [hcy, map_zero]

end PushoutLocalization

section Stage

variable {A B ι σ : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (P : Algebra.Presentation A B ι σ) (Q : Ideal B) [Q.IsPrime]

/-- The prime of the base ring of the stage `t` under `Q`. -/
noncomputable abbrev basePrime (t : Finset A) : Ideal (base P t) :=
  (Q.under A).comap (algebraMap (base P t) A)

/-- The prime of the model of the stage `t` under `Q`. -/
noncomputable abbrev modelPrime (t : Finset A) : Ideal (model P t) :=
  Q.comap (toB P t).toRingHom

omit [Q.IsPrime] in
theorem modelPrime_eq (t : Finset A) : modelPrime P Q t = Q.comap (toB P t) := by
  rw [modelPrime, AlgHom.toRingHom_eq_coe, Ideal.comap_coe]

instance (t : Finset A) : (modelPrime P Q t).LiesOver (basePrime P Q t) where
  over := by
    ext x
    change algebraMap A B (x : A) ∈ Q ↔ toB P t (algebraMap _ _ x) ∈ Q
    rw [AlgHom.commutes]
    exact Iff.rfl

/-- The localized base ring of the stage `t`. -/
noncomputable abbrev baseLoc (t : Finset A) : Type _ := Localization.AtPrime (basePrime P Q t)

/-- The localized model of the stage `t`. -/
noncomputable abbrev modelLoc (t : Finset A) : Type _ := Localization.AtPrime (modelPrime P Q t)

noncomputable instance (t : Finset A) : Algebra (baseLoc P Q t) (modelLoc P Q t) :=
  Localization.AtPrime.algebraOfLiesOver (basePrime P Q t) (modelPrime P Q t)

instance (t : Finset A) : IsLocalHom (algebraMap (baseLoc P Q t) (modelLoc P Q t)) :=
  Localization.isLocalHom_localRingHom _ _ _ _

instance (t : Finset A) : IsScalarTower (base P t) (baseLoc P Q t) (modelLoc P Q t) :=
  .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (base P t) (model P t) (modelLoc P Q t)]
    exact (Localization.localRingHom_to_map (basePrime P Q t) (modelPrime P Q t)
      (algebraMap (base P t) (model P t)) _ x).symm

/-- The inclusions of the stage base rings, as ring maps. -/
noncomputable abbrev baseIncl {t t' : Finset A} (h : t ≤ t') : base P t →+* base P t' :=
  (Subalgebra.inclusion (base_mono P h)).toRingHom

theorem algebraMap_baseIncl {t t' : Finset A} (h : t ≤ t') (x : base P t) :
    algebraMap (base P t') A (baseIncl P h x) = algebraMap (base P t) A x :=
  algebraMap_inclusion (base_mono P h) x

instance : DirectedSystem (fun t : Finset A ↦ base P t) fun _ _ h ↦ baseIncl P h :=
  directedSystem_inclusion (base P) fun _ _ h ↦ base_mono P h

instance : DirectedSystem (fun t : Finset A ↦ model P t) fun _ _ h ↦ trans P h where
  map_self := by intro _ x; exact trans_refl x
  map_map := by intro _ _ _ h₁ h₂ x; exact trans_trans h₁ h₂ x

theorem toB_trans' {t t' : Finset A} (h : t ≤ t') (x : model P t) :
    (toB P t').toRingHom (trans P h x) = (toB P t).toRingHom x :=
  toB_trans h x

/-- The transition maps of the localized stage base rings. -/
noncomputable abbrev baseLocMap {t t' : Finset A} (h : t ≤ t') :
    baseLoc P Q t →+* baseLoc P Q t' :=
  locMap (fun _ _ h ↦ baseIncl P h) (fun t ↦ algebraMap (base P t) A)
    (fun _ _ h x ↦ algebraMap_baseIncl P h x) (Q.under A) (basePrime P Q) (fun _ ↦ rfl) t t' h

/-- The transition maps of the localized stage models. -/
noncomputable abbrev modelLocMap {t t' : Finset A} (h : t ≤ t') :
    modelLoc P Q t →+* modelLoc P Q t' :=
  locMap (fun _ _ h ↦ trans P h) (fun t ↦ (toB P t).toRingHom) (fun _ _ h x ↦ toB_trans' P h x)
    Q (modelPrime P Q) (fun _ ↦ rfl) t t' h

/-- The maps from the localized stage base rings to `A_p`. -/
noncomputable abbrev baseLocι (t : Finset A) :
    baseLoc P Q t →+* Localization.AtPrime (Q.under A) :=
  locι (fun t ↦ algebraMap (base P t) A) (Q.under A) (basePrime P Q) (fun _ ↦ rfl) t

/-- The maps from the localized stage models to `B_Q`. -/
noncomputable abbrev modelLocι (t : Finset A) : modelLoc P Q t →+* Localization.AtPrime Q :=
  locι (fun t ↦ (toB P t).toRingHom) Q (modelPrime P Q) (fun _ ↦ rfl) t

theorem baseLocMap_algebraMap {t t' : Finset A} (h : t ≤ t') (x : base P t) :
    baseLocMap P Q h (algebraMap (base P t) (baseLoc P Q t) x) =
      algebraMap (base P t') (baseLoc P Q t') (baseIncl P h x) :=
  Localization.localRingHom_to_map _ _ _ _ x

theorem modelLocMap_algebraMap {t t' : Finset A} (h : t ≤ t') (x : model P t) :
    modelLocMap P Q h (algebraMap (model P t) (modelLoc P Q t) x) =
      algebraMap (model P t') (modelLoc P Q t') (trans P h x) :=
  Localization.localRingHom_to_map _ _ _ _ x

theorem baseLocι_algebraMap (t : Finset A) (x : base P t) :
    baseLocι P Q t (algebraMap (base P t) (baseLoc P Q t) x) =
      algebraMap A (Localization.AtPrime (Q.under A)) (algebraMap (base P t) A x) :=
  Localization.localRingHom_to_map _ _ _ _ x

theorem modelLocι_algebraMap (t : Finset A) (x : model P t) :
    modelLocι P Q t (algebraMap (model P t) (modelLoc P Q t) x) =
      algebraMap B (Localization.AtPrime Q) (toB P t x) :=
  Localization.localRingHom_to_map _ _ _ _ x

/-- `B_Q` as an algebra over `A_p`, where `p` is the prime of `A` under `Q`. -/
@[reducible] noncomputable def localAlgebra :
    Algebra (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q) :=
  Localization.AtPrime.algebraOfLiesOver (Q.under A) Q

attribute [local instance] localAlgebra

instance : IsLocalHom (algebraMap (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q)) :=
  Localization.isLocalHom_localRingHom _ _ _ _

instance : IsScalarTower A (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q) :=
  .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q)]
    exact (Localization.localRingHom_to_map (Q.under A) Q (algebraMap A B) _ x).symm

theorem map_comm_stage {t t' : Finset A} (h : t ≤ t') (r : baseLoc P Q t) :
    modelLocMap P Q h (algebraMap (baseLoc P Q t) (modelLoc P Q t) r) =
      algebraMap (baseLoc P Q t') (modelLoc P Q t') (baseLocMap P Q h r) := by
  let φ₁ := (modelLocMap P Q h).comp (algebraMap (baseLoc P Q t) (modelLoc P Q t))
  let φ₂ := (algebraMap (baseLoc P Q t') (modelLoc P Q t')).comp (baseLocMap P Q h)
  have : φ₁ = φ₂ := IsLocalization.ringHom_ext (basePrime P Q t).primeCompl <|
    RingHom.ext fun x ↦ by
      simp only [φ₁, φ₂, RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply (base P t) (baseLoc P Q t) (modelLoc P Q t),
        IsScalarTower.algebraMap_apply (base P t) (model P t) (modelLoc P Q t),
        modelLocMap_algebraMap, baseLocMap_algebraMap,
        ← IsScalarTower.algebraMap_apply (base P t') (baseLoc P Q t') (modelLoc P Q t'),
        IsScalarTower.algebraMap_apply (base P t') (model P t') (modelLoc P Q t')]
      exact congrArg (algebraMap (model P t') (modelLoc P Q t')) (trans_algebraMap h x)
  exact DFunLike.congr_fun this r

theorem ι_comm_stage (t : Finset A) (r : baseLoc P Q t) :
    modelLocι P Q t (algebraMap (baseLoc P Q t) (modelLoc P Q t) r) =
      algebraMap (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q)
        (baseLocι P Q t r) := by
  let φ₁ := (modelLocι P Q t).comp (algebraMap (baseLoc P Q t) (modelLoc P Q t))
  let φ₂ := (algebraMap (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q)).comp
    (baseLocι P Q t)
  have : φ₁ = φ₂ := IsLocalization.ringHom_ext (basePrime P Q t).primeCompl <|
    RingHom.ext fun x ↦ by
      simp only [φ₁, φ₂, RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply (base P t) (baseLoc P Q t) (modelLoc P Q t),
        IsScalarTower.algebraMap_apply (base P t) (model P t) (modelLoc P Q t),
        modelLocι_algebraMap, baseLocι_algebraMap,
        ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Q.under A))
          (Localization.AtPrime Q), AlgHom.commutes,
        IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q)]
      rfl
  exact DFunLike.congr_fun this r

/-- The local algebra system of the stages, localized at the primes under `Q`. -/
noncomputable def stageSystem :
    LocalAlgebraSystem (Finset A) (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q) where
  base t := baseLoc P Q t
  alg t := modelLoc P Q t
  structure_local _ := inferInstance
  baseMap _ _ h := baseLocMap P Q h
  algMap _ _ h := modelLocMap P Q h
  base_directed := directedSystem_locMap _ _ _ _ _ _
  alg_directed := directedSystem_locMap _ _ _ _ _ _
  baseMap_local _ _ _ := Localization.isLocalHom_localRingHom _ _ _ _
  algMap_local _ _ _ := Localization.isLocalHom_localRingHom _ _ _ _
  map_comm _ _ h r := map_comm_stage P Q h r
  baseι t := baseLocι P Q t
  algι t := modelLocι P Q t
  baseι_local _ := Localization.isLocalHom_localRingHom _ _ _ _
  algι_local _ := Localization.isLocalHom_localRingHom _ _ _ _
  baseι_compat := locι_locMap _ _ _ _ _ _
  algι_compat := locι_locMap _ _ _ _ _ _
  ι_comm t r := ι_comm_stage P Q t r

theorem stageSystem_isColimit [Finite σ] : (stageSystem P Q).IsColimit := by
  refine ⟨bijective_lift_locι (fun _ _ h ↦ baseIncl P h) (fun t ↦ algebraMap (base P t) A)
    (fun _ _ h x ↦ algebraMap_baseIncl P h x) (Q.under A) (basePrime P Q) (fun _ ↦ rfl) ?_ ?_,
    bijective_lift_locι (fun _ _ h ↦ trans P h) (fun t ↦ (toB P t).toRingHom)
    (fun _ _ h x ↦ toB_trans' P h x) Q (modelPrime P Q) (fun _ ↦ rfl) ?_ ?_⟩
  · intro a
    exact ⟨{a}, ⟨a, mem_base_of_mem P (Finset.mem_singleton_self a)⟩, rfl⟩
  · intro t x hx
    exact ⟨t, le_rfl, Subtype.ext hx⟩
  · intro b
    obtain ⟨t, -, x, hx⟩ := exists_lift P ∅ b
    exact ⟨t, x, hx⟩
  · intro t x hx
    exact exists_trans_eq_zero P x hx

/-- The tensor transition map of the localized stages. -/
noncomputable def rbc {t t' : Finset A} (h : t ≤ t') :
    letI : Algebra (baseLoc P Q t) (baseLoc P Q t') := (baseLocMap P Q h).toAlgebra
    modelLoc P Q t ⊗[baseLoc P Q t] baseLoc P Q t' →+* modelLoc P Q t' :=
  (stageSystem P Q).ringBaseChangeMap h

theorem rbc_tmul {t t' : Finset A} (h : t ≤ t') (s : modelLoc P Q t) (r : baseLoc P Q t') :
    letI : Algebra (baseLoc P Q t) (baseLoc P Q t') := (baseLocMap P Q h).toAlgebra
    rbc P Q h (s ⊗ₜ r) = modelLocMap P Q h s * algebraMap (baseLoc P Q t') (modelLoc P Q t') r :=
  rfl

/-- The tensor transition of the localized stages is a localization at a prime. -/
theorem isLocalization_rbc {t t' : Finset A} (h : t ≤ t') :
    letI : Algebra (baseLoc P Q t) (baseLoc P Q t') := (baseLocMap P Q h).toAlgebra
    letI : Algebra (modelLoc P Q t ⊗[baseLoc P Q t] baseLoc P Q t') (modelLoc P Q t') :=
      (rbc P Q h).toAlgebra
    IsLocalization.AtPrime (modelLoc P Q t')
      ((IsLocalRing.maximalIdeal (modelLoc P Q t')).comap (rbc P Q h)) := by
  let _ : Algebra (baseLoc P Q t) (baseLoc P Q t') := (baseLocMap P Q h).toAlgebra
  let _ := baseAlgebra P h
  let _ := modelAlgebra P h
  have _ := isScalarTower_model P h
  have _ := isPushout P h
  obtain ⟨E, hE⟩ : ∃ E : model P t ⊗[base P t] base P t' ≃+* model P t',
      ∀ x c, E (x ⊗ₜ c) = trans P h x * algebraMap (base P t') (model P t') c :=
    ⟨(Algebra.IsPushout.equiv (base P t) (model P t) (base P t') (model P t')).toRingEquiv,
      fun x c ↦ Algebra.IsPushout.equiv_tmul _ _ _ _ x c⟩
  have hM (s : model P t) (hs : s ∈ (modelPrime P Q t).primeCompl) :
      trans P h s ∈ (modelPrime P Q t').primeCompl := by
    rw [Ideal.mem_primeCompl_iff] at hs ⊢
    intro hs'
    apply hs
    change toB P t' (trans P h s) ∈ Q at hs'
    rwa [toB_trans] at hs'
  have hN (d : base P t') (hd : d ∈ (basePrime P Q t').primeCompl) :
      algebraMap (base P t') (model P t') d ∈ (modelPrime P Q t').primeCompl := by
    rw [Ideal.mem_primeCompl_iff] at hd ⊢
    intro hd'
    apply hd
    change toB P t' (algebraMap _ _ d) ∈ Q at hd'
    rw [AlgHom.commutes] at hd'
    exact hd'
  have HS : (algebraMap (model P t) (modelLoc P Q t)).comp (algebraMap (base P t) (model P t)) =
      (algebraMap (baseLoc P Q t) (modelLoc P Q t)).comp
        (algebraMap (base P t) (baseLoc P Q t)) :=
    RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  have HT : (algebraMap (base P t') (baseLoc P Q t')).comp (algebraMap (base P t) (base P t')) =
      (algebraMap (baseLoc P Q t) (baseLoc P Q t')).comp
        (algebraMap (base P t) (baseLoc P Q t)) :=
    RingHom.ext fun x ↦ (baseLocMap_algebraMap P Q h x).symm
  have hν (c : base P t') :
      algebraMap (baseLoc P Q t') (modelLoc P Q t') (algebraMap (base P t') (baseLoc P Q t') c) =
        algebraMap (model P t') (modelLoc P Q t') (algebraMap (base P t') (model P t') c) := by
    rw [← IsScalarTower.algebraMap_apply (base P t') (baseLoc P Q t') (modelLoc P Q t'),
      IsScalarTower.algebraMap_apply (base P t') (model P t') (modelLoc P Q t')]
  have key := isLocalization_tensor_of_isPushout (R := base P t) (S := model P t) (R' := base P t')
    (S' := model P t') (Rp := baseLoc P Q t) (Sq := modelLoc P Q t) (Rp' := baseLoc P Q t')
    (Sq' := modelLoc P Q t') (modelPrime P Q t).primeCompl (basePrime P Q t').primeCompl
    (modelPrime P Q t').primeCompl (trans P h) (algebraMap (base P t') (model P t')) E hE hM hN
    HS HT (rbc P Q h) (modelLocMap P Q h) (algebraMap (baseLoc P Q t') (modelLoc P Q t'))
    (rbc_tmul P Q h) (modelLocMap_algebraMap P Q h) hν
  convert key using 1

theorem stageSystem_isPrimeLocalization {t t' : Finset A} (h : t ≤ t') :
    (stageSystem P Q).IsPrimeLocalization h :=
  ⟨_, Ideal.comap_isPrime _ _, isLocalization_rbc P Q h⟩

theorem essFiniteType_int_of_subsingleton {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.EssFiniteType ℤ X _ _ i₁) : @Algebra.EssFiniteType ℤ X _ _ i₂ := by
  obtain rfl := Subsingleton.elim i₁ i₂
  exact h

theorem stageSystem_isApproximation [Finite ι] [Finite σ] :
    (stageSystem P Q).IsApproximation := by
  refine ⟨stageSystem_isColimit P Q, fun t ↦ ?_, fun t ↦ ?_,
    fun _ _ h ↦ stageSystem_isPrimeLocalization P Q h⟩
  · have := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := base P t) (A := baseLoc P Q t)
      fun _ ↦ by simp
    have : Algebra.EssFiniteType (base P t) (baseLoc P Q t) :=
      .of_isLocalization _ (basePrime P Q t).primeCompl
    exact essFiniteType_int_of_subsingleton _ _
      (Algebra.EssFiniteType.comp ℤ (base P t) (baseLoc P Q t))
  · exact Algebra.EssFiniteType.of_comp (base P t) (baseLoc P Q t) (modelLoc P Q t)

/-- **Flatness at a finite stage.** If `B` is flat over `A` and `Q` is a prime of `B`, then
for some finite stage `t` the localization of the stage model at the prime under `Q` is flat
over the stage base ring. -/
theorem exists_flat_stage [Finite ι] [Finite σ] [Module.Flat A B] :
    ∃ t, Module.Flat (base P t) (Localization.AtPrime (Q.comap (toB P t))) := by
  have := P.finitePresentation_of_isFinite
  have hess : EssFinitePresentation (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q) := by
    have h₁ : EssFinitePresentation A (Localization.AtPrime (Q.under A)) :=
      essFinitePresentation_of_isLocalization A A _ (Q.under A).primeCompl
    have h₂ : EssFinitePresentation A (Localization.AtPrime Q) :=
      essFinitePresentation_of_isLocalization A B _ Q.primeCompl
    exact essFinitePresentationTowerCancellation A _ _ h₁ h₂
  have hE := (stageSystem P Q).regularModuleSystem_isApproximation
    (stageSystem_isApproximation P Q)
  obtain ⟨t, ht⟩ := localApproximationFlatnessDescent (Finset A) _ _ _ (stageSystem P Q)
    (stageSystem P Q).regularModuleSystem hess inferInstance hE
    (by exact (inferInstance :
      Module.Flat (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q)))
  refine ⟨t, ?_⟩
  have : Module.Flat (baseLoc P Q t) (modelLoc P Q t) := ht
  have : Module.Flat (base P t) (modelLoc P Q t) :=
    Module.Flat.trans (base P t) (baseLoc P Q t) (modelLoc P Q t)
  exact this

end Stage

end Langlands.Algebra.FinitePresentationStages
