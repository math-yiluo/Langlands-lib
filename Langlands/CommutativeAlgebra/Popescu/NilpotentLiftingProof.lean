import Langlands.MathlibBase
import Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingStatement
import Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractStatement
import Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractProof

/-! # Proof of Stacks 07CM: lifting smooth factorizations along a nilpotent ideal -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.NilpotentLifting

open MvPolynomial

section SmoothLift

variable {R : Type u} [CommRing R] (I : Ideal R)

lemma aeval_map_mk {S : Type*} [CommRing S] [Algebra (R ⧸ I) S] [Algebra R S]
    [IsScalarTower R (R ⧸ I) S] {ι : Type*} (x : ι → S) (p : MvPolynomial ι R) :
    aeval x (MvPolynomial.map (Ideal.Quotient.mk I) p) = aeval x p := by
  rw [← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]

/-- A submersive presentation over `R ⧸ I` lifts to a smooth `R`-algebra mapping onto the
presented algebra with kernel inside `I B`. -/
theorem exists_smooth_lift_of_presentation {S : Type u} [CommRing S] [Algebra (R ⧸ I) S]
    [Algebra R S] [IsScalarTower R (R ⧸ I) S] {ι σ : Type} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) S ι σ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.Smooth R B ∧
      ∃ π : B →ₐ[R] S, Function.Surjective π ∧ RingHom.ker π ≤ I.map (algebraMap R B) := by
  classical
  cases nonempty_fintype σ
  have hsurj : Function.Surjective (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk I)) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose v hv using fun j : σ ↦ hsurj (P.relation j)
  let P₀ := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  let K := Ideal.span (Set.range v)
  let d : MvPolynomial ι R ⧸ K := P₀.jacobian
  let Q := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  let PB : Algebra.SubmersivePresentation R (Localization.Away d) (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.comp P₀
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmooth R (Localization.Away d) := PB.isStandardSmooth
  -- the map `B₀ → S`
  have hK : K ≤ RingHom.ker (aeval (R := R) P.val) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rw [← aeval_map_mk I, hv]
    exact P.aeval_val_relation j
  let π₀ : (MvPolynomial ι R ⧸ K) →ₐ[R] S := Ideal.Quotient.liftₐ K (aeval P.val)
    fun a ha ↦ hK ha
  have hπ₀ : ∀ p, π₀ (Ideal.Quotient.mk K p) = aeval P.val p := fun _ ↦ rfl
  have hπ₀d : π₀ d = P.jacobian := by
    show π₀ P₀.jacobian = P.jacobian
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change π₀ (Ideal.Quotient.mk K _) = _
    rw [hπ₀, Algebra.Generators.algebraMap_apply]
    rw [← aeval_map_mk I, RingHom.map_det]
    congr 2
    ext i j : 1
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rw [← pderiv_map]
    change pderiv (P.map i) (MvPolynomial.map (Ideal.Quotient.mk I) (v j)) = _
    rw [hv]
  have hunit : ∀ y : Submonoid.powers d, IsUnit (π₀ y) := by
    rintro ⟨_, k, rfl⟩
    simp only [map_pow, hπ₀d]
    exact P.jacobian_isUnit.pow k
  let π : Localization.Away d →ₐ[R] S :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π₀) hunit
  have hπ : ∀ x, π (algebraMap _ _ x) = π₀ x := fun x ↦
    IsLocalization.lift_eq (M := Submonoid.powers d) hunit x
  refine ⟨Localization.Away d, inferInstance, inferInstance, inferInstance, π, ?_, ?_⟩
  · intro s
    obtain ⟨p, hp⟩ := P.algebraMap_surjective s
    obtain ⟨q, rfl⟩ := hsurj p
    refine ⟨algebraMap _ _ (Ideal.Quotient.mk K q), ?_⟩
    rw [hπ, hπ₀, ← aeval_map_mk I, ← hp, Algebra.Generators.algebraMap_apply]
  · intro b hb
    rw [RingHom.mem_ker] at hb
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers d) b
    dsimp only at hb ⊢
    have hx : π₀ x = 0 := by
      have h1 : π (IsLocalization.mk' (Localization.Away d) x y) * π₀ y = π₀ x := by
        rw [← hπ, ← hπ, ← map_mul, IsLocalization.mk'_spec]
      rw [← h1]
      change π (IsLocalization.mk' (Localization.Away d) x y) * _ = 0
      rw [hb, zero_mul]
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπ₀] at hx
    have h2 : MvPolynomial.map (Ideal.Quotient.mk I) p ∈ K.map (MvPolynomial.map (Ideal.Quotient.mk I)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      have : (MvPolynomial.map (Ideal.Quotient.mk I) ∘ v) = P.relation := funext hv
      rw [this, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val,
        RingHom.mem_ker, aeval_map_mk I]
      exact hx
    obtain ⟨q, hq, hpq⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h2
    have h3 : p - q ∈ Ideal.map (C : R →+* MvPolynomial ι R) I := by
      have : p - q ∈ RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk I)) := by
        rw [RingHom.mem_ker, map_sub, hpq, sub_self]
      rwa [MvPolynomial.ker_map, Ideal.mk_ker] at this
    have h4 : Ideal.Quotient.mk K p ∈ I.map (algebraMap R (MvPolynomial ι R ⧸ K)) := by
      have : Ideal.Quotient.mk K p = Ideal.Quotient.mk K (p - q) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
      rw [this]
      have h5 := Ideal.mem_map_of_mem (Ideal.Quotient.mk K) h3
      rwa [Ideal.map_map] at h5
    have h6 := Ideal.mem_map_of_mem (algebraMap (MvPolynomial ι R ⧸ K) (Localization.Away d)) h4
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h6
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h6

end SmoothLift

section Nakayama

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Nakayama's lemma for a nilpotent ideal: an algebra map that is surjective modulo `I`
is surjective. -/
theorem surjective_of_surjective_mod {B T : Type*} [CommRing B] [CommRing T] [Algebra R B]
    [Algebra R T] (hI : IsNilpotent I) (f : B →ₐ[R] T)
    (hf : ∀ t : T, ∃ b : B, t - f b ∈ I.map (algebraMap R T)) :
    Function.Surjective f := by
  let N : Submodule R T := LinearMap.range f.toLinearMap
  have h1 : (⊤ : Submodule R T) ≤ N ⊔ I • ⊤ := by
    intro t _
    obtain ⟨b, hb⟩ := hf t
    have hb' : t - f b ∈ I • (⊤ : Submodule R T) := by
      rw [Ideal.smul_top_eq_map]
      exact hb
    have := Submodule.add_mem_sup (show f b ∈ N from ⟨b, rfl⟩) hb'
    rwa [add_sub_cancel] at this
  have h2 : ∀ n : ℕ, (⊤ : Submodule R T) ≤ N ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ n ih =>
      calc (⊤ : Submodule R T) ≤ N ⊔ I ^ n • ⊤ := ih
        _ ≤ N ⊔ I ^ n • (N ⊔ I • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (I ^ n • N ⊔ I ^ (n + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (n + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  obtain ⟨n, hn⟩ := hI
  have := h2 n
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  intro t
  obtain ⟨b, hb⟩ := this (Submodule.mem_top (x := t))
  exact ⟨b, hb⟩

end Nakayama

section Cover

variable {R : Type u} [CommRing R] (I : Ideal R)

lemma exists_sum_of_mem_map {S : Type*} [CommRing S] [Algebra R S] {x : S}
    (hx : x ∈ I.map (algebraMap R S)) :
    ∃ (N : ℕ) (ε : Fin N → R) (s : Fin N → S), (∀ l, ε l ∈ I) ∧ x = ∑ l, ε l • s l := by
  obtain ⟨N, a, b, hab⟩ := Submodule.mem_span_set'.mp hx
  choose ε hε hεb using fun l ↦ (b l).2
  refine ⟨N, ε, a, hε, ?_⟩
  rw [← hab]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [smul_eq_mul, ← hεb l, Algebra.smul_def, mul_comm]

/-- A smooth `R`-algebra covers any `R`-algebra whose reduction modulo the nilpotent ideal `I`
is standard smooth, with kernel inside `I B`. -/
theorem exists_smooth_cover (hI : IsNilpotent I) {A : Type u} [CommRing A] [Algebra R A]
    [hA : Algebra.IsStandardSmooth (R ⧸ I) (A ⧸ I.map (algebraMap R A))] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.Smooth R B ∧
      ∃ θ : B →ₐ[R] A, Function.Surjective θ ∧ RingHom.ker θ ≤ I.map (algebraMap R B) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hA.out
  obtain ⟨B, _, _, hB, π, hπ, hπker⟩ := exists_smooth_lift_of_presentation I P
  have hnil : IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ R (I.map (algebraMap R A)))) := by
    rw [show RingHom.ker (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) =
      I.map (algebraMap R A) from Ideal.Quotient.mkₐ_ker R _]
    obtain ⟨k, hk⟩ := hI
    exact ⟨k, by rw [← Ideal.map_pow, hk, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  let θ : B →ₐ[R] A := Algebra.FormallySmooth.liftOfSurjective π
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) Ideal.Quotient.mk_surjective hnil
  have hθ : ∀ b, Ideal.Quotient.mk (I.map (algebraMap R A)) (θ b) = π b := fun b ↦ by
    have := Algebra.FormallySmooth.liftOfSurjective_apply π
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) Ideal.Quotient.mk_surjective hnil b
    rwa [Ideal.Quotient.mkₐ_eq_mk] at this
  refine ⟨B, inferInstance, inferInstance, hB, θ, ?_, ?_⟩
  · apply surjective_of_surjective_mod I hI θ
    intro a
    obtain ⟨b, hb⟩ := hπ (Ideal.Quotient.mk _ a)
    refine ⟨b, ?_⟩
    rw [← Ideal.Quotient.eq, hθ, hb]
  · intro b hb
    apply hπker
    rw [RingHom.mem_ker, ← hθ, (RingHom.mem_ker).mp hb, map_zero]

/-- The reduction modulo `I` of `C[t, d] / (rel)`, where each `rel i` agrees modulo `I` with a
lift `g i` of a relation of a presentation `Bb = (C ⧸ I C)[t] / (ḡ)`, is `Bb[d]`. -/
theorem nonempty_algEquiv_reduction {C : Type u} [CommRing C] [Algebra R C]
    {Bb : Type u} [CommRing Bb] [Algebra (R ⧸ I) Bb] [Algebra (C ⧸ I.map (algebraMap R C)) Bb]
    [IsScalarTower (R ⧸ I) (C ⧸ I.map (algebraMap R C)) Bb] {n m : ℕ}
    (f : MvPolynomial (Fin n) (C ⧸ I.map (algebraMap R C)) →ₐ[C ⧸ I.map (algebraMap R C)] Bb)
    (hf : Function.Surjective f) (g : Fin m → MvPolynomial (Fin n) C)
    (hg : RingHom.ker f.toRingHom ≤ Ideal.span (Set.range fun i ↦
      MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)))
    (hg' : ∀ i, f (MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)) = 0)
    {D : Type} {A' : Type u} [CommRing A'] [Algebra R A']
    (p : MvPolynomial (Fin n ⊕ D) C →ₐ[R] A') (hp : Function.Surjective p)
    (rel : Fin m → MvPolynomial (Fin n ⊕ D) C) (hker : RingHom.ker p = Ideal.span (Set.range rel))
    (hrel : ∀ i, rename Sum.inl (g i) - rel i ∈
      I.map (algebraMap R (MvPolynomial (Fin n ⊕ D) C))) :
    Nonempty (MvPolynomial D Bb ≃ₐ[R ⧸ I] A' ⧸ I.map (algebraMap R A')) := by
  classical
  let mkC := Ideal.Quotient.mk (I.map (algebraMap R C))
  let mkA := Ideal.Quotient.mk (I.map (algebraMap R A'))
  have hfC : ∀ x, f (MvPolynomial.C x) = algebraMap _ Bb x := fun x ↦ f.commutes x
  -- the map `μ : A' ⧸ I A' → Bb[d]`
  let μ₀ : MvPolynomial (Fin n ⊕ D) C →+* MvPolynomial D Bb :=
    eval₂Hom (MvPolynomial.C.comp ((algebraMap (C ⧸ I.map (algebraMap R C)) Bb).comp mkC))
      (Sum.elim (fun k ↦ MvPolynomial.C (f (X k))) X)
  have hμ₀C : ∀ c, μ₀ (MvPolynomial.C c) =
      MvPolynomial.C (algebraMap (C ⧸ I.map (algebraMap R C)) Bb (mkC c)) := fun c ↦
    eval₂Hom_C _ _ _
  have hμ₀l : ∀ k, μ₀ (X (Sum.inl k)) = MvPolynomial.C (f (X k)) := fun k ↦ eval₂Hom_X' _ _ _
  have hμ₀r : ∀ d, μ₀ (X (Sum.inr d)) = X d := fun d ↦ eval₂Hom_X' _ _ _
  have hμ₀ren : ∀ q, μ₀ (rename Sum.inl q) =
      MvPolynomial.C (f (MvPolynomial.map mkC q)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [rename_C, hμ₀C, MvPolynomial.map_C, hfC]
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X q k hq => simp only [map_mul, hq, rename_X, hμ₀l, MvPolynomial.map_X]
  have hμ₀I : I.map (algebraMap R (MvPolynomial (Fin n ⊕ D) C)) ≤ RingHom.ker μ₀ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.algebraMap_apply, hμ₀C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr), map_zero, map_zero]
  have hkerμ₀ : RingHom.ker p ≤ RingHom.ker μ₀ := by
    rw [hker, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 := (RingHom.mem_ker).mp (hμ₀I (hrel i))
    rw [map_sub, hμ₀ren, hg', map_zero, zero_sub, neg_eq_zero] at h1
    exact h1
  let μ₁ : A' →+* MvPolynomial D Bb :=
    (RingHom.liftOfSurjective (p : MvPolynomial (Fin n ⊕ D) C →+* A') hp)
      ⟨μ₀, fun x hx ↦ hkerμ₀ hx⟩
  have hμ₁ : ∀ q, μ₁ (p q) = μ₀ q := fun q ↦
    RingHom.liftOfSurjective_comp_apply (p : MvPolynomial (Fin n ⊕ D) C →+* A') hp
      ⟨μ₀, fun x hx ↦ hkerμ₀ hx⟩ q
  have hμ₁I : I.map (algebraMap R A') ≤ RingHom.ker μ₁ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, ← p.commutes, hμ₁]
    exact (RingHom.mem_ker).mp (hμ₀I (Ideal.mem_map_of_mem _ hr))
  let μ : A' ⧸ I.map (algebraMap R A') →+* MvPolynomial D Bb :=
    Ideal.Quotient.lift _ μ₁ fun a ha ↦ (RingHom.mem_ker).mp (hμ₁I ha)
  have hμ : ∀ q, μ (mkA (p q)) = μ₀ q := fun q ↦ by
    rw [← hμ₁]
    exact Ideal.Quotient.lift_mk _ _ _
  -- the map `κ : Bb[d] → A' ⧸ I A'`
  let γ₀ : C →+* A' := (p : MvPolynomial (Fin n ⊕ D) C →+* A').comp MvPolynomial.C
  have hγ₀ : γ₀.comp (algebraMap R C) = algebraMap R A' := by
    ext r
    show p (MvPolynomial.C (algebraMap R C r)) = _
    rw [← MvPolynomial.algebraMap_apply]
    exact p.commutes r
  have hJ : I.map (algebraMap R C) ≤ (I.map (algebraMap R A')).comap γ₀ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hγ₀]
  let qC : (C ⧸ I.map (algebraMap R C)) →+* A' ⧸ I.map (algebraMap R A') :=
    Ideal.quotientMap _ γ₀ hJ
  have hqC : ∀ c, qC (mkC c) = mkA (p (MvPolynomial.C c)) := fun c ↦ Ideal.quotientMap_mk
  let η : MvPolynomial (Fin n) (C ⧸ I.map (algebraMap R C)) →+* A' ⧸ I.map (algebraMap R A') :=
    eval₂Hom qC fun k ↦ mkA (p (X (Sum.inl k)))
  have hηC : ∀ c, η (MvPolynomial.C c) = qC c := fun c ↦ eval₂Hom_C _ _ _
  have hηX : ∀ k, η (X k) = mkA (p (X (Sum.inl k))) := fun k ↦ eval₂Hom_X' _ _ _
  have hηmap : ∀ q, η (MvPolynomial.map mkC q) = mkA (p (rename Sum.inl q)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.map_C, hηC, hqC, rename_C]
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X q k hq => simp only [map_mul, hq, MvPolynomial.map_X, hηX, rename_X]
  have hkerη : RingHom.ker f.toRingHom ≤ RingHom.ker η := by
    refine hg.trans ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hηmap, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := Ideal.mem_map_of_mem (p : MvPolynomial (Fin n ⊕ D) C →+* A') (hrel i)
    rw [Ideal.map_map, p.comp_algebraMap] at h1
    have h2 : rel i ∈ RingHom.ker p := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    rw [RingHom.mem_ker] at h2
    rwa [RingHom.coe_coe, map_sub, h2, sub_zero] at h1
  let κB : Bb →+* A' ⧸ I.map (algebraMap R A') :=
    (RingHom.liftOfSurjective f.toRingHom hf) ⟨η, hkerη⟩
  have hκB : ∀ q, κB (f q) = η q := fun q ↦
    RingHom.liftOfSurjective_comp_apply f.toRingHom hf ⟨η, hkerη⟩ q
  let κ : MvPolynomial D Bb →+* A' ⧸ I.map (algebraMap R A') :=
    eval₂Hom κB fun d ↦ mkA (p (X (Sum.inr d)))
  have hκC : ∀ b, κ (MvPolynomial.C b) = κB b := fun b ↦ eval₂Hom_C _ _ _
  have hκX : ∀ d, κ (X d) = mkA (p (X (Sum.inr d))) := fun d ↦ eval₂Hom_X' _ _ _
  have hκBC : ∀ c, κB (algebraMap (C ⧸ I.map (algebraMap R C)) Bb (mkC c)) =
      mkA (p (MvPolynomial.C c)) := by
    intro c
    rw [← hfC, hκB, hηC, hqC]
  -- the two maps are inverse
  have hμη : μ.comp η = MvPolynomial.C.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [RingHom.comp_apply, RingHom.comp_apply, hηC, hqC, hμ, hμ₀C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, hfC]
    · intro k
      rw [RingHom.comp_apply, RingHom.comp_apply, hηX, hμ, hμ₀l, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
  have h1 : μ.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro b
      obtain ⟨q, rfl⟩ := hf b
      rw [RingHom.comp_apply, hκC, hκB, RingHom.id_apply]
      exact RingHom.congr_fun hμη q
    · intro d
      rw [RingHom.comp_apply, hκX, hμ, hμ₀r, RingHom.id_apply]
  have h3 : κ.comp μ₀ = mkA.comp (p : MvPolynomial (Fin n ⊕ D) C →+* A') := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, hμ₀C, hκC, hκBC, RingHom.coe_coe]
    · rintro (k | d)
      · rw [RingHom.comp_apply, RingHom.comp_apply, hμ₀l, hκC, hκB, hηX, RingHom.coe_coe]
      · rw [RingHom.comp_apply, RingHom.comp_apply, hμ₀r, hκX, RingHom.coe_coe]
  have h2 : κ.comp μ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun a ↦ ?_
    obtain ⟨q, rfl⟩ := hp a
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply]
    change κ (μ (mkA (p q))) = mkA (p q)
    rw [hμ]
    exact RingHom.congr_fun h3 q
  let e0 : MvPolynomial D Bb ≃+* A' ⧸ I.map (algebraMap R A') := RingEquiv.ofRingHom κ μ h2 h1
  have hcomm : ∀ x : R ⧸ I, e0 (algebraMap (R ⧸ I) (MvPolynomial D Bb) x) =
      algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) x := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change κ _ = _
    rw [MvPolynomial.algebraMap_apply, hκC,
      IsScalarTower.algebraMap_apply (R ⧸ I) (C ⧸ I.map (algebraMap R C)) Bb,
      Ideal.Quotient.algebraMap_quotient_map_quotient, hκBC,
      Ideal.Quotient.algebraMap_quotient_map_quotient, ← MvPolynomial.algebraMap_apply,
      p.commutes]
  exact ⟨AlgEquiv.ofRingEquiv hcomm⟩

/-- The core of Stacks 07CK: given a presentation of a standard smooth `R ⧸ I`-algebra `Bb`
over `C ⧸ I C` compatible with `ψ : C → Λ` modulo `I`, there is an `R`-algebra `A'` through
which `ψ` factors and a smooth `R`-algebra `B'` mapping onto `A'` with kernel inside `I B'`. -/
theorem exists_cover_of_presentation (hI : IsNilpotent I) {Λ : Type u} [CommRing Λ]
    [Algebra R Λ] {C : Type u} [CommRing C] [Algebra R C] (ψ : C →ₐ[R] Λ)
    {Bb : Type u} [CommRing Bb] [Algebra (R ⧸ I) Bb] [Algebra.IsStandardSmooth (R ⧸ I) Bb]
    [Algebra (C ⧸ I.map (algebraMap R C)) Bb]
    [IsScalarTower (R ⧸ I) (C ⧸ I.map (algebraMap R C)) Bb] {n m : ℕ}
    (f : MvPolynomial (Fin n) (C ⧸ I.map (algebraMap R C)) →ₐ[C ⧸ I.map (algebraMap R C)] Bb)
    (hf : Function.Surjective f) (g : Fin m → MvPolynomial (Fin n) C)
    (hg : RingHom.ker f.toRingHom ≤ Ideal.span (Set.range fun i ↦
      MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)))
    (hg' : ∀ i, f (MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)) = 0)
    (β : Bb →+* Λ ⧸ I.map (algebraMap R Λ))
    (hβ : ∀ c : C, β (algebraMap _ Bb (Ideal.Quotient.mk (I.map (algebraMap R C)) c)) =
      Ideal.Quotient.mk (I.map (algebraMap R Λ)) (ψ c)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A') (B' : Type u) (_ : CommRing B')
      (_ : Algebra R B'), Algebra.Smooth R B' ∧ ∃ θ : B' →ₐ[R] A', Function.Surjective θ ∧
        RingHom.ker θ ≤ I.map (algebraMap R B') ∧
        ∃ (γ : C →ₐ[R] A') (δ : A' →ₐ[R] Λ), δ.comp γ = ψ := by
  classical
  let mkC := Ideal.Quotient.mk (I.map (algebraMap R C))
  have hfC : ∀ x, f (MvPolynomial.C x) = algebraMap _ Bb x := fun x ↦ f.commutes x
  -- lifts of the images of the variables in `Λ ⧸ I Λ`
  choose lam hlam using fun k : Fin n ↦
    Ideal.Quotient.mk_surjective (I := I.map (algebraMap R Λ)) (β (f (X k)))
  let Φ : MvPolynomial (Fin n) C →ₐ[R] Λ := aevalTower ψ lam
  have hΦ : ∀ p, Ideal.Quotient.mk (I.map (algebraMap R Λ)) (Φ p) =
      β (f (MvPolynomial.map mkC p)) := by
    intro p
    have : (Ideal.Quotient.mk (I.map (algebraMap R Λ))).comp (Φ : MvPolynomial (Fin n) C →+* Λ) =
        β.comp ((f : MvPolynomial (Fin n) _ →+* Bb).comp (MvPolynomial.map mkC)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, RingHom.coe_coe, Φ, aevalTower_C, MvPolynomial.map_C, hfC]
        exact (hβ c).symm
      · intro k
        simp only [RingHom.comp_apply, RingHom.coe_coe, Φ, aevalTower_X, MvPolynomial.map_X, hlam]
    exact RingHom.congr_fun this p
  have hΦg : ∀ i, Φ (g i) ∈ I.map (algebraMap R Λ) := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, hΦ, hg' i, map_zero]
  choose N ε s hε hs using fun i ↦ exists_sum_of_mem_map I (hΦg i)
  -- the algebra `A'`
  let D := Σ i : Fin m, Fin (N i)
  let rel : Fin m → MvPolynomial (Fin n ⊕ D) C := fun i ↦
    rename Sum.inl (g i) - ∑ l : Fin (N i), ε i l • X (Sum.inr ⟨i, l⟩)
  let K := Ideal.span (Set.range rel)
  let Φ' : MvPolynomial (Fin n ⊕ D) C →ₐ[R] Λ := aevalTower ψ (Sum.elim lam fun d ↦ s d.1 d.2)
  have hΦ'ren : ∀ p, Φ' (rename Sum.inl p) = Φ p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp only [Φ', Φ, rename_C, aevalTower_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p k hp => simp only [map_mul, hp, rename_X, Φ', Φ, aevalTower_X, Sum.elim_inl]
  have hΦ'rel : ∀ i, Φ' (rel i) = 0 := by
    intro i
    simp only [rel, map_sub, map_sum, map_smul, hΦ'ren, Φ', aevalTower_X, Sum.elim_inr]
    rw [← hs i, sub_self]
  have hKΦ' : K ≤ RingHom.ker Φ' := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hΦ'rel i
  let δ : (MvPolynomial (Fin n ⊕ D) C ⧸ K) →ₐ[R] Λ :=
    Ideal.Quotient.liftₐ K Φ' fun a ha ↦ hKΦ' ha
  let γ : C →ₐ[R] (MvPolynomial (Fin n ⊕ D) C ⧸ K) :=
    (Ideal.Quotient.mkₐ R K).comp (IsScalarTower.toAlgHom R C (MvPolynomial (Fin n ⊕ D) C))
  have hδγ : δ.comp γ = ψ := by
    ext c
    show Φ' (algebraMap C _ c) = ψ c
    exact aevalTower_algebraMap _ _ _
  have hrel : ∀ i, rename Sum.inl (g i) - rel i ∈
      I.map (algebraMap R (MvPolynomial (Fin n ⊕ D) C)) := by
    intro i
    simp only [rel, sub_sub_cancel]
    refine Ideal.sum_mem _ fun l _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hε i l))
  obtain ⟨e⟩ := nonempty_algEquiv_reduction I f hf g hg hg' (Ideal.Quotient.mkₐ R K)
    Ideal.Quotient.mk_surjective rel (Ideal.Quotient.mkₐ_ker R K) hrel
  have : Finite D := inferInstanceAs (Finite (Σ i : Fin m, Fin (N i)))
  have : Algebra.IsStandardSmooth (R ⧸ I) (MvPolynomial D Bb) :=
    Algebra.IsStandardSmooth.trans (R ⧸ I) Bb (MvPolynomial D Bb)
  have := Algebra.IsStandardSmooth.of_algEquiv e
  obtain ⟨B', _, _, hB', θ, hθ, hθker⟩ :=
    exists_smooth_cover I hI (A := MvPolynomial (Fin n ⊕ D) C ⧸ K)
  exact ⟨_, inferInstance, inferInstance, B', _, _, hB', θ, hθ, hθker, γ, δ, hδγ⟩

/-- Stacks 07CK in the form used here: property PT modulo the nilpotent ideal `I` and Stacks
07CH give, for every map `ψ : C → Λ` from a finitely presented `R`-algebra, an `R`-algebra `A'`
through which `ψ` factors and a smooth `R`-algebra `B'` mapping onto `A'` with kernel in `I B'`. -/
theorem exists_cover (hS4 : StandardSmoothRetractStatement.{u}) (hI : IsNilpotent I)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ]
    (hPT : HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C] (ψ : C →ₐ[R] Λ) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A') (B' : Type u) (_ : CommRing B')
      (_ : Algebra R B'), Algebra.Smooth R B' ∧ ∃ θ : B' →ₐ[R] A', Function.Surjective θ ∧
        RingHom.ker θ ≤ I.map (algebraMap R B') ∧
        ∃ (γ : C →ₐ[R] A') (δ : A' →ₐ[R] Λ), δ.comp γ = ψ := by
  classical
  have : Algebra.FinitePresentation (R ⧸ I) (C ⧸ I.map (algebraMap R C)) :=
    Algebra.FinitePresentation.equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm
  have hle : I.map (algebraMap R C) ≤ (I.map (algebraMap R Λ)).comap ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, ψ.commutes]
    exact Ideal.mem_map_of_mem _ hr
  let ψb : (C ⧸ I.map (algebraMap R C)) →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ) :=
    (Ideal.quotientMapₐ _ ψ hle).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hψb : ∀ c, ψb (Ideal.Quotient.mk (I.map (algebraMap R C)) c) =
      Ideal.Quotient.mk (I.map (algebraMap R Λ)) (ψ c) := fun c ↦ rfl
  obtain ⟨B₀, _, _, hB₀, g₀, h₀, hgh⟩ := hPT (C ⧸ I.map (algebraMap R C)) ψb
  obtain ⟨Bb, _, _, _, _, -, hBb, ⟨r⟩⟩ := hS4 (R ⧸ I) B₀
  let γb : (C ⧸ I.map (algebraMap R C)) →ₐ[R ⧸ I] Bb :=
    (IsScalarTower.toAlgHom (R ⧸ I) B₀ Bb).comp g₀
  let : Algebra (C ⧸ I.map (algebraMap R C)) Bb := γb.toRingHom.toAlgebra
  have : IsScalarTower (R ⧸ I) (C ⧸ I.map (algebraMap R C)) Bb :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (γb.commutes x).symm
  have : Algebra.FinitePresentation (C ⧸ I.map (algebraMap R C)) Bb :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (R ⧸ I) _ _
  obtain ⟨n, f, hf, hfg⟩ :=
    Algebra.FinitePresentation.out (R := C ⧸ I.map (algebraMap R C)) (A := Bb)
  obtain ⟨m, gb, hgb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hsurj : Function.Surjective
      (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk (I.map (algebraMap R C)))) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose g hg using fun i ↦ hsurj (gb i)
  have hgb' : (fun i ↦ MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)) = gb :=
    funext hg
  have hker : RingHom.ker f.toRingHom ≤ Ideal.span (Set.range fun i ↦
      MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)) := by
    intro x hx
    rw [← hgb] at hx
    rw [hgb']
    exact hx
  have hg' : ∀ i, f (MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R C))) (g i)) = 0 := by
    intro i
    rw [hg]
    have : gb i ∈ RingHom.ker f.toRingHom := hgb ▸ Submodule.subset_span ⟨i, rfl⟩
    exact (RingHom.mem_ker).mp this
  let β : Bb →+* Λ ⧸ I.map (algebraMap R Λ) :=
    (h₀ : B₀ →+* Λ ⧸ I.map (algebraMap R Λ)).comp (r : Bb →+* B₀)
  have hβ : ∀ c : C, β (algebraMap _ Bb (Ideal.Quotient.mk (I.map (algebraMap R C)) c)) =
      Ideal.Quotient.mk (I.map (algebraMap R Λ)) (ψ c) := by
    intro c
    change h₀ (r (algebraMap B₀ Bb (g₀ (Ideal.Quotient.mk (I.map (algebraMap R C)) c)))) = _
    rw [r.commutes, Algebra.algebraMap_self_apply, ← AlgHom.comp_apply, hgh, hψb]
  exact exists_cover_of_presentation I hI ψ f hf g hker hg' β hβ

end Cover

section Step

variable {R : Type u} [CommRing R] (I : Ideal R)

lemma isNilpotent_of_le_map (hI : IsNilpotent I) {S : Type*} [CommRing S] [Algebra R S]
    {J : Ideal S} (hJ : J ≤ I.map (algebraMap R S)) : IsNilpotent J := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨k, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc J ^ k ≤ (I.map (algebraMap R S)) ^ k := Ideal.pow_right_mono hJ k
    _ = (I ^ k).map (algebraMap R S) := (Ideal.map_pow _ _ _).symm
    _ ≤ ⊥ := by rw [hk, Ideal.zero_eq_bot, Ideal.map_bot]

/-- One step of the proof of Stacks 07CM: an element `h ∈ I ^ k B` killed by `φ : B → Λ` can be
pushed into `I ^ (k + 1) B'` along a factorization `B → B' → Λ` of `φ` through a smooth `B'`. -/
theorem exists_step (hS4 : StandardSmoothRetractStatement.{u}) (hI : IsNilpotent I)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ] [Module.Flat R Λ]
    (hPT : HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B] (φ : B →ₐ[R] Λ) (k : ℕ)
    {h : B} (hh : h ∈ (I ^ k).map (algebraMap R B)) (hφ : φ h = 0) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra R B'), Algebra.Smooth R B' ∧
      ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), β.comp α = φ ∧
        α h ∈ (I ^ (k + 1)).map (algebraMap R B') := by
  classical
  obtain ⟨N, ε, s, hε, hs⟩ := exists_sum_of_mem_map (I ^ k) hh
  have h0 : ∑ l, ε l • φ (s l) = 0 := by
    rw [← hφ, hs, map_sum]
    simp only [map_smul]
  obtain ⟨K, a, y, hy, hrel⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := Λ)
    (f := ε) (x := fun l ↦ φ (s l)) h0
  -- the finitely presented algebra `C = B[x] / (s l - Σ a l j x j)`
  let rels : Fin N → MvPolynomial (Fin K) B := fun l ↦ MvPolynomial.C (s l) - ∑ j, a l j • X j
  let Kc := Ideal.span (Set.range rels)
  have : Algebra.FinitePresentation R (MvPolynomial (Fin K) B ⧸ Kc) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range rels))
  let ψ₀ : MvPolynomial (Fin K) B →ₐ[R] Λ := aevalTower φ y
  have hψ₀ : Kc ≤ RingHom.ker ψ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    simp only [rels, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_sum, map_smul, ψ₀,
      aevalTower_C, aevalTower_X]
    exact sub_eq_zero.mpr (hy l)
  let ψ : (MvPolynomial (Fin K) B ⧸ Kc) →ₐ[R] Λ := Ideal.Quotient.liftₐ Kc ψ₀ fun x hx ↦ hψ₀ hx
  let ιC : B →ₐ[R] MvPolynomial (Fin K) B ⧸ Kc :=
    (Ideal.Quotient.mkₐ R Kc).comp (IsScalarTower.toAlgHom R B (MvPolynomial (Fin K) B))
  have hψι : ∀ b, ψ (ιC b) = φ b := fun b ↦ aevalTower_algebraMap _ _ _
  obtain ⟨A', _, _, B', _, _, hB', θ, hθ, hθker, γ, δ, hδγ⟩ := exists_cover I hS4 hI hPT ψ
  have hnil : IsNilpotent (RingHom.ker θ) := isNilpotent_of_le_map I hI hθker
  let α : B →ₐ[R] B' := Algebra.FormallySmooth.liftOfSurjective (γ.comp ιC) θ hθ hnil
  have hα : ∀ b, θ (α b) = γ (ιC b) := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply (γ.comp ιC) θ hθ hnil b
  refine ⟨B', inferInstance, inferInstance, hB', α, δ.comp θ, ?_, ?_⟩
  · ext b
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hα, ← AlgHom.comp_apply δ γ, hδγ, hψι]
  · -- lift the images of the variables
    choose y' hy' using fun j ↦ hθ (γ (Ideal.Quotient.mkₐ R Kc (X j)))
    let z : Fin N → B' := fun l ↦ α (s l) - ∑ j, a l j • y' j
    have hz : ∀ l, z l ∈ I.map (algebraMap R B') := by
      intro l
      apply hθker
      have hιs : ιC (s l) = Ideal.Quotient.mkₐ R Kc (∑ j, a l j • X j) := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        show Ideal.Quotient.mk Kc (MvPolynomial.C (s l)) = _
        rw [Ideal.Quotient.eq]
        exact Ideal.subset_span ⟨l, rfl⟩
      rw [RingHom.mem_ker, map_sub, hα, hιs]
      simp only [map_sum, map_smul, hy', sub_self]
    have key : α h = ∑ l, ε l • z l := by
      have h2 : ∑ l, ε l • ∑ j, a l j • y' j = 0 := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, hrel, zero_smul, Finset.sum_const_zero]
      calc α h = ∑ l, ε l • α (s l) := by rw [hs, map_sum]; simp only [map_smul]
        _ = ∑ l, ε l • z l + ∑ l, ε l • ∑ j, a l j • y' j := by
          rw [← Finset.sum_add_distrib]
          simp only [z, ← smul_add, sub_add_cancel]
        _ = ∑ l, ε l • z l := by rw [h2, add_zero]
    rw [key]
    refine Ideal.sum_mem _ fun l _ ↦ ?_
    rw [Algebra.smul_def, pow_succ, Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hε l)) (hz l)

end Step

section Final

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Iterating `exists_step` until `I ^ N = 0`: an element killed by `φ : B → Λ` is killed by
some factorization `B → B' → Λ` of `φ` through a smooth `B'`. -/
theorem exists_kill_one (hS4 : StandardSmoothRetractStatement.{u}) (hI : IsNilpotent I)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ] [Module.Flat R Λ]
    (hPT : HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B] (φ : B →ₐ[R] Λ)
    {h : B} (hφ : φ h = 0) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra R B'), Algebra.Smooth R B' ∧
      ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), β.comp α = φ ∧ α h = 0 := by
  have key : ∀ k : ℕ, ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra R B'),
      Algebra.Smooth R B' ∧ ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), β.comp α = φ ∧
        α h ∈ (I ^ k).map (algebraMap R B') := by
    intro k
    induction k with
    | zero =>
      refine ⟨B, inferInstance, inferInstance, inferInstance, AlgHom.id R B, φ, rfl, ?_⟩
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ k ih =>
      obtain ⟨B', _, _, hB', α, β, hβα, hα⟩ := ih
      have hβ : β (α h) = 0 := by rw [← AlgHom.comp_apply, hβα, hφ]
      obtain ⟨B'', _, _, hB'', α', β', hβα', hα'⟩ := exists_step I hS4 hI hPT β k hα hβ
      refine ⟨B'', inferInstance, inferInstance, hB'', α'.comp α, β', ?_, hα'⟩
      rw [← AlgHom.comp_assoc, hβα', hβα]
  obtain ⟨N, hN⟩ := hI
  obtain ⟨B', _, _, hB', α, β, hβα, hα⟩ := key N
  refine ⟨B', inferInstance, inferInstance, hB', α, β, hβα, ?_⟩
  rwa [hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at hα

/-- `exists_kill_one` for a finite family of elements killed by `φ`. -/
theorem exists_kill_family (hS4 : StandardSmoothRetractStatement.{u}) (hI : IsNilpotent I)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ] [Module.Flat R Λ]
    (hPT : HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) (m : ℕ)
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B] (φ : B →ₐ[R] Λ)
    (h : Fin m → B) (hφ : ∀ i, φ (h i) = 0) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra R B'), Algebra.Smooth R B' ∧
      ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), β.comp α = φ ∧ ∀ i, α (h i) = 0 := by
  induction m generalizing B with
  | zero =>
    exact ⟨B, inferInstance, inferInstance, inferInstance, AlgHom.id R B, φ, rfl,
      fun i ↦ i.elim0⟩
  | succ m ih =>
    obtain ⟨B', _, _, hB', α, β, hβα, hα⟩ :=
      ih φ (fun i ↦ h i.castSucc) fun i ↦ hφ i.castSucc
    have hβ : β (α (h (Fin.last m))) = 0 := by rw [← AlgHom.comp_apply, hβα, hφ]
    obtain ⟨B'', _, _, hB'', α', β', hβα', hα'⟩ := exists_kill_one I hS4 hI hPT β hβ
    refine ⟨B'', inferInstance, inferInstance, hB'', α'.comp α, β', ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hβα', hβα]
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact hα'
      · rw [AlgHom.comp_apply, hα j, map_zero]

end Final

/-- Stacks 07CM, conditional on Stacks 07CH (`StandardSmoothRetractStatement`). -/
theorem nilpotentLifting_of (hS4 : StandardSmoothRetractStatement.{u}) :
    NilpotentLiftingStatement.{u} := by
  intro R Λ _ _ _ I hI _ hPT A _ _ _ f
  obtain ⟨n, p, hp, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  obtain ⟨m, h, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hhp : ∀ i, p (h i) = 0 := fun i ↦ by
    have : h i ∈ RingHom.ker p.toRingHom := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  have : Algebra.Smooth R (MvPolynomial (Fin n) R) := {}
  obtain ⟨B', _, _, hB', α, β, hβα, hα⟩ :=
    exists_kill_family I hS4 hI hPT m (f.comp p) h fun i ↦ by
      rw [AlgHom.comp_apply, hhp i, map_zero]
  have hle : RingHom.ker p.toRingHom ≤ RingHom.ker α.toRingHom := by
    rw [← hspan]
    change Ideal.span _ ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hα i
  refine ⟨B', inferInstance, inferInstance, hB', AlgHom.liftOfSurjective p hp α hle, β, ?_⟩
  ext x
  obtain ⟨q, rfl⟩ := hp x
  rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply, ← AlgHom.comp_apply, hβα,
    AlgHom.comp_apply]

/-- Stacks Proposition 16.5.3 (07CM). -/
theorem nilpotentLifting : NilpotentLiftingStatement.{u} :=
  nilpotentLifting_of StandardSmoothRetract.standardSmoothRetract

end Langlands.CommutativeAlgebra.Popescu.NilpotentLifting
