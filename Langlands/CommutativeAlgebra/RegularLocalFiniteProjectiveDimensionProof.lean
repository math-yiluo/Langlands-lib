import Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionStatement
import Langlands.CommutativeAlgebra.RegularLocalDomainProof
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Proof: finite modules over regular local rings have finite projective dimension -/

universe u

open CategoryTheory IsLocalRing

namespace Langlands.CommutativeAlgebra

namespace RegularLocalFiniteProjectiveDimension

section ChangeOfRings

variable {R : Type u} [CommRing R] (x : R)

/-- Restriction of scalars along `R → R ⧸ (x)`. -/
noncomputable abbrev res : ModuleCat.{u} (R ⧸ Ideal.span {x}) ⥤ ModuleCat.{u} R :=
  ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))

variable {x}

/-- Restriction of scalars along `R → R ⧸ (x)` preserves short exact sequences. -/
theorem shortExact_map_res {T : ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x}))}
    (hT : T.ShortExact) : (T.map (res x)).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
    hT.moduleCat_injective_f hT.moduleCat_surjective_g

variable (x) in
/-- Reduction modulo `x` on a free module, as an `R`-linear map to the restriction of the
free `R ⧸ (x)`-module. -/
noncomputable def finsuppReduce (I : Type u) :
    (I →₀ R) →ₗ[R] (res x).obj (ModuleCat.of (R ⧸ Ideal.span {x}) (I →₀ R ⧸ Ideal.span {x})) where
  toFun v := Finsupp.mapRange (Ideal.Quotient.mk _) (map_zero _) v
  map_add' v w := Finsupp.mapRange_add (map_add _) v w
  map_smul' r v := by
    refine Finsupp.ext fun i => ?_
    change Ideal.Quotient.mk _ (r * v i) = Ideal.Quotient.mk _ r * Ideal.Quotient.mk _ (v i)
    exact map_mul _ _ _

/-- A free `R ⧸ (x)`-module has projective dimension at most one over `R` when `x` is
`R`-regular. -/
theorem hasProjectiveDimensionLT_res_finsupp (hx : IsSMulRegular R x) (I : Type u) :
    HasProjectiveDimensionLT
      ((res x).obj (ModuleCat.of (R ⧸ Ideal.span {x}) (I →₀ R ⧸ Ideal.span {x}))) 2 := by
  let T : ShortComplex (ModuleCat.{u} R) :=
    { X₁ := ModuleCat.of R (I →₀ R)
      X₂ := ModuleCat.of R (I →₀ R)
      X₃ := (res x).obj (ModuleCat.of (R ⧸ Ideal.span {x}) (I →₀ R ⧸ Ideal.span {x}))
      f := ModuleCat.ofHom (x • LinearMap.id)
      g := ModuleCat.ofHom (finsuppReduce x I)
      zero := by
        refine ModuleCat.hom_ext (LinearMap.ext fun v => Finsupp.ext fun i => ?_)
        change Ideal.Quotient.mk _ (x * v i) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x) }
  have hT : T.ShortExact := by
    refine ModuleCat.shortComplex_shortExact T ?_ ?_ ?_
    · intro w
      constructor
      · intro hw
        classical
        have hw' : (Finsupp.mapRange (Ideal.Quotient.mk _) (map_zero _) w :
            I →₀ R ⧸ Ideal.span {x}) = 0 := hw
        have hmem : ∀ i, w i ∈ Ideal.span {x} := fun i => by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact DFunLike.congr_fun hw' i
        let φ : R → R := fun a =>
          if h : a ∈ Ideal.span {x} then (Ideal.mem_span_singleton'.mp h).choose else 0
        have hφ : ∀ a ∈ Ideal.span {x}, x * φ a = a := fun a h => by
          simp only [φ, h, ↓reduceDIte]
          rw [mul_comm]
          exact (Ideal.mem_span_singleton'.mp h).choose_spec
        have hφ0 : φ 0 = 0 := hx (by simpa [smul_eq_mul] using hφ 0 (zero_mem _))
        refine ⟨Finsupp.mapRange φ hφ0 w, Finsupp.ext fun i => ?_⟩
        change x * φ (w i) = w i
        exact hφ _ (hmem i)
      · rintro ⟨v, rfl⟩
        exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp T.zero) v
    · intro v w h
      refine Finsupp.ext fun i => ?_
      exact hx (DFunLike.congr_fun h i)
    · exact Finsupp.mapRange_surjective _ (map_zero _) Ideal.Quotient.mk_surjective
  have : Projective T.X₂ := by
    change Projective (ModuleCat.of R (I →₀ R))
    infer_instance
  exact hT.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

/-- A projective `R ⧸ (x)`-module has projective dimension at most one over `R` when `x` is
`R`-regular: it is a retract of a free module. -/
theorem hasProjectiveDimensionLT_res_of_projective (hx : IsSMulRegular R x)
    (N : ModuleCat.{u} (R ⧸ Ideal.span {x})) [Projective N] :
    HasProjectiveDimensionLT ((res x).obj N) 2 := by
  let f : ModuleCat.of (R ⧸ Ideal.span {x}) (N →₀ R ⧸ Ideal.span {x}) ⟶ N :=
    ModuleCat.ofHom (Finsupp.linearCombination _ id)
  have : Epi f := (ModuleCat.epi_iff_surjective _).mpr fun v =>
    ⟨Finsupp.single v 1, by simp [f]⟩
  let e : Retract N (ModuleCat.of (R ⧸ Ideal.span {x}) (N →₀ R ⧸ Ideal.span {x})) :=
    { i := Projective.factorThru (𝟙 N) f
      r := f
      retract := Projective.factorThru_comp _ _ }
  have := hasProjectiveDimensionLT_res_finsupp hx N
  exact (e.map (res x)).hasProjectiveDimensionLT 2

/-- Change of rings: if an `R ⧸ (x)`-module has projective dimension at most `n`, its
restriction to `R` has projective dimension at most `n + 1`, when `x` is `R`-regular. -/
theorem hasProjectiveDimensionLE_res (hx : IsSMulRegular R x) (n : ℕ) :
    ∀ (N : ModuleCat.{u} (R ⧸ Ideal.span {x})), HasProjectiveDimensionLE N n →
      HasProjectiveDimensionLE ((res x).obj N) (n + 1) := by
  induction n with
  | zero =>
    intro N hN
    have : Projective N := (projective_iff_hasProjectiveDimensionLE_zero N).mpr hN
    exact hasProjectiveDimensionLT_res_of_projective hx N
  | succ n ih =>
    intro N hN
    let f := Finsupp.linearCombination (R ⧸ Ideal.span {x}) (id : N → N)
    have hf : Function.Surjective f := fun v => ⟨Finsupp.single v 1, by simp [f]⟩
    have hT := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (LinearMap.ker f)) n :=
      hT.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance hN
    have h1 := ih _ hK
    have := hasProjectiveDimensionLT_res_finsupp hx N
    have h2 : HasProjectiveDimensionLT
        ((res x).obj (ModuleCat.of (R ⧸ Ideal.span {x}) (N →₀ R ⧸ Ideal.span {x}))) (n + 3) :=
      hasProjectiveDimensionLT_of_ge _ 2 (n + 3) (by omega)
    exact (shortExact_map_res hT).hasProjectiveDimensionLT_X₃ (n + 2) h1 h2

end ChangeOfRings

section RegularLocal

/-- Finite modules over a regular local ring whose maximal ideal is generated by `d` elements
have projective dimension at most `d`. -/
theorem hasProjectiveDimensionLE_of_spanFinrank_eq (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], (maximalIdeal R).spanFinrank = d →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
        HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro R _ _ hd M _ _ _
  have hreg : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · -- `𝔪 = 0`, so `R` is a field and `M` is free.
    subst h0
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp hd
    let _ : Field R := (isField_iff_maximalIdeal_eq.mpr hbot).toField
    have : Projective (ModuleCat.of R M) := inferInstance
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp this
  · have hm2 : maximalIdeal R ≠ maximalIdeal R ^ 2 := by
      intro h
      have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
        rw [smul_eq_mul, ← pow_two, ← h]
      have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing hle (maximalIdeal_le_jacobson _)
      rw [this, Submodule.spanFinrank_bot] at hd
      omega
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt
      (lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) hm2.symm)
    have : IsDomain R := regularLocalDomain R inferInstance
    have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
    -- `R ⧸ (x)` is regular local, with fewer generators of its maximal ideal.
    have hxtop : Ideal.span {x} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal x).mp hx
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hdrop := RegularLocalDomain.spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hdim : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
      have := Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal R) hx
      rwa [maximalIdeal_height_eq_ringKrullDim] at this
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
      apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
        (ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial :
          ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊥)
      rw [← he, ← hreg] at hdim
      rw [← he]
      have h1 : (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : ℕ∞) ≤ e + 1 := by
        have := (Nat.cast_le (α := WithBot ℕ∞)).mpr hdrop
        exact_mod_cast this.trans hdim
      have h2 : ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : ℕ∞) ≤ e := by
        push_cast at h1
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
      exact_mod_cast h2
    set m := (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank with hm
    -- A finite free presentation `0 → K → R^k → M → 0`.
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    have hT := LinearMap.shortExact_shortComplexKer hf
    have hKreg : IsSMulRegular (LinearMap.ker f) x := IsSMulRegular.of_ne_zero hx0
    -- `K ⧸ x K` is a finite `R ⧸ (x)`-module, so its projective dimension is at most `m`.
    have : IsScalarTower R (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hQ := ih m (by omega) (R ⧸ Ideal.span {x}) rfl (QuotSMulTop x (LinearMap.ker f))
    have hQR := hasProjectiveDimensionLE_res (IsSMulRegular.of_ne_zero hx0) m _ hQ
    let eQ : (res x).obj (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)))
        ≃ₗ[R] ModuleCat.of R (QuotSMulTop x (LinearMap.ker f)) :=
      { toFun := id
        invFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hQR' : HasProjectiveDimensionLE
        (ModuleCat.of R (QuotSMulTop x (LinearMap.ker f))) (m + 1) :=
      ModuleCat.hasProjectiveDimensionLE_of_linearEquiv eQ (m + 1)
    -- Hence the projective dimension of `K` is at most `m`.
    have hpd := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (LinearMap.ker f)) x hKreg hx
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) m := by
      rw [← projectiveDimension_le_iff] at hQR' ⊢
      rw [hpd, Nat.cast_add, Nat.cast_one] at hQR'
      exact ENat.WithBot.add_le_add_one_right_iff.mp hQR'
    have h2 : HasProjectiveDimensionLT (ModuleCat.of R (Fin k → R)) (m + 2) :=
      hasProjectiveDimensionLT_of_ge _ 1 (m + 2) (by omega)
    have hM : HasProjectiveDimensionLT (ModuleCat.of R M) (m + 2) :=
      hT.hasProjectiveDimensionLT_X₃ (m + 1) hK h2
    exact hasProjectiveDimensionLT_of_ge _ (m + 2) (d + 1) (by omega)

end RegularLocal

end RegularLocalFiniteProjectiveDimension

open RegularLocalFiniteProjectiveDimension in
/-- Every finite module over a regular local ring has finite projective dimension. -/
theorem regularLocalFiniteProjectiveDimension :
    RegularLocalFiniteProjectiveDimensionStatement.{u} := by
  intro R _ hR M _ _ _
  exact ⟨_, hasProjectiveDimensionLE_of_spanFinrank_eq _ R rfl M⟩

end Langlands.CommutativeAlgebra
