import Langlands.CommutativeAlgebra.Popescu.DesingTools

/-! # Local structure of a presentation at a smooth point (in the spirit of Stacks 07C6) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.Desing

open MvPolynomial

section LinearAlgebra

/-- Given vectors `v_ℓ ∈ K^n`, pick a maximal linearly independent subfamily `v ∘ e` and columns
`u` such that the square minor `(v (e j) (u l))` is invertible. -/
theorem exists_basis_minor {K : Type*} [Field K] {n m : ℕ} (v : Fin m → Fin n → K) :
    ∃ (c : ℕ) (e : Fin c → Fin m) (u : Fin c → Fin n), Function.Injective e ∧
      Function.Injective u ∧ (∀ ℓ, v ℓ ∈ Submodule.span K (Set.range (v ∘ e))) ∧
      Matrix.det (Matrix.of fun j l : Fin c ↦ v (e j) (u l)) ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let eqv := Fintype.equivFin κ
  set c := Fintype.card κ
  let e : Fin c → Fin m := a ∘ eqv.symm
  have he : Function.Injective e := ha.comp eqv.symm.injective
  have hli' : LinearIndependent K (v ∘ e) := hli.comp _ eqv.symm.injective
  have hspan' : Submodule.span K (Set.range (v ∘ e)) = Submodule.span K (Set.range v) := by
    rw [← hspan]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨eqv.symm j, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨eqv k, by simp [e]⟩
  let V : Matrix (Fin c) (Fin n) K := Matrix.of fun j i ↦ v (e j) i
  have hrank : V.rank = c := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : V.row = v ∘ e := rfl
    rw [this, finrank_span_eq_card hli', Fintype.card_fin]
  have hcols : Submodule.span K (Set.range V.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank, Module.finrank_fin_fun]
  obtain ⟨κ', a', ha', hspan2, hli2⟩ := exists_linearIndependent' K V.col
  have : Finite κ' := Finite.of_injective a' ha'
  have : Fintype κ' := Fintype.ofFinite κ'
  have hcard : Fintype.card κ' = c := by
    have hb : Submodule.span K (Set.range (V.col ∘ a')) = ⊤ := by rw [hspan2, hcols]
    let b := Module.Basis.mk hli2 (by rw [hb])
    rw [← Module.finrank_fin_fun K (n := c), Module.finrank_eq_card_basis b]
  let eqv' : κ' ≃ Fin c := (Fintype.equivFin κ').trans (finCongr hcard)
  let u : Fin c → Fin n := a' ∘ eqv'.symm
  have hu : Function.Injective u := ha'.comp eqv'.symm.injective
  refine ⟨c, e, u, he, hu, fun ℓ ↦ ?_, ?_⟩
  · rw [hspan']
    exact Submodule.subset_span ⟨ℓ, rfl⟩
  · have hli3 : LinearIndependent K (V.col ∘ u) := hli2.comp _ eqv'.symm.injective
    have : (Matrix.of fun j l : Fin c ↦ v (e j) (u l)).col = V.col ∘ u := rfl
    rw [← this, Matrix.linearIndependent_cols_iff_isUnit] at hli3
    exact (Matrix.isUnit_iff_isUnit_det _).mp hli3 |>.ne_zero

end LinearAlgebra

section Nakayama

open IsLocalRing TensorProduct

/-- Nakayama over a local ring `P`: if the images of `F ∘ g` span `k ⊗ M` over the residue field
in the sense that every `1 ⊗ F i` is a combination of the `1 ⊗ F (g j)`, and the `F i` span `M`,
then the `F (g j)` span `M`. -/
theorem span_comp_eq_top_of_tmul {P M : Type*} [CommRing P] [IsLocalRing P] [AddCommGroup M]
    [Module P M] [Module.Finite P M] {ι κ : Type*} [Fintype κ] (F : ι → M)
    (hF : ∀ x : M, ∃ (s : Finset ι) (b : ι → P), ∑ i ∈ s, b i • F i = x) (g : κ → ι)
    (hrel : ∀ i, ∃ c : κ → ResidueField P,
      (1 : ResidueField P) ⊗ₜ[P] F i = ∑ j, c j ⊗ₜ[P] F (g j)) :
    Submodule.span P (Set.range (F ∘ g)) = ⊤ := by
  classical
  set N := Submodule.span P (Set.range (F ∘ g))
  have hres : ∀ a : ResidueField P, ∃ p : P, a = p • (1 : ResidueField P) := by
    intro a
    obtain ⟨p, rfl⟩ := residue_surjective a
    exact ⟨p, by rw [← ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one]⟩
  have hFj : ∀ i, (1 : ResidueField P) ⊗ₜ[P] F i ∈ N.map (TensorProduct.mk P (ResidueField P) M 1) := by
    intro i
    obtain ⟨c, hc⟩ := hrel i
    rw [hc]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    obtain ⟨p, hp⟩ := hres (c j)
    rw [hp, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩))
  have hNtop : N.map (TensorProduct.mk P (ResidueField P) M 1) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨s, b, hb⟩ := hF x
      rw [← hb, tmul_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [tmul_smul]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨p, hp⟩ := hres a
      rw [hp, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ (hFj i)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact (map_tensorProduct_mk_eq_top).mp hNtop

end Nakayama

section Chart

open IsLocalRing KaehlerDifferential TensorProduct

/-- A presentation `φ : k[x] ↠ C` with kernel `(f_1, …, f_m)`, smooth at a prime `q`: there are
relations `f ∘ e`, variables `u` and `a ∈ k[x]` with `a · det(∂ f_{e j} / ∂ x_{u l}) ∉ q` and
`a f_ℓ ∈ (f ∘ e)` for all `ℓ`. -/
theorem exists_chart {k : Type u} [CommRing k] {C : Type u} [CommRing C] [Algebra k C] {n m : ℕ}
    (φ : MvPolynomial (Fin n) k →ₐ[k] C) (hφ : Function.Surjective φ)
    (f : Fin m → MvPolynomial (Fin n) k) (hker : RingHom.ker φ = Ideal.span (Set.range f))
    (q : Ideal C) [q.IsPrime] (hq : Algebra.IsSmoothAt k q) :
    ∃ (c : ℕ) (e : Fin c → Fin m) (u : Fin c → Fin n) (a : MvPolynomial (Fin n) k),
      Function.Injective e ∧ Function.Injective u ∧
      φ (a * Matrix.det (Matrix.of fun j l : Fin c ↦ pderiv (u l) (f (e j)))) ∉ q ∧
      ∀ ℓ, a * f ℓ ∈ Ideal.span (Set.range (f ∘ e)) := by
  classical
  have hfker : ∀ j, φ (f j) = 0 := fun j ↦ by
    have : f j ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨j, rfl⟩
    exact this
  let q₀ : Ideal (MvPolynomial (Fin n) k) := q.comap φ
  let ρ : Localization.AtPrime q₀ →+* Localization.AtPrime q :=
    Localization.localRingHom q₀ q φ.toRingHom rfl
  let _ : Algebra (Localization.AtPrime q₀) (Localization.AtPrime q) := ρ.toAlgebra
  have hρ : ∀ x, ρ (algebraMap _ (Localization.AtPrime q₀) x) =
      algebraMap C (Localization.AtPrime q) (φ x) :=
    fun x ↦ Localization.localRingHom_to_map _ _ _ _ x
  have hρmk' : ∀ x (y : q₀.primeCompl), ρ (IsLocalization.mk' (Localization.AtPrime q₀) x y) =
      IsLocalization.mk' (Localization.AtPrime q) (φ x) (⟨φ y, y.2⟩ : q.primeCompl) :=
    fun x y ↦ Localization.localRingHom_mk' _ _ _ _ x y
  have : IsScalarTower k (Localization.AtPrime q₀) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      show algebraMap k _ r = ρ (algebraMap k _ r)
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (Localization.AtPrime q₀), hρ,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hρsurj : Function.Surjective ρ := by
    intro z
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨x', rfl⟩ := hφ x
    obtain ⟨t', ht'⟩ := hφ t
    have ht'q : t' ∈ q₀.primeCompl := by
      show φ t' ∉ q
      rw [ht']
      exact t.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime q₀) x' ⟨t', ht'q⟩, ?_⟩
    rw [hρmk']
    show _ = IsLocalization.mk' (Localization.AtPrime q) (φ x') t
    congr 1
    exact Subtype.ext ht'
  -- the kernel of `ρ`
  have hFker : ∀ j, algebraMap _ (Localization.AtPrime q₀) (f j) ∈
      RingHom.ker (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q)) := by
    intro j
    rw [RingHom.mem_ker]
    show ρ _ = 0
    rw [hρ, hfker j, map_zero]
  have hkerspan : RingHom.ker (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q)) =
      Ideal.span (Set.range fun j ↦ algebraMap _ (Localization.AtPrime q₀) (f j)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective q₀.primeCompl x
      dsimp only at hx ⊢
      rw [RingHom.mem_ker] at hx
      change ρ (IsLocalization.mk' _ p s) = 0 at hx
      rw [hρmk', IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨⟨t, ht⟩, htp⟩ := hx
      obtain ⟨t', rfl⟩ := hφ t
      have h1 : t' * p ∈ Ideal.span (Set.range f) := by
        rw [← hker, RingHom.mem_ker, map_mul]
        exact htp
      have h2 : algebraMap _ (Localization.AtPrime q₀) (t' * p) ∈
          Ideal.span (Set.range fun j ↦ algebraMap _ (Localization.AtPrime q₀) (f j)) := by
        have := Ideal.mem_map_of_mem (algebraMap _ (Localization.AtPrime q₀)) h1
        rw [Ideal.map_span, ← Set.range_comp] at this
        exact this
      have ht'q : t' ∈ q₀.primeCompl := ht
      have hu : IsUnit (algebraMap _ (Localization.AtPrime q₀) (t' * s)) := by
        simpa using IsLocalization.map_units (Localization.AtPrime q₀)
          (⟨t', ht'q⟩ * s : q₀.primeCompl)
      have h4 : IsLocalization.mk' (Localization.AtPrime q₀) p s *
          algebraMap _ (Localization.AtPrime q₀) (t' * s) =
          algebraMap _ (Localization.AtPrime q₀) (t' * p) := by
        rw [map_mul, mul_left_comm, IsLocalization.mk'_spec, ← map_mul]
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      have : IsLocalization.mk' (Localization.AtPrime q₀) p s =
          algebraMap _ (Localization.AtPrime q₀) (t' * p) * w := by
        rw [← h4, mul_assoc, hw, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hFker j
  have hkerFG : (RingHom.ker (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q))).FG := by
    rw [hkerspan]
    exact Submodule.fg_span (Set.finite_range _)
  -- Kähler differentials of `P = k[x]_{q₀}`
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) :=
    Algebra.FormallyEtale.of_isLocalization q₀.primeCompl
  let eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k)
    (Localization.AtPrime q₀)
  have : Module.Free (Localization.AtPrime q₀) Ω[Localization.AtPrime q₀⁄k] :=
    Module.Free.of_equiv eΩ
  have : Module.Finite (Localization.AtPrime q₀) Ω[Localization.AtPrime q₀⁄k] :=
    Module.Finite.equiv eΩ
  -- the residue field of `P` as an algebra over `S`
  have hkerle : RingHom.ker ρ ≤
      RingHom.ker (algebraMap (Localization.AtPrime q₀) (ResidueField (Localization.AtPrime q₀))) := by
    intro x hx
    rw [RingHom.mem_ker, ResidueField.algebraMap_eq, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff]
    intro hxu
    have := hxu.map ρ
    rw [(RingHom.mem_ker).mp hx] at this
    exact not_isUnit_zero this
  let σS : Localization.AtPrime q →+* ResidueField (Localization.AtPrime q₀) :=
    ρ.liftOfSurjective hρsurj ⟨algebraMap _ _, hkerle⟩
  let _ : Algebra (Localization.AtPrime q) (ResidueField (Localization.AtPrime q₀)) :=
    σS.toAlgebra
  have : IsScalarTower (Localization.AtPrime q₀) (Localization.AtPrime q)
      (ResidueField (Localization.AtPrime q₀)) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    show algebraMap _ _ x = σS (ρ x)
    exact (RingHom.liftOfSurjective_comp_apply ρ hρsurj ⟨_, hkerle⟩ x).symm
  have h₃ : maximalIdeal (Localization.AtPrime q) ≤
      RingHom.ker (algebraMap (Localization.AtPrime q) (ResidueField (Localization.AtPrime q₀))) := by
    intro s hs
    obtain ⟨x, rfl⟩ := hρsurj s
    rw [RingHom.mem_ker]
    show σS (ρ x) = 0
    rw [RingHom.liftOfSurjective_comp_apply]
    show algebraMap _ (ResidueField (Localization.AtPrime q₀)) x = 0
    rw [ResidueField.algebraMap_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs
    exact fun hu ↦ hs (hu.map ρ)
  have hinj := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := k)
    (S := Localization.AtPrime q) (Localization.AtPrime q₀)
    (ResidueField (Localization.AtPrime q₀)) hρsurj hkerFG h₃).mp hq
  -- the cotangent complex on the generators `f_j`
  let F : Fin m → RingHom.ker (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q)) :=
    fun j ↦ ⟨_, hFker j⟩
  let v : Fin m → Fin n → (ResidueField (Localization.AtPrime q₀)) :=
    fun j i ↦ algebraMap _ (ResidueField (Localization.AtPrime q₀)) (algebraMap _ (Localization.AtPrime q₀) (pderiv i (f j)))
  let w : Fin n → (ResidueField (Localization.AtPrime q₀)) ⊗[Localization.AtPrime q₀] Ω[Localization.AtPrime q₀⁄k] :=
    fun i ↦ 1 ⊗ₜ D k (Localization.AtPrime q₀)
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i))
  have hDf : ∀ p : MvPolynomial (Fin n) k,
      D k (Localization.AtPrime q₀) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) p) =
        ∑ i, algebraMap _ (Localization.AtPrime q₀) (pderiv i p) •
          D k (Localization.AtPrime q₀) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i)) := by
    intro p
    have h := (mvPolynomialBasis k (Fin n)).sum_repr (D k (MvPolynomial (Fin n) k) p)
    simp only [mvPolynomialBasis_repr_apply, mvPolynomialBasis_apply] at h
    have h2 := congrArg (KaehlerDifferential.map k k (MvPolynomial (Fin n) k)
      (Localization.AtPrime q₀)) h
    rw [map_sum, KaehlerDifferential.map_D] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.map_smul, KaehlerDifferential.map_D]
    exact (algebraMap_smul (Localization.AtPrime q₀) (pderiv i p)
      (D k (Localization.AtPrime q₀)
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i)))).symm
  have himg : ∀ (a : (ResidueField (Localization.AtPrime q₀))) (j : Fin m),
      cotangentComplexBaseChange k (Localization.AtPrime q) (Localization.AtPrime q₀) (ResidueField (Localization.AtPrime q₀))
        (a ⊗ₜ[Localization.AtPrime q₀] F j) = ∑ i, (a * v j i) • w i := by
    intro a j
    rw [cotangentComplexBaseChange_tmul, kerToTensor_apply]
    show a • ((1 : (ResidueField (Localization.AtPrime q₀))) ⊗ₜ D k (Localization.AtPrime q₀) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (f j))) = _
    rw [hDf, tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have e1 : (1 : ResidueField (Localization.AtPrime q₀)) ⊗ₜ[Localization.AtPrime q₀]
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (pderiv i (f j)) •
          D k (Localization.AtPrime q₀)
            (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i))) =
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (pderiv i (f j)) •
          (1 : ResidueField (Localization.AtPrime q₀))) ⊗ₜ[Localization.AtPrime q₀]
          D k (Localization.AtPrime q₀)
            (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i)) :=
      (TensorProduct.smul_tmul (R := Localization.AtPrime q₀)
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (pderiv i (f j)))
        (1 : ResidueField (Localization.AtPrime q₀)) (D k (Localization.AtPrime q₀)
          (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (X i)))).symm
    rw [e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]
    rfl
  have hzero : ∀ (ι : Type) [Fintype ι] (a : ι → (ResidueField (Localization.AtPrime q₀))) (g : ι → Fin m),
      (∀ i, ∑ t, a t * v (g t) i = 0) →
        ∑ t, a t ⊗ₜ[Localization.AtPrime q₀] F (g t) = (0 : (ResidueField (Localization.AtPrime q₀)) ⊗[Localization.AtPrime q₀] _) := by
    intro ι _ a g h
    apply hinj
    rw [map_sum, map_zero]
    simp only [himg]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, h, zero_smul, Finset.sum_const_zero]
  -- the linear algebra
  obtain ⟨c, e, u, he, hu, hspan, hdet⟩ := exists_basis_minor v
  have hrel : ∀ ℓ, ∃ c' : Fin c → (ResidueField (Localization.AtPrime q₀)), (1 : (ResidueField (Localization.AtPrime q₀))) ⊗ₜ[Localization.AtPrime q₀] F ℓ = ∑ j, c' j ⊗ₜ[Localization.AtPrime q₀] F (e j) := by
    intro ℓ
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField (Localization.AtPrime q₀))).mp (hspan ℓ)
    refine ⟨c', ?_⟩
    have h := hzero (Unit ⊕ Fin c) (Sum.elim (fun _ ↦ 1) (fun j ↦ -c' j))
      (Sum.elim (fun _ ↦ ℓ) e) (by
        intro i
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, one_mul,
          neg_mul, Finset.sum_neg_distrib]
        rw [← hc']
        simp [Finset.sum_apply, v])
    rw [Fintype.sum_sum_type] at h
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, neg_tmul,
      Finset.sum_neg_distrib] at h
    rw [← sub_eq_zero, ← h, sub_eq_add_neg]
  -- Nakayama over the local ring `P`
  have : Module.Finite (Localization.AtPrime q₀)
      (RingHom.ker (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q))) :=
    Module.Finite.iff_fg.mpr hkerFG
  have hN : Submodule.span (Localization.AtPrime q₀) (Set.range (F ∘ e)) = ⊤ := by
    refine span_comp_eq_top_of_tmul F (fun x ↦ ?_) e hrel
    have hx : x.1 ∈ Ideal.span (Set.range fun j ↦
        algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime q₀) (f j)) := hkerspan ▸ x.2
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
    refine ⟨Finset.univ, b, Subtype.ext ?_⟩
    rw [← hb, Submodule.coe_sum]
    rfl
  -- clearing denominators
  have hloc : ∀ ℓ, ∃ aℓ ∉ q₀, aℓ * f ℓ ∈ Ideal.span (Set.range (f ∘ e)) := by
    intro ℓ
    have hℓ : F ℓ ∈ Submodule.span (Localization.AtPrime q₀) (Set.range (F ∘ e)) :=
      hN ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hℓ
    have h1 : algebraMap _ (Localization.AtPrime q₀) (f ℓ) ∈
        (Ideal.span (Set.range (f ∘ e))).map (algebraMap _ (Localization.AtPrime q₀)) := by
      have h2 := congrArg Subtype.val hb
      rw [Submodule.coe_sum] at h2
      rw [← show (F ℓ).1 = algebraMap _ (Localization.AtPrime q₀) (f ℓ) from rfl, ← h2]
      refine Ideal.sum_mem _ fun j _ ↦ ?_
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
    obtain ⟨⟨⟨y, hy⟩, ⟨s, hs⟩⟩, hys⟩ :=
      (IsLocalization.mem_map_algebraMap_iff q₀.primeCompl (Localization.AtPrime q₀)).mp h1
    have h3 : algebraMap _ (Localization.AtPrime q₀) (s * f ℓ - y) = 0 := by
      rw [map_sub, map_mul, mul_comm]
      exact sub_eq_zero.mpr hys
    obtain ⟨⟨t, ht⟩, htz⟩ := (IsLocalization.map_eq_zero_iff q₀.primeCompl _ _).mp h3
    refine ⟨t * s, (inferInstance : q₀.IsPrime).mul_notMem ht hs, ?_⟩
    have : t * s * f ℓ = t * y := by
      rw [mul_sub, sub_eq_zero] at htz
      rw [mul_assoc]
      exact htz
    rw [this]
    exact Ideal.mul_mem_left _ _ hy
  choose aℓ haℓ haℓf using hloc
  refine ⟨c, e, u, ∏ ℓ, aℓ ℓ, he, hu, ?_, fun ℓ ↦ ?_⟩
  · show (∏ ℓ, aℓ ℓ) * _ ∉ q₀
    refine (inferInstance : q₀.IsPrime).mul_notMem ?_ ?_
    · intro hmem
      obtain ⟨ℓ, _, hℓ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact haℓ ℓ hℓ
    · intro hmem
      apply hdet
      have hmax : algebraMap _ (Localization.AtPrime q₀)
          (Matrix.det (Matrix.of fun j l : Fin c ↦ pderiv (u l) (f (e j)))) ∈
            maximalIdeal (Localization.AtPrime q₀) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q₀ _).mpr hmem
      rw [← residue_eq_zero_iff, ← ResidueField.algebraMap_eq,
        ← RingHom.comp_apply, RingHom.map_det] at hmax
      exact hmax
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ ℓ), mul_assoc]
    exact Ideal.mul_mem_left _ _ (haℓf ℓ)

end Chart

end Langlands.CommutativeAlgebra.Popescu.Desing
