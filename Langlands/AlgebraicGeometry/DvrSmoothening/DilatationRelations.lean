import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationLocal
import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationResidue
import Langlands.AlgebraicGeometry.DvrSmoothening.GoodChart

/-! # Relations of `A` lie in the square of the centre, up to unit-valued multipliers and the
auxiliary relations -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- **Good relations at a point on a good centre.** Let `P = R[X₁, …, X_N] → A` be a
presentation of a finite type algebra over a discrete valuation ring, and `J ⊆ A` an ideal cut
out by points of ramification index one, with `A ⧸ J` smooth over the residue field and
`(A ⧸ J) ⊗ Ω_{A/R}` free. Let `A → R'` be a point of a local ring whose closed point lies on the
centre. Then there are relations `wₗ` of `A` and lifts `zⱼ` of elements of `J` whose differentials
are linearly independent at the closed point, such that:
* every relation `f` of `A` satisfies `e f ∈ (ϖ, z)² + (w)` for some `e` with unit value;
* every `x ∈ J` satisfies `e x ∈ (ϖ, z)` for some `e` with unit value.
This is the affine content of BLR §3.3, proof of Proposition 5 (printed p. 69). -/
theorem exists_dilatation_relations {R A R' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {ϖ : R}
    (hϖ : Irreducible ϖ) (J : Ideal A) (S : Set (Ideal A)) (hJ : J = sInf S)
    (hS : ∀ p ∈ S, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : A →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p)
    (hB : Algebra.Smooth (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] (A ⧸ J)))
    (hfree : Module.Free (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    [CommRing R'] [IsLocalRing R']
    {N : ℕ} [Algebra (MvPolynomial (Fin N) R) A] [IsScalarTower R (MvPolynomial (Fin N) R) A]
    (hsurj : Function.Surjective (algebraMap (MvPolynomial (Fin N) R) A))
    [Algebra A R'] [Algebra (MvPolynomial (Fin N) R) R']
    [IsScalarTower (MvPolynomial (Fin N) R) A R']
    (hJu : J ≤ (IsLocalRing.maximalIdeal R').comap (algebraMap A R')) :
    ∃ (n m : ℕ) (z : Fin n → MvPolynomial (Fin N) R) (w : Fin m → MvPolynomial (Fin N) R),
      (∀ l, algebraMap (MvPolynomial (Fin N) R) A (w l) = 0) ∧
      (∀ j, algebraMap (MvPolynomial (Fin N) R) A (z j) ∈ J) ∧
      LinearIndependent (IsLocalRing.ResidueField R')
        (fun k => (1 : IsLocalRing.ResidueField R') ⊗ₜ[MvPolynomial (Fin N) R]
          KaehlerDifferential.D R (MvPolynomial (Fin N) R) (Sum.elim z w k)) ∧
      (∀ f, algebraMap (MvPolynomial (Fin N) R) A f = 0 →
        ∃ e, IsUnit (algebraMap (MvPolynomial (Fin N) R) R' e) ∧
          e * f ∈ (Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔
            Ideal.span (Set.range z)) ^ 2 ⊔ Ideal.span (Set.range w)) ∧
      (∀ x ∈ J, ∃ e, IsUnit (algebraMap (MvPolynomial (Fin N) R) R' e) ∧
        algebraMap (MvPolynomial (Fin N) R) A e * x ∈
          Ideal.span {algebraMap R A ϖ} ⊔
            Ideal.span (Set.range fun j => algebraMap (MvPolynomial (Fin N) R) A (z j))) := by
  classical
  -- the maximal ideal of `R` maps into `J`
  have hmJ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R A r ∈ J := by
    intro r hr
    rw [hJ]
    refine Submodule.mem_sInf.mpr fun p hp => ?_
    obtain ⟨R'', _, _, _, _, _, ψ, -, hψ⟩ := hS p hp
    rw [← hψ, Ideal.mem_comap, AlgHom.commutes]
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap R R'') r ((IsLocalRing.mem_maximalIdeal r).mp hr))
  have hϖJ : algebraMap R A ϖ ∈ J :=
    hmJ ϖ ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)
  -- `A ⧸ J` as a smooth algebra over the residue field
  let ιk : IsLocalRing.ResidueField R →+* A ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (A ⧸ J))
      (fun r hr => Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ r hr))
  letI : Algebra (IsLocalRing.ResidueField R) (A ⧸ J) := ιk.toAlgebra
  have : IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  have : Algebra.FormallySmooth (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] (A ⧸ J)) := hB.formallySmooth
  have : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (A ⧸ J) :=
    Algebra.FormallySmooth.of_equiv (residueTensorEquiv (A ⧸ J))
  -- the residue field of `R'`
  let κB : A ⧸ J →+* IsLocalRing.ResidueField R' :=
    Ideal.Quotient.lift J (algebraMap A (IsLocalRing.ResidueField R'))
      (fun a ha => (IsLocalRing.residue_eq_zero_iff _).mpr (hJu ha))
  letI : Algebra (A ⧸ J) (IsLocalRing.ResidueField R') := κB.toAlgebra
  have : IsScalarTower A (A ⧸ J) (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- choice of `z` and `w`
  let d : MvPolynomial (Fin N) R → IsLocalRing.ResidueField R' ⊗[MvPolynomial (Fin N) R]
      Ω[MvPolynomial (Fin N) R⁄R] := fun p => (1 : _) ⊗ₜ KaehlerDifferential.D R _ p
  have : Module.Finite (IsLocalRing.ResidueField R')
      (IsLocalRing.ResidueField R' ⊗[MvPolynomial (Fin N) R] Ω[MvPolynomial (Fin N) R⁄R]) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis _
      (KaehlerDifferential.mvPolynomialBasis R (Fin N)))
  obtain ⟨n, m, z, w, hw, hz, hli, hspanI, hspanJ⟩ :=
    exists_extension (K := IsLocalRing.ResidueField R') d
    {f | algebraMap (MvPolynomial (Fin N) R) A f = 0}
    {f | algebraMap (MvPolynomial (Fin N) R) A f ∈ J}
    (fun f (hf : algebraMap _ A f = 0) => show algebraMap _ A f ∈ J by rw [hf]; exact J.zero_mem)
  have hzw : Sum.elim (d ∘ z) (d ∘ w) = d ∘ Sum.elim z w := by
    funext k; cases k <;> rfl
  have hw' : ∀ l, algebraMap (MvPolynomial (Fin N) R) A (w l) = 0 := hw
  have hz' : ∀ j, algebraMap (MvPolynomial (Fin N) R) A (z j) ∈ J := hz
  -- local generators of the centre
  let β0 : MvPolynomial (Fin N) R →ₐ[R] A ⧸ J :=
    (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin N) R) A)
  have hβ0 : Function.Surjective β0 := Ideal.Quotient.mk_surjective.comp hsurj
  have hβ0J : ∀ p, β0 p = 0 ↔ algebraMap (MvPolynomial (Fin N) R) A p ∈ J := fun p =>
    Ideal.Quotient.eq_zero_iff_mem
  have hκ : ∀ p, algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') p =
      κB (β0 p) := fun p => by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin N) R) A (IsLocalRing.ResidueField R')]
    rfl
  have hJP : ∀ j, algebraMap (MvPolynomial (Fin N) R) A j ∈ J →
      ∃ s, algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') s ≠ 0 ∧
        s * j ∈ Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔
          Ideal.span (Set.range (Sum.elim z w)) := by
    intro j hj
    refine exists_mul_mem_span_of_residue hϖ β0 hβ0 κB hκ (Sum.elim z w) ?_ ?_ j
      ((hβ0J j).mpr hj)
    · rintro (i | l)
      · exact (hβ0J _).mpr (hz' i)
      · exact (hβ0J _).mpr (by rw [Sum.elim_inr, hw' l]; exact J.zero_mem)
    · intro p hp
      have := hspanJ p ((hβ0J p).mp hp)
      rw [hzw] at this
      exact this
  have hunit : ∀ s, algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') s ≠ 0 →
      IsUnit (algebraMap (MvPolynomial (Fin N) R) R' s) := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin N) R) R'
      (IsLocalRing.ResidueField R')] at hs
    by_contra h
    exact hs ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  have hsplit : Ideal.span (Set.range (Sum.elim z w)) =
      Ideal.span (Set.range z) ⊔ Ideal.span (Set.range w) := by
    rw [Set.Sum.elim_range, Ideal.span_union]
  refine ⟨n, m, z, w, hw', hz', ?_, ?_, ?_⟩
  · rw [hzw] at hli; exact hli
  · -- the relations lie in `(ϖ, z)² + (w)` up to units
    intro f hf
    set J0 := Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔ Ideal.span (Set.range z)
      with hJ0
    set Wd := Ideal.span (Set.range w) with hWd
    have hJ0J0W : J0 * (J0 ⊔ Wd) ≤ J0 ^ 2 ⊔ Wd := by
      rw [Ideal.mul_sup, pow_two]
      exact sup_le_sup_left Ideal.mul_le_right _
    have hWdker : ∀ q ∈ Wd, algebraMap (MvPolynomial (Fin N) R) A q = 0 := by
      intro q hq
      have : Wd ≤ RingHom.ker (algebraMap (MvPolynomial (Fin N) R) A) :=
        Ideal.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hw' l)
      exact this hq
    have hJ0J : J0 ≤ J.comap (algebraMap (MvPolynomial (Fin N) R) A) := by
      refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro _ rfl
        rw [SetLike.mem_coe, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact hϖJ
      · rintro _ ⟨j, rfl⟩
        exact hz' j
    have hQJ : J0 ^ 2 ⊔ Wd ≤ (J ^ 2).comap (algebraMap (MvPolynomial (Fin N) R) A) := by
      refine sup_le ((Ideal.pow_right_mono hJ0J 2).trans (Ideal.le_comap_pow _ 2)) ?_
      intro q hq
      rw [Ideal.mem_comap, hWdker q hq]
      exact Ideal.zero_mem _
    obtain ⟨s, hs, hsf⟩ := hJP f (by rw [hf]; exact J.zero_mem)
    rw [hsplit, ← sup_assoc] at hsf
    obtain ⟨a1, ha1, a2, ha2, h12⟩ := Submodule.mem_sup.mp hsf
    obtain ⟨b1, hb1, b2, hb2, hb12⟩ := Submodule.mem_sup.mp ha1
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hb1
    obtain ⟨gz, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb2
    -- the differential relation in `(A ⧸ J) ⊗ Ω_A`
    let δ : MvPolynomial (Fin N) R → (A ⧸ J) ⊗[A] Ω[A⁄R] :=
      fun p => (1 : A ⧸ J) ⊗ₜ KaehlerDifferential.D R A (algebraMap (MvPolynomial (Fin N) R) A p)
    have hδmul : ∀ p q, δ (p * q) = β0 p • δ q + β0 q • δ p := by
      intro p q
      simp only [δ, map_mul]
      rw [one_tmul_D_mul]
      rfl
    have hδadd : ∀ p q, δ (p + q) = δ p + δ q := fun p q => by
      simp only [δ, map_add, TensorProduct.tmul_add]
    have hδsum : ∀ (q : Fin n → MvPolynomial (Fin N) R), δ (∑ j, q j) = ∑ j, δ (q j) :=
      fun q => by simp only [δ, map_sum, TensorProduct.tmul_sum]
    have hδϖ : δ (algebraMap R (MvPolynomial (Fin N) R) ϖ) = 0 := by
      simp only [δ, ← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap,
        TensorProduct.tmul_zero]
    have hβϖ : β0 (algebraMap R (MvPolynomial (Fin N) R) ϖ) = 0 := by
      rw [hβ0J, ← IsScalarTower.algebraMap_apply]; exact hϖJ
    have hβz : ∀ j, β0 (z j) = 0 := fun j => (hβ0J _).mpr (hz' j)
    have hδa2 : δ a2 = 0 := by
      simp only [δ, hWdker a2 ha2, map_zero, TensorProduct.tmul_zero]
    have hterm : ∀ j, δ (gz j * z j) = β0 (gz j) • δ (z j) := fun j => by
      rw [hδmul, hβz j, zero_smul, add_zero]
    have hsum : ∑ j, β0 (gz j) • δ (z j) = 0 := by
      have h0 : δ (s * f) = 0 := by
        simp only [δ, map_mul, hf, mul_zero, map_zero, TensorProduct.tmul_zero]
      rw [← h12, ← hb12, hδadd, hδadd, hδa2, add_zero, hδmul, hδϖ, hβϖ, smul_zero, zero_smul,
        add_zero, zero_add, hδsum] at h0
      simpa only [hterm] using h0
    -- independence of the `dzⱼ` on the centre
    have hliB : LinearIndependent (IsLocalRing.ResidueField R')
        (fun j => (1 : IsLocalRing.ResidueField R') ⊗ₜ[A ⧸ J] δ (z j)) := by
      let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J)
        (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField R') Ω[A⁄R]
      let ψK := tensorKaehlerMap R (IsLocalRing.ResidueField R') (P := MvPolynomial (Fin N) R)
        (S := A)
      have hcomp : ∀ j, cb ((1 : IsLocalRing.ResidueField R') ⊗ₜ[A ⧸ J] δ (z j)) =
          ψK (d (z j)) := by
        intro j
        simp only [cb, δ, ψK, d, tensorKaehlerMap_tmul_D,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
      apply LinearIndependent.of_comp cb.toLinearMap
      have hfun : (cb.toLinearMap ∘ fun j => (1 : IsLocalRing.ResidueField R') ⊗ₜ[A ⧸ J] δ (z j)) =
          fun j => ψK (d (z j)) := funext hcomp
      rw [hfun, Fintype.linearIndependent_iff]
      intro c hc
      have hker : ∑ j, c j • d (z j) ∈ LinearMap.ker ψK := by
        rw [LinearMap.mem_ker, map_sum]
        simpa only [map_smul] using hc
      rw [ker_tensorKaehlerMap R (IsLocalRing.ResidueField R') hsurj] at hker
      have hle : Submodule.span (IsLocalRing.ResidueField R') (Set.range fun g :
          RingHom.ker (algebraMap (MvPolynomial (Fin N) R) A) =>
            (1 : IsLocalRing.ResidueField R') ⊗ₜ[MvPolynomial (Fin N) R]
              KaehlerDifferential.D R (MvPolynomial (Fin N) R) (g : MvPolynomial (Fin N) R)) ≤
          Submodule.span (IsLocalRing.ResidueField R') (Set.range (d ∘ w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨g, hg⟩, rfl⟩
        exact hspanI g hg
      obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hle hker)
      have := Fintype.linearIndependent_iff.mp hli (Sum.elim c (fun l => -e l)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, neg_smul,
          Finset.sum_neg_distrib]
        rw [← he]
        simp only [Function.comp_apply, add_neg_cancel])
      intro j
      exact this (Sum.inl j)
    obtain ⟨t, ht, htb⟩ := exists_mul_eq_zero_of_linearIndependent (fun j => δ (z j)) hliB
      (fun j => β0 (gz j)) hsum
    obtain ⟨t', rfl⟩ := hβ0 t
    have ht' : algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') t' ≠ 0 := by
      rw [hκ]; exact ht
    have hJ1 : ∀ j, ∃ sj, algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') sj ≠ 0 ∧
        sj * (t' * gz j) ∈ Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔
          Ideal.span (Set.range (Sum.elim z w)) := fun j =>
      hJP _ (by rw [← hβ0J, map_mul]; exact htb j)
    choose sj hsj hmemj using hJ1
    set s' := ∏ j, sj j with hs'def
    have hs' : algebraMap (MvPolynomial (Fin N) R) (IsLocalRing.ResidueField R') s' ≠ 0 := by
      rw [hs'def, map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => hsj j
    have hmem' : ∀ j, s' * (t' * gz j) ∈
        Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔
          (Ideal.span (Set.range z) ⊔ Ideal.span (Set.range w)) := by
      intro j
      rw [← hsplit, hs'def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm (sj j),
        mul_assoc]
      exact Ideal.mul_mem_left _ _ (hmemj j)
    have hdec : ∀ j, ∃ a r, r ∈ Ideal.span (Set.range z) ⊔ Ideal.span (Set.range w) ∧
        s' * (t' * gz j) = a * algebraMap R (MvPolynomial (Fin N) R) ϖ + r := by
      intro j
      obtain ⟨b, hb, r, hr, h⟩ := Submodule.mem_sup.mp (hmem' j)
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      exact ⟨a, r, hr, h.symm⟩
    choose a r hr hdec using hdec
    set G := s' * t' * g + ∑ j, a j * z j with hGdef
    set rest := ∑ j, z j * r j + s' * t' * a2 with hrestdef
    have hid : s' * t' * (s * f) = algebraMap R (MvPolynomial (Fin N) R) ϖ * G + rest := by
      have hj : ∀ j, s' * t' * (gz j * z j) =
          algebraMap R (MvPolynomial (Fin N) R) ϖ * (a j * z j) + z j * r j := fun j => by
        have := hdec j
        linear_combination (z j) * this
      rw [← h12, ← hb12, mul_add, mul_add, Finset.mul_sum,
        Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib]
      simp only [hGdef, hrestdef, mul_add, Finset.mul_sum]
      ring
    have hrest : rest ∈ J0 ^ 2 ⊔ Wd := by
      refine add_mem (sum_mem fun j _ => hJ0J0W (Ideal.mul_mem_mul ?_ ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ ha2))
      · exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
      · exact (sup_le_sup_right (le_sup_right : Ideal.span (Set.range z) ≤ J0) Wd :
          _ ≤ J0 ⊔ Wd) (hr j)
    have hπG : algebraMap R A ϖ * algebraMap (MvPolynomial (Fin N) R) A G ∈ J ^ 2 := by
      have h1 : algebraMap (MvPolynomial (Fin N) R) A (s' * t' * (s * f)) = 0 := by
        simp only [map_mul, hf, mul_zero]
      rw [hid, map_add, map_mul, ← IsScalarTower.algebraMap_apply] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      exact (J ^ 2).neg_mem (hQJ hrest)
    have hGJ := mem_of_mul_mem_sq hϖ J S hJ hS _ hπG
    obtain ⟨s'', hs'', hmemG⟩ := hJP G hGJ
    rw [hsplit, ← sup_assoc] at hmemG
    have hϖG : algebraMap R (MvPolynomial (Fin N) R) ϖ * (s'' * G) ∈ J0 ^ 2 ⊔ Wd :=
      hJ0J0W (Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hmemG)
    refine ⟨s'' * (s' * t') * s, ?_, ?_⟩
    · rw [map_mul, map_mul, map_mul]
      exact ((hunit _ hs'').mul ((hunit _ hs').mul (hunit _ ht'))).mul (hunit _ hs)
    · have : s'' * (s' * t') * s * f =
          algebraMap R (MvPolynomial (Fin N) R) ϖ * (s'' * G) + s'' * rest := by
        rw [mul_assoc (s'' * (s' * t')) s f, mul_assoc s'', hid]
        ring
      rw [this]
      exact add_mem hϖG (Ideal.mul_mem_left _ _ hrest)
  · intro x hx
    obtain ⟨x', rfl⟩ := hsurj x
    obtain ⟨s, hs, hmem⟩ := hJP x' hx
    refine ⟨s, hunit s hs, ?_⟩
    rw [← map_mul]
    have hle : Ideal.span {algebraMap R (MvPolynomial (Fin N) R) ϖ} ⊔
        Ideal.span (Set.range (Sum.elim z w)) ≤
        (Ideal.span {algebraMap R A ϖ} ⊔ Ideal.span (Set.range fun j =>
          algebraMap (MvPolynomial (Fin N) R) A (z j))).comap
          (algebraMap (MvPolynomial (Fin N) R) A) := by
      refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro _ rfl
        rw [SetLike.mem_coe, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      · rintro _ ⟨i | l, rfl⟩
        · exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
        · rw [SetLike.mem_coe, Ideal.mem_comap, Sum.elim_inr, hw' l]
          exact Ideal.zero_mem _
    exact hle hmem

end Langlands.AlgebraicGeometry.DvrSmoothening
