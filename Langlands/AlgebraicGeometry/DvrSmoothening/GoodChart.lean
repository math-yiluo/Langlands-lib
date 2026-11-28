import Langlands.AlgebraicGeometry.DvrSmoothening.GoodChartAlgebra
import Langlands.AlgebraicGeometry.DvrSmoothening.GoodChartStatement

/-! # Closures of points of ramification index one have good charts -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Localization commutes with quotients: if `A'` is the localization of `A` away from `s`, then
`A' ⧸ J A'` is the localization of `A ⧸ J` away from the class of `s`. -/
theorem isLocalization_away_quotient {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (s : A) [IsLocalization.Away s A'] (J : Ideal A) :
    letI := (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A')
      Ideal.le_comap_map).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk J s) (A' ⧸ J.map (algebraMap A A')) := by
  letI := (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A')
      Ideal.le_comap_map).toAlgebra
  have halg : ∀ a : A, algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A'))
      (Ideal.Quotient.mk J a) = Ideal.Quotient.mk _ (algebraMap A A' a) := fun a => rfl
  apply IsLocalization.Away.mk
  · rw [halg]
    exact (IsLocalization.Away.algebraMap_isUnit s).map (Ideal.Quotient.mk _)
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s y
    refine ⟨n, Ideal.Quotient.mk J a, ?_⟩
    rw [halg, halg, ← map_pow, ← map_mul, ha]
  · intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [halg, halg, Ideal.Quotient.eq, ← map_sub] at hab
    obtain ⟨⟨j, m⟩, hjm⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) A').mp hab
    simp only at hjm
    rw [← map_mul] at hjm
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) A').mp hjm
    obtain ⟨n₁, hn₁⟩ := c.2
    obtain ⟨n₂, hn₂⟩ := (m : Submonoid.powers s).2
    simp only at hn₁ hn₂
    refine ⟨n₁ + n₂, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, ← map_pow, ← map_sub, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    have : s ^ (n₁ + n₂) * (x - y) = (c : A) * (j : A) := by
      rw [pow_add, hn₁, hn₂, ← hc]
      ring
    rw [this]
    exact J.mul_mem_left _ j.2

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- For an algebra `Q` over the residue field `k` of `R`, the base change `k ⊗_R Q` is `Q`. -/
noncomputable def residueTensorEquiv (Q : Type*) [CommRing Q] [Algebra R Q]
    [Algebra (IsLocalRing.ResidueField R) Q] [IsScalarTower R (IsLocalRing.ResidueField R) Q] :
    IsLocalRing.ResidueField R ⊗[R] Q ≃ₐ[IsLocalRing.ResidueField R] Q := by
  refine AlgEquiv.ofBijective (Algebra.TensorProduct.lift
    (Algebra.ofId (IsLocalRing.ResidueField R) Q) (AlgHom.id R Q)
    (fun _ _ => Commute.all _ _)) ⟨?_, fun q => ⟨1 ⊗ₜ q, by simp⟩⟩
  have hinv : ∀ x : IsLocalRing.ResidueField R ⊗[R] Q,
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (Algebra.TensorProduct.lift
        (Algebra.ofId (IsLocalRing.ResidueField R) Q) (AlgHom.id R Q)
        (fun _ _ => Commute.all _ _) x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c q =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      simp only [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_id, id_eq]
      have e : algebraMap (IsLocalRing.ResidueField R) Q (IsLocalRing.residue R r) =
          algebraMap R Q r := by
        rw [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) Q,
          IsLocalRing.ResidueField.algebraMap_eq]
      rw [e, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        IsLocalRing.ResidueField.algebraMap_eq]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
  intro x y hxy
  rw [← hinv x, ← hinv y, hxy]

end Residue

/-- The closure of a nonempty family of points of ramification index one has a good chart:
BLR §3.3, Lemma 4, with the density of the locus of §3.4. -/
theorem goodChartStatement : GoodChartStatement.{u} := by
  intro R A _ _ _ _ _ _ J S hJ hSne hpts
  classical
  let k := IsLocalRing.ResidueField R
  -- The maximal ideal of `R` maps into `J`.
  have hmJ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R A r ∈ J := by
    intro r hr
    rw [hJ]
    refine Submodule.mem_sInf.mpr fun p hp => ?_
    obtain ⟨R'', _, _, _, _, _, ψ, -, hψ⟩ := hpts p hp
    rw [← hψ, Ideal.mem_comap, AlgHom.commutes]
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap R R'') r ((IsLocalRing.mem_maximalIdeal r).mp hr))
  -- `A ⧸ J` as an algebra over the residue field.
  let ι : k →+* A ⧸ J := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (A ⧸ J))
    (fun r hr => Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ r hr))
  letI : Algebra k (A ⧸ J) := ι.toAlgebra
  have : IsScalarTower R k (A ⧸ J) := IsScalarTower.of_algebraMap_eq fun r => rfl
  have : Algebra.FiniteType k (A ⧸ J) := Algebra.FiniteType.of_restrictScalars_finiteType R k _
  -- `A ⧸ J` is nonzero.
  obtain ⟨p₀, hp₀⟩ := hSne
  have hJp₀ : J ≤ p₀ := hJ ▸ sInf_le hp₀
  have : J ≠ ⊤ := by
    obtain ⟨R'', _, _, _, _, _, ψ, -, hψ⟩ := hpts p₀ hp₀
    have : p₀.IsPrime := hψ ▸ Ideal.comap_isPrime _ _
    exact fun h => this.ne_top (top_le_iff.mp (h ▸ hJp₀))
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr this
  -- `A ⧸ J` is geometrically reduced.
  choose R'' iR iD iV iA iL ψ hram hψ using fun p : S => hpts p.1 p.2
  let f : ∀ p : S, A ⧸ J →ₐ[k] IsLocalRing.ResidueField (R'' p) := fun p =>
    { toRingHom := Ideal.Quotient.lift J ((IsLocalRing.residue (R'' p)).comp (ψ p).toRingHom)
        (by
          intro a ha
          have ha' : a ∈ sInf S := hJ ▸ ha
          have : a ∈ p.1 := Submodule.mem_sInf.mp ha' p.1 p.2
          rw [← hψ p] at this
          exact (IsLocalRing.residue_eq_zero_iff _).mpr this)
      commutes' := by
        intro c
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
        change IsLocalRing.residue (R'' p) (ψ p (algebraMap R A r)) = _
        rw [AlgHom.commutes]
        rfl }
  have : ∀ p : S, Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (R'' p)) :=
    fun p => (hram p).2
  have : Algebra.IsGeometricallyReduced k (A ⧸ J) := by
    refine isGeometricallyReduced_of_forall_eq_zero (fun p : S => IsLocalRing.ResidueField (R'' p))
      f fun a ha => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hJ]
    refine Submodule.mem_sInf.mpr fun p hp => ?_
    have := ha ⟨p, hp⟩
    change IsLocalRing.residue _ (ψ ⟨p, hp⟩ x) = 0 at this
    rw [IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hψ] at this
    exact this
  -- Generic smoothness and freeness.
  obtain ⟨q, hq, r₁, hr₁, r₂, hr₂, hfree₁, hsm₂⟩ :=
    exists_free_smooth (k := k) (B := A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I := J) (r₁ * r₂)
  refine ⟨s, fun hsJ => ?_, ?_⟩
  · have : r₁ * r₂ ∈ q := by
      rw [← hs, Ideal.Quotient.eq_zero_iff_mem.mpr hsJ]
      exact q.zero_mem
    exact (hq.mem_or_mem this).elim hr₁ hr₂
  intro A' _ _ _ _ _
  letI : Algebra (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) :=
    (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map).toAlgebra
  have hloc : IsLocalization.Away (r₁ * r₂) (A' ⧸ J.map (algebraMap A A')) :=
    hs ▸ isLocalization_away_quotient s J
  have hAQ : IsScalarTower A (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  letI : Algebra k (A' ⧸ J.map (algebraMap A A')) :=
    ((algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A'))).comp (algebraMap k (A ⧸ J))).toAlgebra
  have : IsScalarTower k (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  have : IsScalarTower R k (A' ⧸ J.map (algebraMap A A')) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change Ideal.Quotient.mk _ (algebraMap R A' r) =
      Ideal.Quotient.mk _ (algebraMap A A' (algebraMap R A r))
    rw [← IsScalarTower.algebraMap_apply]
  -- Smoothness.
  have : Algebra.FinitePresentation k (A ⧸ J) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsmr : Algebra.Smooth k (Localization.Away (r₁ * r₂)) := by
    rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
    exact fun x hx => (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm₂)
      (PrimeSpectrum.basicOpen_mul_le_right r₁ r₂ hx)
  have hsmQ : Algebra.Smooth k (A' ⧸ J.map (algebraMap A A')) :=
    Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (r₁ * r₂))
      (Localization.Away (r₁ * r₂)) (A' ⧸ J.map (algebraMap A A'))).restrictScalars k)
  refine ⟨Algebra.Smooth.of_equiv (residueTensorEquiv (A' ⧸ J.map (algebraMap A A'))).symm, ?_⟩
  -- Freeness.
  have hu : IsUnit (algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) r₁) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A' ⧸ J.map (algebraMap A A')) (r₁ * r₂)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  letI : Algebra (Localization.Away r₁) (A' ⧸ J.map (algebraMap A A')) :=
    (IsLocalization.Away.lift r₁ hu).toAlgebra
  have : IsScalarTower (A ⧸ J) (Localization.Away r₁) (A' ⧸ J.map (algebraMap A A')) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r₁ hu x).symm
  have : Algebra.FormallyEtale A A' := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
  let e1 : A' ⊗[A] Ω[A⁄R] ≃ₗ[A'] Ω[A'⁄R] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A A').equiv
  let e2 : (A' ⧸ J.map (algebraMap A A')) ⊗[A'] (A' ⊗[A] Ω[A⁄R]) ≃ₗ[A' ⧸ J.map (algebraMap A A')]
      (A' ⧸ J.map (algebraMap A A')) ⊗[A'] Ω[A'⁄R] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e1
  let e3 := TensorProduct.AlgebraTensorModule.cancelBaseChange A A'
    (A' ⧸ J.map (algebraMap A A')) (A' ⧸ J.map (algebraMap A A')) Ω[A⁄R]
  let e4 := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J)
    (A' ⧸ J.map (algebraMap A A')) (A' ⧸ J.map (algebraMap A A')) Ω[A⁄R]
  let e5 := TensorProduct.AlgebraTensorModule.cancelBaseChange (A ⧸ J) (Localization.Away r₁)
    (A' ⧸ J.map (algebraMap A A')) (A' ⧸ J.map (algebraMap A A')) ((A ⧸ J) ⊗[A] Ω[A⁄R])
  let e6 := LocalizedModule.equivTensorProduct (Submonoid.powers r₁) ((A ⧸ J) ⊗[A] Ω[A⁄R])
  have : Module.Free (Localization.Away r₁)
      (Localization.Away r₁ ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R])) := Module.Free.of_equiv e6
  have : Module.Free (A' ⧸ J.map (algebraMap A A')) ((A' ⧸ J.map (algebraMap A A')) ⊗[Localization.Away r₁]
      (Localization.Away r₁ ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R]))) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis _ (Module.Free.chooseBasis _ _))
  exact Module.Free.of_equiv (e5.trans (e4.trans (e3.symm.trans e2)))

end Langlands.AlgebraicGeometry.DvrSmoothening
