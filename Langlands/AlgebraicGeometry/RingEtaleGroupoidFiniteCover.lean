import Langlands.AlgebraicGeometry.RingEtaleGroupoidStableSubalgebra

/-! # Finite surjective covers at finitely generated levels

Let `ψ : B →ₐ[B₀] B'` be an equivariant map of algebras with multiplicative coactions of a
ring étale groupoid `t₀ : B₀ →+* C₀`, where `B₀` is Noetherian, `ψ` is finite and the kernel
of `ψ` is nil. For every finite subset `s ⊆ B'` there are finitely generated stable
subalgebras `D ⊆ B` and `D' ⊆ B'` with `ψ(D) ⊆ D'` and `s ⊆ D'`, such that the restriction
`D → D'` of `ψ` is finite and induces a surjection of prime spectra. This is the ring form
of the third step of the proof of Stacks Project Lemma 70.15.1 (Tag 07VS).
-/

universe u

open TensorProduct Polynomial

namespace Langlands.AlgebraicGeometry

namespace RingEtaleGroupoid

/-- If `PrimeSpectrum.comap ψ` is surjective, the kernel of `ψ` consists of nilpotents. -/
theorem ker_le_nilradical_of_comap_surjective {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (h : Function.Surjective (PrimeSpectrum.comap ψ)) :
    RingHom.ker ψ ≤ nilradical R := by
  intro x hx
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  obtain ⟨q, hq⟩ := h ⟨p, hp⟩
  have hxq : x ∈ (PrimeSpectrum.comap ψ q).asIdeal := by
    change ψ x ∈ q.asIdeal
    rw [RingHom.mem_ker.mp hx]
    exact q.asIdeal.zero_mem
  rw [hq] at hxq
  exact hxq

/-- An integral ring map whose kernel consists of nilpotents induces a surjection of prime
spectra (lying over). -/
theorem comap_surjective_of_isIntegral {R S : Type u} [CommRing R] [CommRing S] (ψ : R →+* S)
    (hint : ψ.IsIntegral) (hker : RingHom.ker ψ ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap ψ) := by
  let := ψ.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  intro p
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal
    (⊥ : Ideal S) (by
      intro x hx
      have hx' : x ∈ RingHom.ker ψ := by
        simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at hx
        exact hx
      exact nilradical_le_prime p.asIdeal (hker hx'))
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀] [Algebra B₀ C₀] {t₀ : B₀ →+* C₀}

theorem map_map_apply {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra B₀ B] [Algebra B₀ B'] [Algebra B₀ B''] (ψ : B' →ₐ[B₀] B'') (φ : B →ₐ[B₀] B')
    (z : C₀ ⊗[B₀] B) :
    Algebra.TensorProduct.map (AlgHom.id B₀ C₀) ψ (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ z) =
      Algebra.TensorProduct.map (AlgHom.id B₀ C₀) (ψ.comp φ) z := by
  rw [Algebra.TensorProduct.map_id_comp]
  rfl

theorem lTensor_comp_mem_range {B' N : Type u} [CommRing B'] [CommRing N] [Algebra B₀ B']
    [Algebra B₀ N] (S : Subalgebra B₀ B') (k : N →ₐ[B₀] S) (w : C₀ ⊗[B₀] N) :
    LinearMap.lTensor C₀ (S.val.comp k).toLinearMap w ∈
      LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap) := by
  refine ⟨LinearMap.lTensor C₀ k.toLinearMap w, ?_⟩
  change LinearMap.lTensor C₀ S.val.toLinearMap (LinearMap.lTensor C₀ k.toLinearMap w) = _
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

open GroupoidCoaction

variable {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B₀ B] [Algebra B₀ B']

/-- The restriction of an equivariant map to stable subalgebras is equivariant for the
restricted coactions. -/
theorem subalgebraCoaction_map (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ B)
    (θ' : GroupoidCoaction t₀ B') (ψ : B →ₐ[B₀] B')
    (hψ : ∀ b, θ'.coaction (ψ b) = Algebra.TensorProduct.map (AlgHom.id B₀ C₀) ψ (θ.coaction b))
    {D : Subalgebra B₀ B} {D' : Subalgebra B₀ B'} (hD : θ.IsStableSubalgebra D)
    (hD' : θ'.IsStableSubalgebra D') (φ : D →ₐ[B₀] D') (hφ : ∀ d, (φ d : B') = ψ d) (d : D) :
    Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ ((hE₀.subalgebraCoaction θ D hD).coaction d) =
      (hE₀.subalgebraCoaction θ' D' hD').coaction (φ d) := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) D'.val : C₀ ⊗[B₀] D' → C₀ ⊗[B₀] B') := by
    intro x y hxy
    apply hE₀.lTensor_val_injective D'
    rw [lTensor_eq_map, lTensor_eq_map, hxy]
  apply hinj
  have hcomp : D'.val.comp φ = ψ.comp D.val := AlgHom.ext fun d => hφ d
  rw [map_map_apply, hcomp, ← map_map_apply, subalgebraCoaction_val, subalgebraCoaction_val,
    ← hψ]
  exact congrArg θ'.coaction (hφ d).symm

/-- Finite surjective covers at finitely generated stable levels. -/
theorem exists_finite_level [IsNoetherianRing B₀] (hE₀ : RingEtaleGroupoid t₀)
    (θ : GroupoidCoaction t₀ B) (hθ : θ.IsMultiplicative) (θ' : GroupoidCoaction t₀ B')
    (hθ' : θ'.IsMultiplicative) (ψ : B →ₐ[B₀] B')
    (hψ : ∀ b, θ'.coaction (ψ b) = Algebra.TensorProduct.map (AlgHom.id B₀ C₀) ψ (θ.coaction b))
    (hfin : (ψ : B →+* B').Finite) (hker : RingHom.ker (ψ : B →+* B') ≤ nilradical B)
    (s : Finset B') :
    ∃ (D : Subalgebra B₀ B) (D' : Subalgebra B₀ B') (_ : θ.IsStableSubalgebra D)
      (_ : θ'.IsStableSubalgebra D') (φ : D →ₐ[B₀] D'),
      D.FG ∧ (s : Set B') ⊆ D' ∧ (∀ d, (φ d : B') = ψ d) ∧ (φ : D →+* D').Finite ∧
        Function.Surjective (PrimeSpectrum.comap (φ : D →+* D')) := by
  classical
  obtain ⟨F, ⟨Y, hY⟩, hsF, hFst⟩ := hE₀.exists_fg_stableSubalgebra θ' hθ' s
  have hint : ∀ y : B', ∃ P : B[X], P.Monic ∧ P.eval₂ (ψ : B →+* B') y = 0 :=
    fun y => hfin.to_isIntegral y
  choose P hPmon hProot using hint
  obtain ⟨D, ⟨G, hG⟩, hCoef, hDst⟩ :=
    hE₀.exists_fg_stableSubalgebra θ hθ (Y.biUnion fun y => (P y).coeffs)
  let X : Set B' := (ψ '' (D : Set B)) ∪ (F : Set B')
  let D' : Subalgebra B₀ B' := Algebra.adjoin B₀ X
  have hFD' : F ≤ D' := fun x hx => Algebra.subset_adjoin (Or.inr hx)
  let φ : D →ₐ[B₀] D' := (ψ.comp D.val).codRestrict D'
    (fun d => Algebra.subset_adjoin (Or.inl ⟨d, d.2, rfl⟩))
  have hφ : ∀ d, (φ d : B') = ψ d := fun _ => rfl
  have hD'st : θ'.IsStableSubalgebra D' := by
    apply isStableSubalgebra_adjoin θ' hθ' X
    rintro x (⟨d, hd, rfl⟩ | hx)
    · obtain ⟨w, hw⟩ := hDst ⟨d, hd⟩
      change LinearMap.lTensor C₀ D.val.toLinearMap w = θ.coaction d at hw
      rw [hψ, ← hw, lTensor_eq_map, map_map_apply, ← lTensor_eq_map]
      have hcomp : ψ.comp D.val = D'.val.comp φ := AlgHom.ext fun _ => rfl
      rw [hcomp]
      exact lTensor_comp_mem_range D' φ w
    · obtain ⟨w, hw⟩ := hFst ⟨x, hx⟩
      change LinearMap.lTensor C₀ F.val.toLinearMap w = θ'.coaction x at hw
      rw [← hw]
      have hcomp : F.val = D'.val.comp (Subalgebra.inclusion hFD') := AlgHom.ext fun _ => rfl
      rw [hcomp]
      exact lTensor_comp_mem_range D' (Subalgebra.inclusion hFD') w
  have hD'eq : D' = Algebra.adjoin B₀ ((G.image ψ ∪ Y : Finset B') : Set B') := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro x (⟨d, hd, rfl⟩ | hx)
      · rw [← hG] at hd
        have hmem : ψ d ∈ (Algebra.adjoin B₀ (G : Set B)).map ψ := ⟨d, hd, rfl⟩
        rw [AlgHom.map_adjoin] at hmem
        refine Algebra.adjoin_mono ?_ hmem
        intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
          Finset.mem_coe]
        exact Or.inl ⟨g, Finset.mem_coe.mp hg, rfl⟩
      · rw [← hY] at hx
        refine Algebra.adjoin_mono ?_ hx
        intro y hy
        simp [hy]
    · rw [Algebra.adjoin_le_iff]
      intro x hx
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at hx
      rcases hx with ⟨g, hg, rfl⟩ | hy
      · exact Algebra.subset_adjoin (Or.inl ⟨g, hG ▸ Algebra.subset_adjoin hg, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inr (hY ▸ Algebra.subset_adjoin hy))
  let _ : Algebra D D' := (φ : D →+* D').toAlgebra
  have : IsScalarTower B₀ D D' := IsScalarTower.of_algebraMap_eq (fun b => (φ.commutes b).symm)
  have hFT : Algebra.FiniteType B₀ D' :=
    (Subalgebra.fg_iff_finiteType D').mp ⟨_, hD'eq.symm⟩
  have : Algebra.FiniteType D D' := Algebra.FiniteType.of_restrictScalars_finiteType B₀ D D'
  have hYint : ∀ y ∈ Y, ∀ hy : y ∈ D', IsIntegral D (⟨y, hy⟩ : D') := by
    intro y hyY hy
    have hlifts : P y ∈ Polynomial.lifts (D.val : D →+* B) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : (P y).coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact ⟨⟨(P y).coeff n, hCoef (Finset.mem_biUnion.mpr
          ⟨y, hyY, Polynomial.coeff_mem_coeffs hn⟩)⟩, rfl⟩
    obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPmon y)
    refine ⟨q, hqmon, ?_⟩
    apply Subtype.val_injective
    change (D'.val : D' →+* B') (Polynomial.eval₂ (algebraMap D D') ⟨y, hy⟩ q) = 0
    rw [Polynomial.hom_eval₂]
    have hc : (D'.val : D' →+* B').comp (algebraMap D D') = (ψ : B →+* B').comp D.val := rfl
    rw [hc, ← Polynomial.eval₂_map, hq]
    exact hProot y
  have : Algebra.IsIntegral D D' := by
    let I := integralClosure D D'
    let K : Subalgebra B₀ B' := (I.restrictScalars B₀).map D'.val
    have hK : D' ≤ K := by
      rw [hD'eq, Algebra.adjoin_le_iff]
      intro x hx
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at hx
      rcases hx with ⟨g, hg, rfl⟩ | hy
      · refine ⟨algebraMap D D' ⟨g, hG ▸ Algebra.subset_adjoin hg⟩, ?_, rfl⟩
        exact isIntegral_algebraMap
      · have hyD' : x ∈ D' := hD'eq ▸ Algebra.subset_adjoin (by simp [hy])
        exact ⟨⟨x, hyD'⟩, hYint x hy hyD', rfl⟩
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz, hzx⟩ := hK x.2
    have : z = x := Subtype.val_injective hzx
    rw [← this]
    exact hz
  have hfinφ : (φ : D →+* D').Finite := Algebra.IsIntegral.finite
  refine ⟨D, D', hDst, hD'st, φ, ⟨G, hG⟩, fun x hx => hFD' (hsF hx), hφ, hfinφ, ?_⟩
  apply comap_surjective_of_isIntegral _ hfinφ.to_isIntegral
  intro d hd
  have hψd : ψ d = 0 := by
    rw [← hφ d]
    exact congrArg Subtype.val (RingHom.mem_ker.mp hd)
  obtain ⟨n, hn⟩ := (mem_nilradical).mp (hker (RingHom.mem_ker.mpr hψd))
  exact (mem_nilradical).mpr ⟨n, Subtype.val_injective (by simpa using hn)⟩

end RingEtaleGroupoid

end Langlands.AlgebraicGeometry
