import Mathlib

/-! # Points of standard etale algebras over fields -/

universe u v

open Polynomial
open scoped IntermediateField

noncomputable section

namespace Langlands.CommutativeAlgebra.EtaleLocalSections

/-- If every root of a monic polynomial `f` over an algebraically closed field is a root of
`g`, then `f` divides `g ^ natDegree f`. -/
lemma dvd_pow_natDegree_of_forall_isRoot {K : Type*} [Field K] [IsAlgClosed K] {f g : K[X]}
    (hf : f.Monic) (h : ∀ y ∈ f.roots, g.IsRoot y) : f ∣ g ^ f.natDegree := by
  have hs : Splits f := IsAlgClosed.splits f
  rw [hs.natDegree_eq_card_roots]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hf]
  rw [← Multiset.prod_replicate, ← Multiset.map_const']
  exact Multiset.prod_dvd_prod_of_dvd _ _ fun y hy => dvd_iff_isRoot.mpr (h y hy)

/-- Let `f` be monic and let `r` be the remainder of `g ^ natDegree f` modulo `f`. At a field
point `φ` where `r` does not vanish, `f` has a root in an algebraic closure at which `g` does
not vanish. -/
lemma exists_root_of_map_modByMonic_ne_zero {A K : Type*} [CommRing A] [Field K] {f : A[X]}
    (g : A[X]) (hf : f.Monic) (φ : A →+* K) (h : ((g ^ f.natDegree) %ₘ f).map φ ≠ 0) :
    ∃ y : AlgebraicClosure K, aeval y (f.map φ) = 0 ∧ aeval y (g.map φ) ≠ 0 := by
  by_contra! H
  let ι := algebraMap K (AlgebraicClosure K)
  have hF : ((f.map φ).map ι).Monic := (hf.map φ).map ι
  have hdeg : ((f.map φ).map ι).natDegree = f.natDegree := by
    rw [(hf.map φ).natDegree_map, hf.natDegree_map]
  have hdvd : (f.map φ).map ι ∣ ((g.map φ).map ι) ^ ((f.map φ).map ι).natDegree := by
    refine dvd_pow_natDegree_of_forall_isRoot hF fun y hy => ?_
    have hy' : aeval y (f.map φ) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots hF.ne_zero).mp hy
    have := H y hy'
    rw [aeval_def, eval₂_eq_eval_map] at this
    exact this
  apply h
  apply Polynomial.map_injective ι ι.injective
  rw [Polynomial.map_zero, map_modByMonic φ hf, map_modByMonic ι (hf.map φ), Polynomial.map_pow,
    Polynomial.map_pow, ← hdeg]
  exact (modByMonic_eq_zero_iff_dvd hF).mpr hdvd

/-- At a field point `φ` where `f` has a root `y` with `g y ≠ 0`, the remainder of
`g ^ natDegree f` modulo the monic polynomial `f` does not vanish. -/
lemma map_modByMonic_ne_zero_of_eval₂ {A K : Type*} [CommRing A] [Field K] {f : A[X]}
    (g : A[X]) (hf : f.Monic) (φ : A →+* K) {y : K} (hy : eval₂ φ y f = 0)
    (hg : eval₂ φ y g ≠ 0) : ((g ^ f.natDegree) %ₘ f).map φ ≠ 0 := by
  intro h
  rw [map_modByMonic φ hf, modByMonic_eq_zero_iff_dvd (hf.map φ)] at h
  obtain ⟨q, hq⟩ := h
  have := congrArg (eval y) hq
  rw [eval_mul, eval_map, eval_map, hy, zero_mul, eval₂_pow] at this
  exact pow_ne_zero _ hg this

/-- A nonzero polynomial over a field does not vanish at some point whose coordinates are
polynomials in a separable algebraic element. -/
lemma exists_separable_point {κ : Type u} [Field κ] {n : ℕ} {h : MvPolynomial (Fin n) κ}
    (hh : h ≠ 0) :
    ∃ (m : κ[X]) (p : Fin n → κ[X]) (z : AlgebraicClosure κ), m.Monic ∧ aeval z m = 0 ∧
      aeval z (derivative m) ≠ 0 ∧ MvPolynomial.aeval (fun i => aeval z (p i)) h ≠ 0 := by
  by_cases hfin : Finite κ
  · let K := AlgebraicClosure κ
    have h' : MvPolynomial.map (algebraMap κ K) h ≠ 0 := fun H =>
      hh (MvPolynomial.map_injective _ (algebraMap κ K).injective (H.trans (map_zero _).symm))
    obtain ⟨c, hc⟩ : ∃ c : Fin n → K, MvPolynomial.eval c (MvPolynomial.map (algebraMap κ K) h) ≠ 0 := by
      by_contra! H
      exact h' (MvPolynomial.funext fun x => by simp [H x])
    let E := IntermediateField.adjoin κ (Set.range c)
    have : FiniteDimensional κ E :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    have : Algebra.IsSeparable κ E := Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨α, hα⟩ := Field.exists_primitive_element κ E
    let θ : K := α
    have hcp : ∀ i, ∃ p : κ[X], aeval θ p = c i := by
      intro i
      have hmem : (⟨c i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E) ∈ κ⟮α⟯ :=
        hα ▸ IntermediateField.mem_top
      rw [← IntermediateField.mem_toSubalgebra,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic α), Algebra.adjoin_singleton_eq_range_aeval] at hmem
      obtain ⟨p, hp⟩ := hmem
      refine ⟨p, ?_⟩
      have := congrArg (fun e : E => (e : K)) hp
      simpa [θ, aeval_algHom_apply] using this
    choose p hp using hcp
    have hθ : minpoly κ θ = minpoly κ α := minpoly.algHom_eq E.val Subtype.val_injective α
    have hsep : (minpoly κ θ).Separable := hθ ▸ Algebra.IsSeparable.isSeparable κ α
    refine ⟨minpoly κ θ, p, θ, minpoly.monic (Algebra.IsIntegral.isIntegral θ),
      minpoly.aeval κ θ, hsep.aeval_derivative_ne_zero (minpoly.aeval κ θ), ?_⟩
    rw [show (fun i => aeval θ (p i)) = c from funext hp]
    rwa [MvPolynomial.eval_map, ← MvPolynomial.aeval_def] at hc
  · have : Infinite κ := not_finite_iff_infinite.mp hfin
    obtain ⟨c, hc⟩ : ∃ c : Fin n → κ, MvPolynomial.eval c h ≠ 0 := by
      by_contra! H
      exact hh (MvPolynomial.funext fun x => by simp [H x])
    refine ⟨X, fun i => C (c i), 0, monic_X, by simp, by simp, ?_⟩
    rw [show (fun i => aeval (0 : AlgebraicClosure κ) (C (c i))) =
      algebraMap κ (AlgebraicClosure κ) ∘ c from by ext; simp, MvPolynomial.aeval_algebraMap_apply]
    exact (_root_.map_ne_zero _).mpr hc

section Residue

variable {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

lemma algebraMap_residueField_ne_zero_iff (b : R) :
    algebraMap R 𝔭.ResidueField b ≠ 0 ↔ b ∉ 𝔭 := by
  rw [ne_eq, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

/-- Finitely many elements of the residue field of `𝔭` come from a single localization `R[1/b]`
with `b ∉ 𝔭`, through a ring map `R[1/b] → κ(𝔭)` extending `R → κ(𝔭)`. -/
lemma exists_away_lift (s : Finset 𝔭.ResidueField) :
    ∃ b ∉ 𝔭, ∃ β : Localization.Away b →+* 𝔭.ResidueField,
      β.comp (algebraMap R _) = algebraMap R 𝔭.ResidueField ∧ ∀ x ∈ s, x ∈ Set.range β := by
  classical
  have hx : ∀ x : 𝔭.ResidueField, ∃ a c : R, c ∉ 𝔭 ∧
      algebraMap R _ a / algebraMap R _ c = x := by
    intro x
    obtain ⟨a', c', hc', rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ 𝔭) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    refine ⟨a, c, fun hc => ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero hc' (Ideal.Quotient.eq_zero_iff_mem.mpr hc)
    · rw [IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) 𝔭.ResidueField a,
        IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) 𝔭.ResidueField c]
      rfl
  choose a c hc hac using hx
  let b : R := ∏ x ∈ s, c x
  have hb : algebraMap R 𝔭.ResidueField b ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => (algebraMap_residueField_ne_zero_iff 𝔭 _).mpr (hc x)
  have hbu : IsUnit (algebraMap R 𝔭.ResidueField b) := isUnit_iff_ne_zero.mpr hb
  let β : Localization.Away b →+* 𝔭.ResidueField := IsLocalization.Away.lift b hbu
  have hβ : β.comp (algebraMap R _) = algebraMap R 𝔭.ResidueField := IsLocalization.lift_comp _
  refine ⟨b, (algebraMap_residueField_ne_zero_iff 𝔭 b).mp hb, β, hβ, fun x hxs => ?_⟩
  have hcu : IsUnit (algebraMap R (Localization.Away b) (c x)) := by
    have hbunit := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b
    obtain ⟨d, hd⟩ : c x ∣ b := Finset.dvd_prod_of_mem c hxs
    have hbd : algebraMap R (Localization.Away b) b =
        algebraMap R (Localization.Away b) (c x) * algebraMap R (Localization.Away b) d := by
      rw [← map_mul, ← hd]
    rw [hbd] at hbunit
    exact isUnit_of_mul_isUnit_left hbunit
  refine ⟨algebraMap R _ (a x) * ↑hcu.unit⁻¹, ?_⟩
  have h1 : β (algebraMap R _ (a x)) = algebraMap R 𝔭.ResidueField (a x) :=
    congrArg (fun φ => φ (a x)) hβ
  have h2 : β (algebraMap R _ (c x)) = algebraMap R 𝔭.ResidueField (c x) :=
    congrArg (fun φ => φ (c x)) hβ
  rw [map_mul, map_units_inv, IsUnit.unit_spec, h1, h2, ← div_eq_mul_inv, hac]

end Residue

section Main

open Algebra

/-- A standard etale algebra over a polynomial ring `R[X₁, …, Xₙ]` has, near each of its
points, a section over an etale `R`-algebra: for every prime `𝔮` of `S` there are an etale
`R`-algebra `R'`, an `R`-algebra map `S → R'`, and a prime of `R'` over the same prime of `R`
as `𝔮`. -/
theorem exists_etale_algHom_of_isStandardEtale {R : Type u} [CommRing R] {n : ℕ} {S : Type u}
    [CommRing S] [Algebra R S] [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [IsStandardEtale (MvPolynomial (Fin n) R) S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Etale R R' ∧ Nonempty (S →ₐ[R] R') ∧
      ∃ 𝔮' : Ideal R', 𝔮'.IsPrime ∧ 𝔮'.comap (algebraMap R R') = 𝔮.comap (algebraMap R S) := by
  classical
  let P := MvPolynomial (Fin n) R
  let Q : StandardEtalePresentation P S := (IsStandardEtale.nonempty_standardEtalePresentation).some
  let 𝔭 := 𝔮.comap (algebraMap R S)
  let κ := 𝔭.ResidueField
  let d := Q.f.natDegree
  let r : P[X] := (Q.g ^ d) %ₘ Q.f
  -- The point `𝔮` of `S`.
  let L₀ := 𝔮.ResidueField
  let φ₀ : P →+* L₀ := (algebraMap S L₀).comp (algebraMap P S)
  have hy₀ : eval₂ φ₀ (algebraMap S L₀ Q.x) Q.f = 0 := by
    have := congrArg (algebraMap S L₀) Q.hasMap.1
    rwa [map_zero, aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq] at this
  have hg₀ : eval₂ φ₀ (algebraMap S L₀ Q.x) Q.g ≠ 0 := by
    have := (Q.hasMap.2.map (algebraMap S L₀)).ne_zero
    rwa [aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq] at this
  obtain ⟨j, hj⟩ : ∃ j, φ₀ (r.coeff j) ≠ 0 := by
    by_contra! H
    exact map_modByMonic_ne_zero_of_eval₂ Q.g Q.monic_f φ₀ hy₀ hg₀
      (Polynomial.ext fun k => by rw [coeff_map, coeff_zero]; exact H k)
  -- The residue field of `𝔭` embeds into that of `𝔮`, and `φ₀` factors through `κ[X]`.
  let ι : κ →+* L₀ := Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) rfl
  let v : Fin n → L₀ := fun i => φ₀ (MvPolynomial.X i)
  have hφ₀ : φ₀ = (MvPolynomial.eval₂Hom ι v).comp (MvPolynomial.map (algebraMap R κ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [φ₀, RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [Ideal.ResidueField.map_algebraMap 𝔭 𝔮 (algebraMap R S) rfl a,
        ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply R P S]
    · intro i
      simp [v]
  let hbar := MvPolynomial.map (algebraMap R κ) (r.coeff j)
  have hhbar : hbar ≠ 0 := by
    intro h0
    apply hj
    rw [hφ₀, RingHom.comp_apply]
    change MvPolynomial.eval₂Hom ι v hbar = 0
    rw [h0, map_zero]
  obtain ⟨mbar, pbar, z, hmon, hmz, hmz', hpz⟩ := exists_separable_point hhbar
  let K := AlgebraicClosure κ
  -- Lift the coefficients to a localization `R[1/b]`.
  let s : Finset κ := mbar.support.image mbar.coeff ∪
    Finset.univ.biUnion fun i => (pbar i).support.image (pbar i).coeff
  obtain ⟨b, hb𝔭, β, hβ, hβs⟩ := exists_away_lift 𝔭 s
  let Rb := Localization.Away b
  have hlift : ∀ q : κ[X], (∀ k ∈ q.support, q.coeff k ∈ s) → q ∈ Polynomial.lifts β := by
    intro q hq
    rw [lifts_iff_coeff_lifts]
    intro k
    by_cases hk : k ∈ q.support
    · exact hβs _ (hq k hk)
    · rw [notMem_support_iff.mp hk]
      exact ⟨0, map_zero β⟩
  obtain ⟨m, hmmap, -, hmmon⟩ := lifts_and_degree_eq_and_monic
    (hlift mbar fun k hk => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)) hmon
  have hplift : ∀ i, ∃ q : Rb[X], q.map β = pbar i := fun i =>
    (mem_lifts _).mp (hlift (pbar i) fun k hk => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hk⟩))
  choose p hp using hplift
  -- The etale algebra `R₁` adjoining a separable root of `m`.
  let E₁ : StandardEtalePair Rb := ⟨m, hmmon, derivative m, ⟨1, 0, 1, by simp⟩⟩
  let R₁ := E₁.Ring
  let : Algebra R R₁ := ((algebraMap Rb R₁).comp (algebraMap R Rb)).toAlgebra
  have : IsScalarTower R Rb R₁ := .of_algebraMap_eq fun _ => rfl
  have : Etale R R₁ := Etale.comp R Rb R₁
  let ψ : P →ₐ[R] R₁ := MvPolynomial.aeval fun i => aeval E₁.X (p i)
  let : Algebra P R₁ := ψ.toRingHom.toAlgebra
  have : IsScalarTower R P R₁ := .of_algebraMap_eq fun a => (ψ.commutes a).symm
  -- The specialization `R'` of the standard etale algebra at `ψ`.
  let E₂ : StandardEtalePair R₁ := Q.P.map (algebraMap P R₁)
  let R' := E₂.Ring
  let : Algebra R R' := ((algebraMap R₁ R').comp (algebraMap R R₁)).toAlgebra
  have : IsScalarTower R R₁ R' := .of_algebraMap_eq fun _ => rfl
  let : Algebra P R' := ((algebraMap R₁ R').comp (algebraMap P R₁)).toAlgebra
  have : IsScalarTower P R₁ R' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R P R' := .of_algebraMap_eq fun a => by
    change algebraMap R₁ R' (algebraMap R R₁ a) =
      algebraMap R₁ R' (algebraMap P R₁ (algebraMap R P a))
    rw [← IsScalarTower.algebraMap_apply R P R₁]
  refine ⟨R', inferInstance, inferInstance, Etale.comp R R₁ R', ?_, ?_⟩
  · have hmap : Q.HasMap E₂.X := by
      simpa [StandardEtalePair.HasMap, E₂] using E₂.hasMap_X
    exact ⟨((Q.lift E₂.X hmap).comp Q.equivRing.toAlgHom).restrictScalars R⟩
  -- A field point of `R'` over `𝔭`.
  let : Algebra Rb K := ((algebraMap κ K).comp β).toAlgebra
  have hev : ∀ q : Rb[X], aeval z q = aeval z (q.map β) := fun q => by
    rw [aeval_def, aeval_def, eval₂_map]
    rfl
  have hz : E₁.HasMap z := by
    refine ⟨?_, ?_⟩
    · change aeval z m = 0
      rw [hev, hmmap, hmz]
    · change IsUnit (aeval z (derivative m))
      rw [hev, ← derivative_map, hmmap]
      exact isUnit_iff_ne_zero.mpr hmz'
  let ρ₁ : R₁ →ₐ[Rb] K := E₁.lift z hz
  let φ : P →+* K := ρ₁.toRingHom.comp (algebraMap P R₁)
  have hφ : φ = (MvPolynomial.eval₂Hom (algebraMap κ K) (fun i => aeval z (pbar i))).comp
      (MvPolynomial.map (algebraMap R κ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      change ρ₁ (ψ (MvPolynomial.C a)) = algebraMap κ K (algebraMap R κ a)
      rw [← MvPolynomial.algebraMap_eq, ψ.commutes]
      change ρ₁ (algebraMap Rb R₁ (algebraMap R Rb a)) = _
      rw [ρ₁.commutes]
      change algebraMap κ K (β (algebraMap R Rb a)) = _
      rw [← RingHom.comp_apply β, hβ]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      change ρ₁ (ψ (MvPolynomial.X i)) = aeval z (pbar i)
      rw [MvPolynomial.aeval_X, ← Polynomial.aeval_algHom_apply, StandardEtalePair.lift_X, hev,
        hp]
  have hφr : r.map φ ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff j) h0
    simp only [coeff_map, coeff_zero] at this
    rw [hφ, RingHom.comp_apply] at this
    exact hpz this
  obtain ⟨y, hy1, hy2⟩ := exists_root_of_map_modByMonic_ne_zero Q.g Q.monic_f φ hφr
  let L := AlgebraicClosure K
  let : Algebra R₁ L := ((algebraMap K L).comp ρ₁.toRingHom).toAlgebra
  have hyE : E₂.HasMap y := by
    rw [aeval_def, eval₂_map] at hy1 hy2
    refine ⟨?_, ?_⟩
    · change aeval y (Q.f.map (algebraMap P R₁)) = 0
      rw [aeval_def, eval₂_map]
      exact hy1
    · change IsUnit (aeval y (Q.g.map (algebraMap P R₁)))
      rw [aeval_def, eval₂_map]
      exact isUnit_iff_ne_zero.mpr hy2
  let ρ' : R' →ₐ[R₁] L := E₂.lift y hyE
  refine ⟨RingHom.ker ρ'.toRingHom, RingHom.ker_isPrime _, ?_⟩
  rw [RingHom.comap_ker]
  have hcomp : ρ'.toRingHom.comp (algebraMap R R') =
      (algebraMap K L).comp ((algebraMap κ K).comp (algebraMap R κ)) := by
    ext a
    change ρ' (algebraMap R₁ R' (algebraMap Rb R₁ (algebraMap R Rb a))) = _
    rw [ρ'.commutes]
    change algebraMap K L (ρ₁ (algebraMap Rb R₁ (algebraMap R Rb a))) = _
    rw [ρ₁.commutes]
    change algebraMap K L (algebraMap κ K (β (algebraMap R Rb a))) = _
    rw [← RingHom.comp_apply β, hβ]
    rfl
  rw [hcomp, RingHom.ker_comp_of_injective _ (algebraMap K L).injective,
    RingHom.ker_comp_of_injective _ (algebraMap κ K).injective, Ideal.ker_algebraMap_residueField]

end Main

end Langlands.CommutativeAlgebra.EtaleLocalSections
