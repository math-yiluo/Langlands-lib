import Langlands.CommutativeAlgebra.Popescu.ArtinianEtaleCriterionStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianColengthOnePullback
import Mathlib

/-! # Proof of the Artinian étale criterion -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace EtaleCriterion

open IsLocalRing Polynomial

/-- A local ring with nilpotent maximal ideal is adically complete. -/
theorem isAdicComplete_of_isNilpotent {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsNilpotent (maximalIdeal R)) : IsAdicComplete (maximalIdeal R) R := by
  obtain ⟨N, hN⟩ := h
  have hpow : ∀ n, N ≤ n → ((maximalIdeal R) ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
      ← Nat.add_sub_cancel' hn, pow_add, hN, Ideal.zero_eq_bot, Ideal.bot_mul]
    rfl
  have h1 : IsHausdorff (maximalIdeal R) R := ⟨fun x hx => by
    have := hx N
    rw [hpow N le_rfl, SModEq.bot] at this
    exact this⟩
  have h2 : IsPrecomplete (maximalIdeal R) R := ⟨fun f hf => ⟨f N, fun n => by
    rcases le_total n N with hn | hn
    · exact hf hn
    · have := hf hn
      rw [hpow N le_rfl, SModEq.bot] at this
      rw [this]⟩⟩
  exact {}

/-- Nakayama's lemma for a nilpotent ideal and an arbitrary module. -/
theorem eq_top_of_le_sup_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : IsNilpotent I) {N : Submodule R M} (h : ⊤ ≤ N ⊔ I • ⊤) : N = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  have key : ∀ k : ℕ, ⊤ ≤ N ⊔ (I ^ (k + 1) • ⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h1 : (I ^ (k + 1) • ⊤ : Submodule R M) ≤ N ⊔ I ^ (k + 2) • ⊤ := by
        calc (I ^ (k + 1) • ⊤ : Submodule R M) ≤ I ^ (k + 1) • (N ⊔ I • ⊤) :=
              Submodule.smul_mono le_rfl h
          _ = I ^ (k + 1) • N ⊔ I ^ (k + 1) • (I • ⊤) := Submodule.smul_sup _ _ _
          _ ≤ N ⊔ I ^ (k + 2) • ⊤ := by
            apply sup_le_sup (Submodule.smul_le_right)
            rw [← Submodule.mul_smul, ← pow_succ]
      calc ⊤ ≤ N ⊔ (I ^ (k + 1) • ⊤ : Submodule R M) := ih
        _ ≤ N ⊔ (N ⊔ I ^ (k + 2) • ⊤) := sup_le_sup_left h1 _
        _ = N ⊔ I ^ (k + 2) • ⊤ := by rw [← sup_assoc, sup_idem]
  have := key n
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_le_iff.mp this

open TensorProduct in
/-- **Stacks 00U6/07DT, Artinian case.** A flat local map of Artinian local rings, essentially of
finite type, with `𝔪_P D = 𝔪_D` and separable residue extension, is standard étale; in particular
`D` is essentially smooth over `P`. -/
theorem artinianEtaleCriterion : ArtinianEtaleCriterionStatement.{u} := by
  intro P D _ _ _ _ _ _ _ _ _ _ hm hsep
  classical
  -- the residue field extension is finite separable with a primitive element `α`
  have : Algebra.FiniteType D (ResidueField D) :=
    .of_surjective (IsScalarTower.toAlgHom D D (ResidueField D)) residue_surjective
  have : Algebra.EssFiniteType P (ResidueField D) := .comp P D (ResidueField D)
  have : Algebra.EssFiniteType (ResidueField P) (ResidueField D) := .of_comp P _ _
  have : Algebra.FormallyUnramified (ResidueField P) (ResidueField D) := .of_isSeparable _ _
  have : Module.Finite (ResidueField P) (ResidueField D) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField P) (ResidueField D)
  have hαint : IsIntegral (ResidueField P) α := Algebra.IsIntegral.isIntegral α
  have hgsep : (minpoly (ResidueField P) α).Separable := Algebra.IsSeparable.isSeparable _ α
  have hgmonic := minpoly.monic hαint
  have hg0 : aeval α (minpoly (ResidueField P) α) = 0 := minpoly.aeval _ α
  -- a monic lift `G` of the minimal polynomial
  have hlifts : minpoly (ResidueField P) α ∈ Polynomial.lifts (residue P) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact residue_surjective _
  obtain ⟨G, hGmap, hGdeg, hGmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hgmonic
  -- residues of polynomial expressions
  have hres : ∀ (F : P[X]) (x : D),
      residue D (aeval x F) = aeval (residue D x) (F.map (residue P)) := by
    intro F x
    have h1 : residue D (aeval x F) = IsScalarTower.toAlgHom P D (ResidueField D) (aeval x F) := rfl
    rw [h1, ← Polynomial.aeval_algHom_apply]
    have h2 : (residue P : P →+* ResidueField P) = algebraMap P (ResidueField P) := rfl
    rw [h2, Polynomial.aeval_map_algebraMap]
    rfl
  -- Hensel's lemma in the Artinian local ring `D`
  have : IsAdicComplete (maximalIdeal D) D :=
    isAdicComplete_of_isNilpotent
      (Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne.isNilpotent_maximalIdeal (Λ := D))
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective α
  have hev : (G.map (algebraMap P D)).eval θ₀ ∈ maximalIdeal D := by
    rw [Polynomial.eval_map_algebraMap, ← residue_eq_zero_iff, hres, hθ₀, hGmap, hg0]
  have hder : IsUnit (Ideal.Quotient.mk (maximalIdeal D)
      ((G.map (algebraMap P D)).derivative.eval θ₀)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    change IsUnit (residue D _)
    rw [hres, hθ₀, ← Polynomial.derivative_map, hGmap, isUnit_iff_ne_zero]
    exact hgsep.aeval_derivative_ne_zero hg0
  obtain ⟨θ, hθroot, hθ⟩ := HenselianRing.is_henselian (G.map (algebraMap P D))
    (hGmonic.map _) θ₀ hev hder
  have hroot : aeval θ G = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact hθroot
  have hθres : residue D θ = α := by
    have h1 : residue D (θ - θ₀) = 0 := (residue_eq_zero_iff _).mpr hθ
    rw [map_sub, sub_eq_zero] at h1
    rw [h1, hθ₀]
  have hunitθ : IsUnit (aeval θ (derivative G)) := by
    rw [← residue_ne_zero_iff_isUnit, hres, hθres, ← Polynomial.derivative_map, hGmap]
    exact hgsep.aeval_derivative_ne_zero hg0
  -- the map `ρ : P[X]/(G) → D`
  let ρ : AdjoinRoot G →ₐ[P] D := AdjoinRoot.liftAlgHom G (Algebra.ofId P D) θ (by
    have h := hroot
    rw [Polynomial.aeval_def] at h
    exact h)
  have hρroot : ρ (AdjoinRoot.root G) = θ := AdjoinRoot.liftAlgHom_root _ _ _ _
  let pb := AdjoinRoot.powerBasis' hGmonic
  -- injectivity: the powers of `θ` are linearly independent (flatness of `D`)
  have hliα : LinearIndependent P
      (fun i : Fin (minpoly (ResidueField P) α).natDegree => θ ^ (i : ℕ)) := by
    apply Module.IsLocalRing.linearIndependent_of_flat
    let φL : ResidueField P ⊗[P] D →ₗ[ResidueField P] ResidueField D :=
      LinearMap.liftBaseChange (ResidueField P)
        (IsScalarTower.toAlgHom P D (ResidueField D)).toLinearMap
    apply LinearIndependent.of_comp φL
    convert linearIndependent_pow (K := ResidueField P) α using 1
    funext i
    simp only [Function.comp_apply, TensorProduct.mk_apply, φL, LinearMap.liftBaseChange_tmul,
      one_smul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', map_pow]
    exact congrArg (· ^ (i : ℕ)) hθres
  have hdim : pb.dim = (minpoly (ResidueField P) α).natDegree := hGdeg
  have hli : LinearIndependent P (fun i : Fin pb.dim => θ ^ (i : ℕ)) :=
    hliα.comp (finCongr hdim) (finCongr hdim).injective
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' := congrArg ρ (pb.basis.sum_repr x)
    rw [hx, map_sum] at hx'
    have hsum : ∑ i, pb.basis.repr x i • θ ^ (i : ℕ) = 0 := by
      rw [hx'.symm.trans rfl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, PowerBasis.coe_basis, map_pow]
      show _ = _ • ρ (AdjoinRoot.root G) ^ (i : ℕ)
      rw [hρroot]
    have hzero := Fintype.linearIndependent_iff.mp hli _ hsum
    rw [← pb.basis.sum_repr x]
    simp [hzero]
  -- surjectivity: Nakayama for the nilpotent ideal `𝔪_P`
  have hsurj : Function.Surjective ρ := by
    let N : Submodule P D := Subalgebra.toSubmodule ρ.range
    have hN : N = ⊤ := by
      apply eq_top_of_le_sup_smul
        (Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne.isNilpotent_maximalIdeal (Λ := P))
      intro d _
      have hd : residue D d ∈ Algebra.adjoin (ResidueField P) {α} := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic, hα]
        trivial
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hd
      obtain ⟨p, hp⟩ := hd
      have hplifts : p ∈ Polynomial.lifts (residue P) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact residue_surjective _
      obtain ⟨Fp, hFp⟩ := hplifts
      have hmem : aeval θ Fp ∈ N := ⟨aeval (AdjoinRoot.root G) Fp, by
        show ρ (aeval (AdjoinRoot.root G) Fp) = _
        rw [← Polynomial.aeval_algHom_apply, hρroot]⟩
      have hdiff : d - aeval θ Fp ∈ (maximalIdeal P • ⊤ : Submodule P D) := by
        rw [Ideal.smul_top_eq_map, hm]
        show d - aeval θ Fp ∈ maximalIdeal D
        rw [← residue_eq_zero_iff, map_sub, hres, hθres,
          show Polynomial.map (residue P) Fp = p from hFp]
        change residue D d - (aeval α) p = 0
        rw [← hp]
        simp
      have : d = aeval θ Fp + (d - aeval θ Fp) := by ring
      rw [this]
      exact Submodule.add_mem_sup hmem hdiff
    intro d
    have : d ∈ N := hN ▸ Submodule.mem_top
    exact this
  let e₃ : AdjoinRoot G ≃ₐ[P] D := AlgEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  -- `D` is standard étale over `P`
  let Pr : StandardEtalePair P := ⟨G, hGmonic, derivative G, 1, 0, 1, by simp⟩
  have hmap : Pr.HasMap θ := ⟨hroot, by simpa using hunitθ⟩
  have hX : (G : P[X]).eval₂ (Algebra.ofId P Pr.Ring) Pr.X = 0 := by
    have h := Pr.hasMap_X.1
    rw [Polynomial.aeval_def] at h
    exact h
  let ψinv : D →ₐ[P] Pr.Ring :=
    (AdjoinRoot.liftAlgHom G (Algebra.ofId P Pr.Ring) Pr.X hX).comp e₃.symm.toAlgHom
  have he₃root : e₃.symm θ = AdjoinRoot.root G := by
    rw [AlgEquiv.symm_apply_eq]
    exact hρroot.symm
  have hψθ : ψinv θ = Pr.X := by
    show AdjoinRoot.liftAlgHom G (Algebra.ofId P Pr.Ring) Pr.X hX (e₃.symm θ) = Pr.X
    rw [he₃root, AdjoinRoot.liftAlgHom_root]
  have h1 : (Pr.lift θ hmap).comp ψinv = AlgHom.id P D := by
    have : ((Pr.lift θ hmap).comp ψinv).comp (e₃ : AdjoinRoot G →ₐ[P] D) =
        (e₃ : AdjoinRoot G →ₐ[P] D) := by
      apply AdjoinRoot.algHom_ext
      show Pr.lift θ hmap (ψinv (ρ (AdjoinRoot.root G))) = ρ (AdjoinRoot.root G)
      rw [hρroot, hψθ, StandardEtalePair.lift_X]
    ext d
    have := AlgHom.congr_fun this (e₃.symm d)
    simpa using this
  have h2 : ψinv.comp (Pr.lift θ hmap) = AlgHom.id P Pr.Ring := by
    apply Pr.hom_ext
    simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, hψθ, AlgHom.id_apply]
  have hbij : Function.Bijective (Pr.lift θ hmap) :=
    ⟨Function.LeftInverse.injective (g := ψinv) fun x => AlgHom.congr_fun h2 x,
      Function.RightInverse.surjective (g := ψinv) fun d => AlgHom.congr_fun h1 d⟩
  have : Algebra.IsStandardEtale P D :=
    ⟨⟨⟨Pr, θ, hmap, hbij⟩⟩⟩
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ⊥, inferInstance,
    IsLocalization.self bot_le⟩

end EtaleCriterion

end Langlands.CommutativeAlgebra.Popescu
