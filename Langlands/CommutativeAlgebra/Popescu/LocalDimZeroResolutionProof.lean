import Langlands.CommutativeAlgebra.Popescu.LocalDimZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothProof
import Langlands.CommutativeAlgebra.Popescu.DimZeroGlue
import Langlands.CommutativeAlgebra.Popescu.LocalFactorization

/-! # Proof of Stacks Lemmas 9.3 and 9.4 from a local smooth factorization -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct Polynomial

set_option maxHeartbeats 1000000 in
/-- Stacks Lemma 9.3 (07F9): from a smooth `R_p`-algebra `T` through which `A → Λ_q` factors,
a factorization `A → C → Λ` with `C` finitely presented and `H_{C/R}Λ ⊄ q`. The proof applies
Lemma 8.3 (`LocalizationStandardDescentStatement`) over `R[t]` with `t ↦ ℓ`. -/
theorem exists_factor_singularIdeal_not_le (h9 : LocalizationStandardDescentStatement.{u})
    (n0 : StrictlyStandardSmoothStatement.{u}) {R A Λ : Type u} [CommRing R] [CommRing A]
    [CommRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A] (f : A →ₐ[R] Λ)
    (q : Ideal Λ) [q.IsPrime] (T : Type u) [CommRing T]
    [Algebra (Localization.AtPrime (q.comap (algebraMap R Λ))) T]
    [Algebra.Smooth (Localization.AtPrime (q.comap (algebraMap R Λ))) T]
    (u : A →+* T) (v : T →+* Localization.AtPrime q)
    (hu : u.comp (algebraMap R A) =
      (algebraMap (Localization.AtPrime (q.comap (algebraMap R Λ))) T).comp
        (algebraMap R (Localization.AtPrime (q.comap (algebraMap R Λ)))))
    (hv : v.comp u = (algebraMap Λ (Localization.AtPrime q)).comp f.toRingHom) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C), Algebra.FinitePresentation R C ∧
      ∃ (gC : A →ₐ[R] C) (hC : C →ₐ[R] Λ), hC.comp gC = f ∧
        ¬ (singularIdeal R C).map hC ≤ q := by
  classical
  set p := q.comap (algebraMap R Λ)
  set Rp := Localization.AtPrime p
  obtain ⟨ℓ, hℓq, hfac⟩ := exists_localization_factor f q u v hu hv
  -- `Λ` as an `R[t]`-algebra, `t ↦ ℓ`
  let _ : Algebra R[X] Λ := (aeval ℓ : R[X] →ₐ[R] Λ).toRingHom.toAlgebra
  have : IsScalarTower R R[X] Λ := .of_algebraMap_eq fun r => (aeval_C ℓ r).symm
  set S : Submonoid R[X] := Submonoid.closure (Polynomial.C '' p.primeCompl ∪ {X})
  have hSq : ∀ s ∈ S, algebraMap R[X] Λ s ∈ q.primeCompl := by
    intro s hs
    have : S ≤ q.primeCompl.comap (algebraMap R[X] Λ).toMonoidHom := by
      rw [Submonoid.closure_le]
      rintro x (⟨r, hr, rfl⟩ | hx)
      · show algebraMap R[X] Λ (Polynomial.C r) ∈ q.primeCompl
        rw [show algebraMap R[X] Λ (Polynomial.C r) = algebraMap R Λ r from aeval_C ℓ r]
        exact hr
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        show aeval ℓ X ∈ q.primeCompl
        rw [aeval_X]
        exact hℓq
    exact this hs
  set R' := Localization S
  set Λ' := Localization (Algebra.algebraMapSubmonoid Λ S)
  obtain ⟨w, hw⟩ := hfac (Algebra.algebraMapSubmonoid Λ S)
    (fun s hs => ⟨Polynomial.C s, Submonoid.subset_closure (Or.inl ⟨s, hs, rfl⟩), aeval_C ℓ s⟩)
    ⟨X, Submonoid.subset_closure (Or.inr rfl), aeval_X ℓ⟩
    (by rintro _ ⟨s, hs, rfl⟩; exact hSq s hs)
  -- the base change of `T` to `S⁻¹R[t]`
  have hCu : ∀ s : p.primeCompl, IsUnit (algebraMap R[X] R' (Polynomial.C (s : R))) := fun s =>
    IsLocalization.map_units R' (⟨Polynomial.C (s : R),
      Submonoid.subset_closure (Or.inl ⟨s, s.2, rfl⟩)⟩ : S)
  let can : Rp →+* R' := IsLocalization.lift (M := p.primeCompl)
    (g := (algebraMap R[X] R').comp Polynomial.C) hCu
  have hcan : ∀ r : R, can (algebraMap R Rp r) = algebraMap R[X] R' (Polynomial.C r) := fun r =>
    IsLocalization.lift_eq _ r
  let _ : Algebra Rp R' := can.toAlgebra
  set B' := R' ⊗[Rp] T
  have : IsScalarTower R[X] R' B' := inferInstance
  have : IsScalarTower R R[X] B' := inferInstance
  -- `A → B'`
  have huB : ∀ r : R, Algebra.TensorProduct.includeRight (u (algebraMap R A r)) =
      algebraMap R B' r := fun r => by
    rw [show u (algebraMap R A r) = algebraMap Rp T (algebraMap R Rp r) from
      RingHom.congr_fun hu r, AlgHom.commutes]
    show algebraMap Rp R' (algebraMap R Rp r) ⊗ₜ[Rp] (1 : T) = _
    rw [show algebraMap Rp R' (algebraMap R Rp r) = can (algebraMap R Rp r) from rfl, hcan]
    rfl
  let uB : A →ₐ[R] B' :=
    { (Algebra.TensorProduct.includeRight : T →ₐ[Rp] B').toRingHom.comp u with
      commutes' := huB }
  let u₁ : R[X] ⊗[R] A →ₐ[R[X]] B' :=
    Algebra.TensorProduct.lift (Algebra.ofId R[X] B') uB fun x y => mul_comm (Algebra.ofId R[X] B' x) (uB y)
  -- `B' → S⁻¹Λ`
  let _ : Algebra Rp Λ' := ((algebraMap R' Λ').comp can).toAlgebra
  have : IsScalarTower Rp R' Λ' := .of_algebraMap_eq fun _ => rfl
  have hwR : ∀ r : Rp, w (algebraMap Rp T r) = algebraMap Rp Λ' r := by
    have h : w.comp (algebraMap Rp T) = (algebraMap R' Λ').comp can := by
      apply IsLocalization.ringHom_ext p.primeCompl
      ext r
      have h1 := RingHom.congr_fun hw (algebraMap R A r)
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, f.commutes] at h1
      simp only [RingHom.coe_comp, Function.comp_apply, hcan]
      rw [show algebraMap Rp T (algebraMap R Rp r) = u (algebraMap R A r) from
        (RingHom.congr_fun hu r).symm]
      rw [h1, ← IsScalarTower.algebraMap_apply R[X] R' Λ', IsScalarTower.algebraMap_apply R[X] Λ Λ']
      congr 1
      exact (aeval_C ℓ r).symm
    exact fun r => RingHom.congr_fun h r
  let wA : T →ₐ[Rp] Λ' := { w with commutes' := hwR }
  let v₁ : B' →ₐ[R'] Λ' := Algebra.TensorProduct.lift (Algebra.ofId R' Λ') wA fun _ _ => .all _ _
  let f₁ : R[X] ⊗[R] A →ₐ[R[X]] Λ :=
    Algebra.TensorProduct.lift (Algebra.ofId R[X] Λ) f fun _ _ => .all _ _
  have huv : (v₁.restrictScalars R[X]).comp u₁ = (IsScalarTower.toAlgHom R[X] Λ Λ').comp f₁ := by
    apply Algebra.TensorProduct.ext'
    intro x a
    have e1 : u₁ (x ⊗ₜ[R] a) = Algebra.ofId R[X] B' x * uB a :=
      Algebra.TensorProduct.lift_tmul _ _ _ _ _
    have e2 : f₁ (x ⊗ₜ[R] a) = Algebra.ofId R[X] Λ x * f a :=
      Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.coe_restrictScalars', e1, e2, map_mul,
      map_mul, IsScalarTower.coe_toAlgHom', Algebra.ofId_apply, Algebra.ofId_apply]
    congr 1
    · rw [IsScalarTower.algebraMap_apply R[X] R' B', AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    · calc v₁ ((1 : R') ⊗ₜ[Rp] u a) = Algebra.ofId R' Λ' 1 * wA (u a) :=
            Algebra.TensorProduct.lift_tmul _ _ _ _ _
        _ = w (u a) := by rw [map_one, one_mul]; rfl
        _ = algebraMap Λ Λ' (f a) := RingHom.congr_fun hw a
  -- Lemma 8.3 over `R[t]`
  obtain ⟨B, _, _, hBfp, g, h, hgh, s, hs, hss⟩ :=
    h9 R[X] (R[X] ⊗[R] A) Λ R' Λ' S f₁ B' u₁ v₁ huv
  let _ : Algebra R B := ((algebraMap R[X] B).comp (algebraMap R R[X])).toAlgebra
  have : IsScalarTower R R[X] B := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R R[X] B
  have hsm := n0 R[X] B (algebraMap R[X] B s) hss
  have : Algebra.FormallySmooth R R[X] := .of_equiv (MvPolynomial.uniqueAlgEquiv R Unit)
  have : Algebra.Smooth R R[X] := {}
  have : Algebra.Smooth R (Localization.Away (algebraMap R[X] B s)) :=
    Algebra.Smooth.comp R R[X] _
  have hsH : algebraMap R[X] B s ∈ singularIdeal R B :=
    DimZeroResolutionProof.mem_singularIdeal_of_smooth _ this
  refine ⟨B, inferInstance, inferInstance, inferInstance,
    (g.restrictScalars R).comp (Algebra.TensorProduct.includeRight : A →ₐ[R] R[X] ⊗[R] A),
    h.restrictScalars R, ?_, ?_⟩
  · ext a
    have := congrArg (fun φ => φ ((1 : R[X]) ⊗ₜ[R] a)) hgh
    simp only [AlgHom.comp_apply, f₁, Algebra.TensorProduct.lift_tmul, map_one, one_mul] at this
    exact this
  · intro hle
    have h1 := hle (Ideal.mem_map_of_mem (h.restrictScalars R) hsH)
    rw [AlgHom.coe_restrictScalars', AlgHom.commutes] at h1
    exact hSq s hs h1

/-- Stacks Lemmas 9.3 and 9.4 (07F9, 07FA), from Lemma 8.3 and Lemma 3.7(d). -/
theorem localDimZeroResolution_of (h9 : LocalizationStandardDescentStatement.{u})
    (n0 : StrictlyStandardSmoothStatement.{u}) : LocalDimZeroResolutionStatement.{u} := by
  intro R A Λ _ _ _ _ _ _ _ _ f q _ hle hmin T _ _ _ u v hu hv
  obtain ⟨C, _, _, _, gC, hC, hgh, hCq⟩ :=
    exists_factor_singularIdeal_not_le h9 n0 f q T u v hu hv
  exact canBeResolved_of_dimZero f q hle hmin C gC hC hgh hCq

/-- Stacks Lemmas 16.9.3 and 16.9.4 (07F9, 07FA): `LocalDimZeroResolutionStatement` holds in
every universe. -/
theorem localDimZeroResolution : LocalDimZeroResolutionStatement.{u} :=
  localDimZeroResolution_of localizationStandardDescent strictlyStandardSmooth

end Langlands.CommutativeAlgebra.Popescu
