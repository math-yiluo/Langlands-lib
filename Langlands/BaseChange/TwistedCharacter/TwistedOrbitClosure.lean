import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.BaseChange.TwistedTriangularDifferential
import Langlands.BaseChange.TwistedCharacter.SemilinearDegeneration
import Langlands.BaseChange.TwistedCharacter.SemisimpleAdjoint
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Mathlib.Analysis.Normed.Ring.Units

/-! # Semisimple points in twisted matrix conjugacy-orbit closures -/

noncomputable section

namespace Langlands.BaseChange

open Module Set Topology
open scoped Matrix

section Model

universe u v

variable {F : Type u} [NontriviallyNormedField F]
  {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) E
local notation "X" => (Fin n → E)
local notation "A" => End F X
local notation "G" => GeneralLinear n E

private def matrixCoefficientEnd : M →ₐ[F] A :=
  (restrictCoefficientEnd : End E X →ₐ[F] A).comp
    ((Matrix.toLinAlgEquiv' : M ≃ₐ[E] End E X).toAlgHom.restrictScalars F)

private theorem matrixCoefficientEnd_injective :
    Function.Injective (matrixCoefficientEnd : M →ₐ[F] A) := by
  intro a b h
  apply (Matrix.toLinAlgEquiv' : M ≃ₐ[E] End E X).injective
  apply LinearMap.ext
  intro w
  exact LinearMap.congr_fun h w

private def coefficientEquiv (σ : E ≃ₐ[F] E) : X ≃ₗ[F] X :=
  LinearEquiv.piCongrRight (fun _ => σ.toLinearEquiv)

private theorem coefficientEquiv_covariance (σ : E ≃ₐ[F] E) (a : M) :
    (coefficientEquiv (n := n) σ).toLinearMap * matrixCoefficientEnd a =
      matrixCoefficientEnd (σ.mapMatrix a) * (coefficientEquiv (n := n) σ).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  change σ ((a *ᵥ x) i) = ((σ.mapMatrix a) *ᵥ fun j => σ (x j)) i
  exact RingHom.map_mulVec (σ : E →+* E) a x i

end Model

/-- The closure of every twisted conjugacy class contains an element with semisimple
adjoint operator. The scalar automorphism can be any coefficient automorphism of
positive finite order, including a power of a cyclic generator. -/
def TwistedSemisimpleOrbitClosureStatement.{u, v} : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [IsReduced E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), 0 < l → σ ^ l = 1 → ∀ δ : GeneralLinear n E,
    ∃ ε ∈ closure (range fun g : GeneralLinear n E => g * δ * (entrywiseAut σ n g)⁻¹),
      Module.End.IsSemisimple (twistedMatrixConj σ ε).toLinearMap

theorem twistedSemisimpleOrbitClosure.{u, v} : TwistedSemisimpleOrbitClosureStatement.{u, v} := by
  intro F _ _ _ E _ _ _ _ _ _ _ σ l n hl hσ δ
  let M := Matrix (Fin n) (Fin n) E
  let X := Fin n → E
  let A := End F X
  let B := End E X
  let G := GeneralLinear n E
  let j : B →ₐ[F] A := restrictCoefficientEnd
  let a : M ≃ₐ[E] B := Matrix.toLinAlgEquiv'
  let jM : M →ₐ[F] A := matrixCoefficientEnd
  let s := (coefficientEquiv (n := n) σ).toLinearMap
  let I : M →ₗ[F] A := (LinearMap.mulRight F s).comp jM.toLinearMap
  have hI (m : M) : I m = jM m * s := rfl
  have hju (k : G) : j (a k.val) = jM k.val := rfl
  have hsunit : IsUnit s := (Module.End.isUnit_iff _).mpr (coefficientEquiv σ).bijective
  have hIinj : Function.Injective I := by
    intro x y hxy
    apply matrixCoefficientEnd_injective (F := F) (E := E) (n := n)
    obtain ⟨u, hu⟩ := hsunit
    have h := congrArg (· * (u⁻¹ : Aˣ).val) hxy
    simpa only [hI, ← hu, mul_assoc, Units.mul_inv, mul_one] using h
  let _ : TopologicalSpace A := moduleTopology F A
  let _ : IsModuleTopology F A := inferInstance
  let _ : IsModuleTopology F M := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let _ : NormedRing M := finiteAlgebraNormedRing F M
  let _ : NormedAlgebra F M := finiteAlgebraNormedAlgebra F M
  let _ : CompleteSpace M := FiniteDimensional.complete F M
  let _ : NormedRing A := finiteAlgebraNormedRing F A
  let _ : NormedAlgebra F A := finiteAlgebraNormedAlgebra F A
  have hIemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hIinj)
  let T := I δ.val
  let O : Set A := range fun g : Bˣ => j g.val * T * j (g⁻¹ : Bˣ).val
  have hTunit : IsUnit T := by
    change IsUnit (I δ.val)
    rw [hI]
    exact (δ.isUnit.map jM).mul hsunit
  have hT : IsCoefficientSemilinear σ T := by
    intro e w
    change a δ.val (s (e • w)) = σ e • a δ.val (s w)
    have he : s (e • w) = σ e • s w := by
      funext i
      exact map_mul σ e (w i)
    rw [he, map_smul]
  have hTO : T ∈ O := ⟨1, by simp⟩
  have hconj (g : Bˣ) (S : A) (hS : S ∈ closure O) :
      j g.val * S * j (g⁻¹ : Bˣ).val ∈ closure O := by
    let c : A → A := fun z => j g.val * z * j (g⁻¹ : Bˣ).val
    have hcont : Continuous c := (continuous_const.mul continuous_id).mul continuous_const
    have hsub : c '' O ⊆ O := by
      rintro _ ⟨_, ⟨g', rfl⟩, rfl⟩
      refine ⟨g * g', ?_⟩
      simp only [c, Units.val_mul, mul_inv_rev, map_mul, mul_assoc]
    exact closure_mono hsub (image_closure_subset_closure_image hcont ⟨S, hS, rfl⟩)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  obtain ⟨S, hS, hSunit, _, hSsemi⟩ := exists_semisimple_in_closed_conjugacyInvariant
    σ l hl hσ (closure O) isClosed_closure hconj (subset_closure hTO) hTunit hT
  let W : Set G := range fun g : G => g * δ * (entrywiseAut σ n g)⁻¹
  have hCov (m : M) : s * jM m = jM (σ.mapMatrix m) * s := coefficientEquiv_covariance σ m
  have hPhi (k : G) :
      I ((k * δ * (entrywiseAut σ n k)⁻¹).val) = jM k.val * T * jM (k⁻¹ : G).val := by
    rw [← map_inv (entrywiseAut σ n), hI]
    change jM (k.val * δ.val * σ.mapMatrix (k⁻¹ : G).val) * s =
      jM k.val * (jM δ.val * s) * jM (k⁻¹ : G).val
    simp only [map_mul, mul_assoc, hCov]
  have hO : O = I '' (Units.val '' W) := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      let k : G := Units.map a.symm.toMonoidHom g
      have h₁ : a k.val = g.val := a.apply_symm_apply _
      have h₂ : a (k⁻¹ : G).val = (g⁻¹ : Bˣ).val := by
        rw [← map_inv]
        exact a.apply_symm_apply _
      refine ⟨(k * δ * (entrywiseAut σ n k)⁻¹).val, ⟨_, ⟨k, rfl⟩, rfl⟩, ?_⟩
      rw [hPhi, ← hju, ← hju, h₁, h₂]
    · rintro ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      refine ⟨Units.map a.toMonoidHom k, ?_⟩
      rw [hPhi, ← hju, ← hju]
      change j (a k.val) * T * j ((Units.map a.toMonoidHom k)⁻¹).val = _
      rw [← map_inv]
      rfl
  rw [hO, hIemb.closure_image_eq] at hS
  obtain ⟨m, hm, hMS⟩ := hS
  have hjunit : IsUnit (jM m) := by
    obtain ⟨u, hu⟩ := hsunit
    have he : jM m = S * (u⁻¹ : Aˣ).val := by
      rw [← hMS, hI, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [he]
    exact hSunit.mul (u⁻¹).isUnit
  have hjunit' : IsUnit (a m) := by
    apply (Module.End.isUnit_iff _).2
    exact (Module.End.isUnit_iff (jM m)).mp hjunit
  obtain ⟨ε, he⟩ := hjunit'.map a.symm.toMonoidHom
  have hε : ε.val = m := he.trans (a.symm_apply_apply _)
  refine ⟨ε, ?_, ?_⟩
  · rw [(Units.isOpenEmbedding_val (R := M)).isEmbedding.closure_eq_preimage_closure_image]
    change ε.val ∈ closure (Units.val '' W)
    rwa [hε]
  · obtain ⟨u, hu⟩ := hSunit
    have hU : u.val = jM ε.val * s := by rw [hu, hε, ← hMS, hI]
    let Ad := ((u.mulLeftLinearEquiv F A).trans (u⁻¹.mulRightLinearEquiv F)).toLinearMap
    have hAd : Module.End.IsSemisimple Ad := isSemisimple_conjugationOnEnd u (hu.symm ▸ hSsemi)
    apply Langlands.GroupScheme.Lie.isSemisimple_of_injective_intertwiner jM.toLinearMap
      matrixCoefficientEnd_injective ?_ hAd
    apply LinearMap.ext
    intro x
    change jM (twistedMatrixConj σ ε x) = u.val * jM x * (u⁻¹ : Aˣ).val
    have hmult : jM (twistedMatrixConj σ ε x) * u.val = u.val * jM x := by
      rw [twistedMatrixConj_apply, hU]
      simp only [map_mul, mul_assoc, hCov]
      have hεinv : jM ((ε⁻¹ : G).val) * jM ε.val = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [← mul_assoc (jM ((ε⁻¹ : G).val)), hεinv, one_mul]
    rw [← hmult, mul_assoc, Units.mul_inv, mul_one]

end Langlands.BaseChange
