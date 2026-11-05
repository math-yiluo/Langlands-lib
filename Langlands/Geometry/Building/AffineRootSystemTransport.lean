import Langlands.Geometry.Building.AffineWeylTransport
import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-! # Affine root system axioms under affine equivalences -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {W : Type uW} {B : Type uB} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- Inverse precomposition on the dual of the translation space. -/
def derivativeTransport (e : A ≃ᵃ[ℝ] B) :
    Module.Dual ℝ V ≃ₗ[ℝ] Module.Dual ℝ W :=
  e.linear.symm.dualMap

/-- The derivative of the transported functional is transported by the dual map. -/
theorem linear_affineFunctionalTransport (e : A ≃ᵃ[ℝ] B) (ψ : A →ᵃ[ℝ] ℝ) :
    (affineFunctionalTransport e ψ).linear = derivativeTransport e ψ.linear := rfl

/-- Equality of derivatives is preserved and reflected. -/
theorem linear_affineFunctionalTransport_eq_iff (e : A ≃ᵃ[ℝ] B)
    (ψ φ : A →ᵃ[ℝ] ℝ) :
    (affineFunctionalTransport e ψ).linear = (affineFunctionalTransport e φ).linear ↔
      ψ.linear = φ.linear := by
  change derivativeTransport e ψ.linear = derivativeTransport e φ.linear ↔ _
  exact (derivativeTransport e).injective.eq_iff

/-- The entire derivative root set is the image under the dual equivalence. -/
theorem derivativeRoots_transportedRoots (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    derivativeRoots (transportedRoots e Ψ) = derivativeTransport e '' derivativeRoots Ψ := by
  simp only [derivativeRoots, transportedRoots, Set.image_image]
  rfl

/-- The fiber of a derivative is carried to its corresponding fiber. -/
theorem derivativeFiber_transportedRoots (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (ψ : A →ᵃ[ℝ] ℝ) :
    {φ | φ ∈ transportedRoots e Ψ ∧
        φ.linear = (affineFunctionalTransport e ψ).linear} =
      affineFunctionalTransport e '' {φ | φ ∈ Ψ ∧ φ.linear = ψ.linear} := by
  ext φ
  constructor
  · rintro ⟨⟨χ, hχ, rfl⟩, hlin⟩
    exact ⟨χ, ⟨hχ, (linear_affineFunctionalTransport_eq_iff e χ ψ).mp hlin⟩, rfl⟩
  · rintro ⟨χ, ⟨hχ, hlin⟩, rfl⟩
    exact ⟨⟨χ, hχ, rfl⟩, (linear_affineFunctionalTransport_eq_iff e χ ψ).mpr hlin⟩

/-- Bounds on differences throughout the whole apartment are unchanged. -/
theorem boundedDerivativeFiber_transportedRoots (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (ψ : A →ᵃ[ℝ] ℝ) (M : ℝ) :
    {φ | φ ∈ transportedRoots e Ψ ∧
        φ.linear = (affineFunctionalTransport e ψ).linear ∧
          ∀ y : B, |φ y - affineFunctionalTransport e ψ y| ≤ M} =
      affineFunctionalTransport e ''
        {φ | φ ∈ Ψ ∧ φ.linear = ψ.linear ∧ ∀ x : A, |φ x - ψ x| ≤ M} := by
  ext φ
  constructor
  · rintro ⟨⟨χ, hχ, rfl⟩, hlin, hb⟩
    refine ⟨χ, ⟨hχ, (linear_affineFunctionalTransport_eq_iff e χ ψ).mp hlin, ?_⟩, rfl⟩
    intro x
    simpa only [affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply] using hb (e x)
  · rintro ⟨χ, ⟨hχ, hlin, hb⟩, rfl⟩
    exact ⟨⟨χ, hχ, rfl⟩, (linear_affineFunctionalTransport_eq_iff e χ ψ).mpr hlin,
      fun y => hb (e.symm y)⟩

/-- Every rank-zero-compatible affine root system transports to such a system. -/
theorem IsAffineRootSystemWithRankZero.transport {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] B) :
    IsAffineRootSystemWithRankZero (transportedRoots e Ψ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      Submodule.span ℝ (derivativeRoots (transportedRoots e Ψ)) =
          (Submodule.span ℝ (derivativeRoots Ψ)).map
            (derivativeTransport e).toLinearMap := by
        rw [Submodule.map_span, derivativeRoots_transportedRoots]
        rfl
      _ = ⊤ := by
        rw [hΨ.span_derivativeRoots_eq_top, Submodule.map_top]
        exact LinearMap.range_eq_top.mpr (derivativeTransport e).surjective
  · rintro _ ⟨ψ, hψ, rfl⟩ he
    apply hΨ.linear_ne_zero ψ hψ
    apply (derivativeTransport e).injective
    rw [map_zero]
    exact he
  · rw [derivativeRoots_transportedRoots]
    exact hΨ.finite_derivativeRoots.image _
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
    exact ⟨e.linear v, (isCoroot_transport_iff e Ψ ψ v).mpr hv⟩
  · rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨φ, hφ, rfl⟩ w hw
    obtain ⟨v, rfl⟩ := e.linear.surjective w
    obtain ⟨n, hn⟩ := hΨ.coroot_integral ψ hψ φ hφ v
      ((isCoroot_transport_iff e Ψ φ v).mp hw)
    exact ⟨n, by simpa only [affineFunctionalTransport_linear_apply] using hn⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    rw [derivativeFiber_transportedRoots]
    exact (hΨ.infinite_fiber ψ hψ).image (affineFunctionalTransport e).injective.injOn
  · rintro _ ⟨ψ, hψ, rfl⟩ M
    rw [boundedDerivativeFiber_transportedRoots]
    exact (hΨ.finite_bounded ψ hψ M).image _

/-- Transport in the inverse direction cancels on each affine functional. -/
@[simp] theorem affineFunctionalTransport_symm_apply (e : A ≃ᵃ[ℝ] B)
    (ψ : A →ᵃ[ℝ] ℝ) :
    affineFunctionalTransport e.symm (affineFunctionalTransport e ψ) = ψ := by
  ext x
  change ψ (e.symm (e x)) = ψ x
  rw [AffineEquiv.symm_apply_apply]

/-- Transport in the inverse direction cancels on the whole root set. -/
@[simp] theorem transportedRoots_symm (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    transportedRoots e.symm (transportedRoots e Ψ) = Ψ := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    simpa only [affineFunctionalTransport_symm_apply] using hφ
  · intro hψ
    exact ⟨affineFunctionalTransport e ψ, ⟨ψ, hψ, rfl⟩,
      affineFunctionalTransport_symm_apply e ψ⟩

/-- The equivalence of actual sets satisfying every rank-zero-compatible root-system axiom. -/
def affineRootSystemTransportEquiv (e : A ≃ᵃ[ℝ] B) :
    {Ψ : Set (A →ᵃ[ℝ] ℝ) // IsAffineRootSystemWithRankZero Ψ} ≃
      {Φ : Set (B →ᵃ[ℝ] ℝ) // IsAffineRootSystemWithRankZero Φ} where
  toFun Ψ := ⟨transportedRoots e Ψ.val, Ψ.property.transport e⟩
  invFun Φ := ⟨transportedRoots e.symm Φ.val, Φ.property.transport e.symm⟩
  left_inv Ψ := Subtype.ext (transportedRoots_symm e Ψ.val)
  right_inv Φ := Subtype.ext (by
    have he : e.symm.symm = e := by ext x; rfl
    simpa only [he] using transportedRoots_symm e.symm Φ.val)

end Langlands.Geometry.Building.AffineRootSystem
