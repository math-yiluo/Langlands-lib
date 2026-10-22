import Langlands.Weil.Representation.UnitaryStatement
import Langlands.Representation.Unitary.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace Langlands.FiniteRepresentation

universe uG uV uU

variable {G : Type uG} [Group G]

/-- The finite-dimensional predicate repackages an invariant positive form. -/
theorem isUnitary_iff_isUnitarizable (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    IsUnitary A ↔ Langlands.IsUnitarizable A.representation := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨{ toInnerProductCore := h, invariant := hh }⟩
  · rintro ⟨h⟩
    exact ⟨h.toInnerProductCore, h.invariant⟩

/-- An invariant positive form pulls back along a genuine intertwining equivalence. -/
theorem isUnitary_of_equiv {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uU} ℂ G}
    (e : Equiv A B) (hB : IsUnitary B) : IsUnitary A := by
  exact (isUnitary_iff_isUnitarizable A).mpr
    ((Langlands.isUnitarizable_iff_of_equiv e).mpr
      ((isUnitary_iff_isUnitarizable B).mp hB))

/-- Unitarizability is invariant under equivalences across carrier universes. -/
theorem unitaryIsomorphismInvariance :
    UnitaryIsomorphismInvariance.{uG, uV, uU} := by
  intro G _ A B ⟨e⟩
  exact ⟨isUnitary_of_equiv e.symm, isUnitary_of_equiv e⟩

private theorem core_twist_inner (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (χ : G →* ℂˣ) (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (h : InnerProductSpace.Core ℂ A) (g : G) (v w : A) :
    h.inner ((twist χ A).representation g v) ((twist χ A).representation g w) =
      h.inner (A.representation g v) (A.representation g w) := by
  let := h
  change h.inner ((χ g : ℂ) • A.representation g v)
    ((χ g : ℂ) • A.representation g w) = _
  rw [h.smul_left]
  rw [show h.inner (A.representation g v) ((χ g : ℂ) • A.representation g w) =
    (χ g : ℂ) * h.inner (A.representation g v) (A.representation g w) from
      InnerProductSpace.Core.inner_smul_right _ _]
  rw [← mul_assoc, Complex.conj_mul', hχ g]
  simp

/-- A modulus-one twist preserves and reflects the same invariant positive form. -/
theorem unitaryTwisting : UnitaryTwisting.{uG, uV} := by
  intro G _ A χ hχ
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, fun g v w => (core_twist_inner A χ hχ h g v w).symm.trans (hh g v w)⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, fun g v w => (core_twist_inner A χ hχ h g v w).trans (hh g v w)⟩

/-- The contragredient of a unitarizable finite-dimensional representation is unitarizable. -/
theorem isUnitary_dual (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hA : IsUnitary A) : IsUnitary (dual A) := by
  change ∃ hd : InnerProductSpace.Core ℂ (Module.Dual ℂ A),
    ∀ g ℓ m, hd.inner (A.representation.dual g ℓ) (A.representation.dual g m) =
      hd.inner ℓ m
  obtain ⟨h, hh⟩ := hA
  let := h
  let : NormedAddCommGroup A := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ A := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ A)
  let : CompleteSpace A := FiniteDimensional.complete ℂ A
  let f : Module.Dual ℂ A ≃ₗ⋆[ℂ] A :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ A ≃ₗ[ℂ] StrongDual ℂ A).trans
      (InnerProductSpace.toDual ℂ A).symm.toLinearEquiv
  have hf (ℓ : Module.Dual ℂ A) (v : A) : inner ℂ (f ℓ) v = ℓ v :=
    InnerProductSpace.toDual_symm_apply
  have hfg (g : G) (ℓ : Module.Dual ℂ A) :
      f (A.representation.dual g ℓ) = A.representation g (f ℓ) := by
    apply ext_inner_right ℂ
    intro v
    rw [hf]
    change ℓ (A.representation g⁻¹ v) = h.inner (A.representation g (f ℓ)) v
    rw [← hf]
    simpa only [Representation.self_inv_apply] using
      (hh g (f ℓ) (A.representation g⁻¹ v)).symm
  let hd : InnerProductSpace.Core ℂ (Module.Dual ℂ A) :=
    { inner := fun ℓ m => inner ℂ (f m) (f ℓ)
      conj_inner_symm := fun ℓ m => inner_conj_symm _ _
      re_inner_nonneg := fun ℓ => inner_self_nonneg
      add_left := fun ℓ m n => by simp only [map_add, inner_add_right]
      smul_left := fun ℓ m c => by simp only [map_smulₛₗ, inner_smul_right]
      definite := fun ℓ hℓ => f.injective (by simpa using (inner_self_eq_zero.mp hℓ)) }
  refine ⟨hd, ?_⟩
  intro g ℓ m
  change inner ℂ (f (A.representation.dual g m)) (f (A.representation.dual g ℓ)) =
    inner ℂ (f m) (f ℓ)
  rw [hfg, hfg]
  exact hh g _ _

/-- Algebraic duality preserves and reflects unitarizability. -/
theorem unitaryDuality : UnitaryDuality.{uG, uV} := by
  intro G _ A
  constructor
  · intro h
    let e : Equiv A (dual (dual A)) :=
      { toLinearEquiv := Module.evalEquiv ℂ A
        isIntertwining' := (Langlands.bidualIntertwining A.representation).isIntertwining' }
    exact isUnitary_of_equiv e (isUnitary_dual (dual A) h)
  · exact isUnitary_dual A

/-- The complete published unitarizability operation target. -/
theorem unitaryOperations : UnitaryOperations.{uG, uV, uU} :=
  ⟨unitaryIsomorphismInvariance, unitaryDuality, unitaryTwisting⟩

end Langlands.FiniteRepresentation
