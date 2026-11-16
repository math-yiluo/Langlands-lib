import Langlands.Automorphic.Contragredient

/-!
# Uniqueness of contragredient realizations

Two actual automorphic realizations `T` and `T'` that both realize the contragredient of
the same realization `S` are equivalent: the composite of the two partial-map bijections
onto the contragredient functionals of `S` is a linear bijection `T ≃ T'` intertwining the
finite, compact and differential operators.
-/

noncomputable section

universe u

namespace Langlands.Automorphic

open NumberField Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance contragredientUniqueRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance contragredientUniqueContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientUniqueSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientUniqueFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance contragredientUniqueStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance contragredientUniqueSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

variable {S T T' : OperatorRealization F n}

section Comparison

variable {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ} {B' : S.Space →ₗ[ℂ] T'.Space →ₗ[ℂ] ℂ}

/-- A linear map `L : T → T'` compatible with two invariant pairings on `S`, the second
nondegenerate in its second variable, commutes with the finite actions. -/
theorem IsInvariantPairing.comparison_finite (hB : S.IsInvariantPairing T B)
    (hB' : S.IsInvariantPairing T' B') (hinj : Function.Injective B'.flip)
    (L : T.Space →ₗ[ℂ] T'.Space) (hL : ∀ x, B'.flip (L x) = B.flip x)
    (d : FiniteAdelicGL F n) (x : T.Space) :
    L (T.finiteRepresentation d x) = T'.finiteRepresentation d (L x) := by
  apply hinj
  exact (hL _).trans ((hB.flip_finite d x).trans
    ((congrArg (S.finiteRepresentation.dual d) (hL x)).symm.trans
      (hB'.flip_finite d (L x)).symm))

/-- A linear map `L : T → T'` compatible with two invariant pairings on `S`, the second
nondegenerate in its second variable, commutes with the compact actions. -/
theorem IsInvariantPairing.comparison_compact (hB : S.IsInvariantPairing T B)
    (hB' : S.IsInvariantPairing T' B') (hinj : Function.Injective B'.flip)
    (L : T.Space →ₗ[ℂ] T'.Space) (hL : ∀ x, B'.flip (L x) = B.flip x)
    (k : standardInfiniteCompact F n) (x : T.Space) :
    L (T.compactRepresentation k x) = T'.compactRepresentation k (L x) := by
  apply hinj
  exact (hL _).trans ((hB.flip_compact k x).trans
    ((congrArg (S.compactRepresentation.dual k) (hL x)).symm.trans
      (hB'.flip_compact k (L x)).symm))

/-- A linear map `L : T → T'` compatible with two invariant pairings on `S`, the second
nondegenerate in its second variable, commutes with the real Lie algebra actions. -/
theorem IsInvariantPairing.comparison_lieAction (hB : S.IsInvariantPairing T B)
    (hB' : S.IsInvariantPairing T' B') (hinj : Function.Injective B'.flip)
    (L : T.Space →ₗ[ℂ] T'.Space) (hL : ∀ x, B'.flip (L x) = B.flip x)
    (X : ArchimedeanGL.RealLieAlgebra F n) (x : T.Space) :
    L (T.lieAction X x) = T'.lieAction X (L x) := by
  apply hinj
  exact (hL _).trans ((hB.flip_lieAction X x).trans
    ((congrArg (fun l : Module.Dual ℂ S.Space => -(l.comp (S.lieAction X))) (hL x)).symm.trans
      (hB'.flip_lieAction X (L x)).symm))

end Comparison

set_option maxHeartbeats 2000000 in
/-- A linear bijection commuting with the real Lie algebra actions commutes with the
actions of the generators `ι(Y)`, `Y ∈ ℂ ⊗_ℝ 𝔤`, of the enveloping algebra; the generator
`z ⊗ X` is `z • (1 ⊗ X)`. -/
theorem envelopingGenerator_comm_of_lieAction (e : T.Space ≃ₗ[ℂ] T'.Space)
    (hlie : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (x : T.Space),
      e (T.lieAction X x) = T'.lieAction X (e x))
    (Y : ArchimedeanGL.ComplexLieAlgebra F n) (x : T.Space) :
    e (T.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) x) =
      T'.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) (e x) := by
  revert x
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    intro x
    have hz : (z ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) =
        z • ArchimedeanGL.complexify F n X := by
      rw [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hX := hlie X x
    change e (T.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ
        (ArchimedeanGL.complexify F n X)) x) =
      T'.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ
        (ArchimedeanGL.complexify F n X)) (e x) at hX
    have h1 : (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) :
        ArchimedeanGL.EnvelopingAlgebra F n) =
        z • UniversalEnvelopingAlgebra.ι ℂ (ArchimedeanGL.complexify F n X) := by
      rw [hz]
      exact map_smul _ _ _
    have h2 : ∀ (R : OperatorRealization F n) (y : R.Space),
        R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X)) y =
          z • R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ
            (ArchimedeanGL.complexify F n X)) y := by
      intro R y
      rw [h1, map_smul]
      rfl
    exact (congrArg e (h2 T x)).trans ((e.map_smul _ _).trans
      ((congrArg (z • ·) hX).trans (h2 T' (e x)).symm))
  | add Y₁ Y₂ h₁ h₂ =>
    intro x
    have h3 : ∀ (R : OperatorRealization F n) (y : R.Space),
        R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ (Y₁ + Y₂)) y =
          R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y₁) y +
            R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y₂) y := by
      intro R y
      rw [map_add, map_add]
      rfl
    exact (congrArg e (h3 T x)).trans ((e.map_add _ _).trans
      ((congrArg₂ (· + ·) (h₁ x) (h₂ x)).trans (h3 T' (e x)).symm))

set_option maxHeartbeats 2000000 in
/-- A linear bijection commuting with the real Lie algebra actions commutes with the
whole enveloping algebra action: both `a ↦ e ∘ T(a) ∘ e⁻¹` and `a ↦ T'(a)` are algebra
homomorphisms out of the universal enveloping algebra of the complexification, and they
agree on its generators. -/
theorem envelopingAction_comm_of_lieAction (e : T.Space ≃ₗ[ℂ] T'.Space)
    (hlie : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (x : T.Space),
      e (T.lieAction X x) = T'.lieAction X (e x))
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (x : T.Space) :
    e (T.envelopingAction a x) = T'.envelopingAction a (e x) := by
  have key : ((e.conjAlgEquiv ℂ).toAlgHom.comp T.envelopingAction :
      ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ T'.Space) =
        T'.envelopingAction := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro Y
    apply LinearMap.ext
    intro y
    change e (T.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) (e.symm y)) =
      T'.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) y
    exact (envelopingGenerator_comm_of_lieAction e hlie Y (e.symm y)).trans
      (congrArg _ (e.apply_symm_apply y))
  have h := LinearMap.congr_fun (AlgHom.congr_fun key a) (e x)
  change e (T.envelopingAction a (e.symm (e x))) = T'.envelopingAction a (e x) at h
  exact (congrArg (fun y => e (T.envelopingAction a y)) (e.symm_apply_apply x)).symm.trans h

set_option maxHeartbeats 2000000 in
/-- **Uniqueness of the contragredient.** Two realizations of the contragredient of the
same realization `S` are equivalent. -/
theorem IsContragredientOf.nonempty_equivalence (h : T.IsContragredientOf S)
    (h' : T'.IsContragredientOf S) : Nonempty (T.Equivalence T') := by
  obtain ⟨B, hB, hBc, hinj, hsurj⟩ := h
  obtain ⟨B', hB', hBc', hinj', hsurj'⟩ := h'
  have hrange : LinearMap.range B.flip = LinearMap.range B'.flip := by
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hsurj' _ (hBc x)
      exact ⟨x', hx'⟩
    · rintro ⟨x', rfl⟩
      obtain ⟨x, hx⟩ := hsurj _ (hBc' x')
      exact ⟨x, hx⟩
  let e : T.Space ≃ₗ[ℂ] T'.Space :=
    (LinearEquiv.ofInjective B.flip hinj).trans
      ((LinearEquiv.ofEq _ _ hrange).trans (LinearEquiv.ofInjective B'.flip hinj').symm)
  have he : ∀ x, B'.flip (e x) = B.flip x := fun x =>
    LinearEquiv.ofInjective_symm_apply (f := B'.flip) (h := hinj')
      (LinearEquiv.ofEq _ _ hrange (LinearEquiv.ofInjective B.flip hinj x))
  have hlie := hB.comparison_lieAction hB' hinj' e.toLinearMap he
  exact ⟨Equivalence.ofGenerators e
    (hB.comparison_finite hB' hinj' e.toLinearMap he)
    (hB.comparison_compact hB' hinj' e.toLinearMap he)
    (envelopingAction_comm_of_lieAction e hlie)⟩

end OperatorRealization

end Langlands.Automorphic
