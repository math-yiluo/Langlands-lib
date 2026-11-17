import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalContragredientExistenceProof

/-! # Nonzero invariant pairings on irreducible cuspidal realizations -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance invariantCriterionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance invariantCriterionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance invariantCriterionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance invariantCriterionFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance invariantCriterionStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance invariantCriterionSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

variable {S T D : OperatorRealization F n}

set_option maxHeartbeats 800000 in
/-- A linear map commuting with the real Lie actions commutes with the genuine
enveloping actions, without any injectivity or surjectivity assumption. -/
theorem envelopingAction_intertwines_of_lieAction (L : S.Space →ₗ[ℂ] T.Space)
    (hL : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (x : S.Space),
      L (S.lieAction X x) = T.lieAction X (L x))
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (x : S.Space) :
    L (S.envelopingAction a x) = T.envelopingAction a (L x) := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra F n)) a
  induction t using TensorAlgebra.induction generalizing x with
  | algebraMap c =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
  | «ι» Y =>
    change L (S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) x) =
      T.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) (L x)
    induction Y using TensorProduct.inductionOn with
    | tmul c X =>
      have hY : (c ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) =
          c • ArchimedeanGL.complexify F n X := by
        rw [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hι : (UniversalEnvelopingAlgebra.ι ℂ
          (c ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) :
          ArchimedeanGL.EnvelopingAlgebra F n) =
          c • UniversalEnvelopingAlgebra.ι ℂ (ArchimedeanGL.complexify F n X) := by
        rw [hY]
        exact map_smul _ _ _
      have haction : ∀ (R : OperatorRealization F n) (y : R.Space),
          R.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) y =
            c • R.lieAction X y := by
        intro R y
        rw [hι, map_smul]
        rfl
      exact (congrArg L (haction S x)).trans ((L.map_smul _ _).trans
        ((congrArg (c • ·) (hL X x)).trans (haction T (L x)).symm))
    | add Y Z hY hZ =>
      simp only [map_add, LinearMap.add_apply, hY, hZ]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Finite, compact and real Lie covariance suffice for a full-operator intertwiner. -/
def Intertwiner.ofLieGenerators (L : S.Space →ₗ[ℂ] T.Space)
    (hd : ∀ d x, L (S.finiteRepresentation d x) = T.finiteRepresentation d (L x))
    (hk : ∀ k x, L (S.compactRepresentation k x) = T.compactRepresentation k (L x))
    (hX : ∀ X x, L (S.lieAction X x) = T.lieAction X (L x)) :
    S.Intertwiner T :=
  Intertwiner.ofGenerators L hd hk (envelopingAction_intertwines_of_lieAction L hX)

variable {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}

/-- The partial map of any invariant pairing has smooth, compact-finite values. -/
theorem IsInvariantPairing.flip_isContragredientFunctional
    (hB : S.IsInvariantPairing T B) (x : T.Space) :
    S.IsContragredientFunctional (B.flip x) := by
  let Ld : T.finiteRepresentation.IntertwiningMap S.finiteRepresentation.dual :=
    { toLinearMap := B.flip
      isIntertwining' := fun d => LinearMap.ext (hB.flip_finite d) }
  let Lk : T.compactRepresentation.IntertwiningMap S.compactRepresentation.dual :=
    { toLinearMap := B.flip
      isIntertwining' := fun k => LinearMap.ext (hB.flip_compact k) }
  exact ⟨Langlands.isSmoothVector_map Ld (T.finiteRepresentation_isSmooth x),
    (T.compactRepresentation_isFiniteVector x).map Lk⟩

set_option maxHeartbeats 800000 in
/-- A nonzero invariant pairing with an irreducible realization is a contragredient
pairing if an irreducible realization of the contragredient is already available. -/
theorem IsInvariantPairing.isContragredientPairing_of_irreducible_contragredient
    (hB : S.IsInvariantPairing T B) (hB0 : B ≠ 0)
    (hT : T.IsIrreducible) (hD : D.IsIrreducible) (hDS : D.IsContragredientOf S) :
    S.IsContragredientPairing T B := by
  classical
  obtain ⟨C, hC, _, hCinj, hCsurj⟩ := hDS
  let e := LinearEquiv.ofInjective C.flip hCinj
  let R : T.Space →ₗ[ℂ] LinearMap.range C.flip :=
    B.flip.codRestrict _ fun x => hCsurj _ (hB.flip_isContragredientFunctional x)
  let L : T.Space →ₗ[ℂ] D.Space := e.symm.toLinearMap.comp R
  have hL : ∀ x, C.flip (L x) = B.flip x := fun x =>
    LinearEquiv.ofInjective_symm_apply (f := C.flip) (h := hCinj) (R x)
  let M : T.Intertwiner D := Intertwiner.ofLieGenerators L
    (hB.comparison_finite hC hCinj L hL)
    (hB.comparison_compact hC hCinj L hL)
    (hB.comparison_lieAction hC hCinj L hL)
  have hM0 : M ≠ 0 := by
    intro hM
    apply hB0
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    have hx : L x = 0 := congrArg (fun Q : T.Intertwiner D => Q x) hM
    have h := LinearMap.congr_fun (hL x) y
    simpa only [hx, map_zero, LinearMap.zero_apply, LinearMap.flip_apply] using h.symm
  let : T.representation.IsIrreducible := hT
  let : D.representation.IsIrreducible := hD
  have hbij : Function.Bijective M :=
    (Representation.IsIrreducible.bijective_or_eq_zero M).resolve_right hM0
  refine ⟨hB, hB.flip_isContragredientFunctional, ?_, ?_⟩
  · intro x y hxy
    apply hbij.1
    apply hCinj
    exact (hL x).trans (hxy.trans (hL y).symm)
  · intro l hl
    obtain ⟨z, hz⟩ := hCsurj l hl
    obtain ⟨x, hx⟩ := hbij.2 z
    refine ⟨x, ?_⟩
    exact (hL x).symm.trans ((congrArg C.flip hx).trans hz)

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable {S T : CuspidalOperatorRealization F r}

/-- Between irreducible cuspidal realizations, every nonzero invariant pairing
identifies the second realization with the full contragredient of the first. -/
theorem isContragredientPairing_of_nonzero_invariant
    {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}
    (hB : S.realization.IsInvariantPairing T.realization B) (hB0 : B ≠ 0) :
    S.realization.IsContragredientPairing T.realization B := by
  obtain ⟨D, hD⟩ := cuspidalContragredientExistence F r S
  exact hB.isContragredientPairing_of_irreducible_contragredient hB0
    T.irreducible D.irreducible hD

/-- It suffices to construct a nonzero invariant bilinear form. -/
theorem isContragredientOf_of_nonzero_invariant
    {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}
    (hB : S.realization.IsInvariantPairing T.realization B) (hB0 : B ≠ 0) :
    T.realization.IsContragredientOf S.realization :=
  ⟨B, isContragredientPairing_of_nonzero_invariant hB hB0⟩

end CuspidalOperatorRealization

/-- Internal criterion retaining the nonzero invariant pairing as an explicit premise. -/
def CuspidalNonzeroInvariantPairingCriterionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S T : CuspidalOperatorRealization F r)
    (B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ),
    S.realization.IsInvariantPairing T.realization B → B ≠ 0 →
      S.realization.IsContragredientPairing T.realization B

/-- The internal nonzero invariant pairing criterion holds in every field universe. -/
theorem cuspidalNonzeroInvariantPairingCriterion :
    CuspidalNonzeroInvariantPairingCriterionStatement.{u} := by
  intro F _ _ _ r S T B hB hB0
  exact CuspidalOperatorRealization.isContragredientPairing_of_nonzero_invariant hB hB0

end Langlands.Automorphic
