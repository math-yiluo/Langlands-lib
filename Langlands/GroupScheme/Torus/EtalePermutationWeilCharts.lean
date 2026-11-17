import Langlands.GroupScheme.Torus.EtalePermutationLocalSplitting
import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionSplit

/-! # Actual Weil charts from the invariant coefficient algebra -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.WeilCoefficientTensor

variable (R A E T : Type u) [CommRing R] [CommRing A] [CommRing E] [CommRing T]
  [Algebra R A] [Algebra R E] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
  (I : Type u) [Finite I] (e : A ⊗[R] E ≃ₐ[A] (I → A))

/-- The coefficient decomposition on every algebra over the chart ring. -/
def equiv : E ⊗[R] T ≃+* (I → T) :=
  (WeilGm.baseChangeTensorEquiv R A E T).trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R := A) (A₁ := T))).toRingEquiv.trans
      (WeilGm.piTensorEquiv (CommRingCat.of A) I T).toRingEquiv)

@[simp] theorem equiv_tmul (c : E) (t : T) :
    equiv R A E T I e (c ⊗ₜ[R] t) =
      fun i => algebraMap A T (e ((1 : A) ⊗ₜ[R] c) i) * t := by
  simp only [equiv, RingEquiv.trans_apply, WeilGm.baseChangeTensorEquiv_tmul]
  change WeilGm.piTensorEquiv (CommRingCat.of A) I T
    (e ((1 : A) ⊗ₜ[R] c) ⊗ₜ[A] t) = _
  rw [WeilGm.piTensorEquiv_tmul (CommRingCat.of A) I T]
  simp only [Algebra.smul_def]

end Langlands.GroupScheme.WeilCoefficientTensor

namespace Langlands.GroupScheme.FiniteAffinePermutationCoefficients

open EtalePermutationAtlas
open Langlands.AlgebraicGeometry
open AffineCoverCoefficientTensors

variable {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S}
  {α : Type u} [Finite α] (U : α → Scheme.{u}) [∀ a, IsAffine (U a)]
  (f : ∀ a, U a ⟶ S) (I : α → Type u) [∀ a, Finite (I a)]
  (e : ∀ a, (GroupScheme.baseChange (f a)).obj D ≅ splitTorus (U a) (I a))
  (H : ∀ a b, LocallyPermutes (f a) (f b) (e a) (e b))
  [∀ a, Flat (f a)] [Surjective (Sigma.desc f)]

instance invariantFinite : Module.Finite Γ(S, ⊤) (coaction U f I e H).invariants :=
  (coaction U f I e H).finite_invariants (coverRingMap_faithfullyFlat U f)
    (FiniteProductCoefficients.finite (fun a => Γ(U a, ⊤)) I)

instance invariantProjective : Module.Projective Γ(S, ⊤) (coaction U f I e H).invariants :=
  (coaction U f I e H).projective_invariants (coverRingMap_faithfullyFlat U f)
    (FiniteProductCoefficients.finite (fun a => Γ(U a, ⊤)) I)
    (FiniteProductCoefficients.etale (fun a => Γ(U a, ⊤)) I)

instance invariantEtale : Algebra.Etale Γ(S, ⊤) (coaction U f I e H).invariants :=
  (coaction U f I e H).etale_invariants (coverRingMap_faithfullyFlat U f)
    (FiniteProductCoefficients.etale (fun a => Γ(U a, ⊤)) I)

/-- The actual Weil group for the invariant coefficient algebra, pulled back
from the spectrum of the affine base's global-section ring. -/
def weilGroup : GroupScheme S :=
  (GroupScheme.baseChange S.isoSpec.hom).obj
    (WeilGm.groupScheme Γ(S, ⊤) (coaction U f I e H).invariants)

/-- The local coefficient algebra splitting gives an actual split chart of the
Weil group over the spectrum of the affine chart ring. -/
def specWeilChart (a : α) :
    (GroupScheme.baseChange (Spec.map (f a).appTop)).obj
        (WeilGm.groupScheme Γ(S, ⊤) (coaction U f I e H).invariants) ≅
      splitTorus (Spec Γ(U a, ⊤)) (I a) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact WeilGm.baseChangeIso (f a).appTop (coaction U f I e H).invariants ≪≫
    WeilGm.congrIso (localDescentEquiv U f I e H a) ≪≫ WeilGm.splitIso Γ(U a, ⊤) (I a)

set_option maxHeartbeats 800000 in
/-- The spectrum chart is the unit map of the actual coefficient tensor
decomposition on every relative test scheme. -/
theorem specWeilChart_hom_points (a : α) (T : Over (Spec Γ(U a, ⊤)))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map (f a).appTop)).obj
      (WeilGm.groupScheme Γ(S, ⊤) (coaction U f I e H).invariants)).X) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    splitTorus.pointsEquiv (I a) T (x ≫ (specWeilChart U f I e H a).hom.hom.hom) =
      MulEquiv.piUnits (Units.map
        (WeilCoefficientTensor.equiv Γ(S, ⊤) Γ(U a, ⊤) (coaction U f I e H).invariants
          (WeilGm.restrictedSections Γ(S, ⊤) Γ(U a, ⊤) T) (I a)
          (localDescentEquiv U f I e H a)).toMonoidHom
        (WeilGm.pointsEquiv Γ(S, ⊤) (coaction U f I e H).invariants
          ((Over.map (Spec.map (f a).appTop)).obj T)
          (GroupScheme.baseChangePointsEquiv (Spec.map (f a).appTop)
            (WeilGm.groupScheme Γ(S, ⊤) (coaction U f I e H).invariants) T x))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  simp only [specWeilChart, Iso.trans_hom, Grp.comp_hom_hom, ← Category.assoc]
  rw [WeilGm.splitIso_hom_points Γ(U a, ⊤) (I a)]
  rw [WeilGm.congrIso_hom_points (localDescentEquiv U f I e H a)]
  rw [WeilGm.baseChangeIso_hom_points (f a).appTop (coaction U f I e H).invariants]
  rfl

/-- Normalize each spectrum chart back to the actual affine chart scheme,
using naturality of the canonical affine isomorphisms. -/
def weilChart (a : α) :
    (GroupScheme.baseChange (f a)).obj (weilGroup U f I e H) ≅ splitTorus (U a) (I a) :=
  Descent.pullbackComparison S.isoSpec.hom (f a) (f a ≫ S.isoSpec.hom) rfl
      (WeilGm.groupScheme Γ(S, ⊤) (coaction U f I e H).invariants) ≪≫
    restrictChart (Spec.map (f a).appTop) (specWeilChart U f I e H a) (U a).isoSpec.hom
      (f a ≫ S.isoSpec.hom) (Scheme.isoSpec_hom_naturality (f a))

/-- The supplied torus chart and its invariant-algebra Weil chart give an
actual local group-scheme isomorphism. -/
def localWeilIso (a : α) :
    (GroupScheme.baseChange (f a)).obj D ≅
      (GroupScheme.baseChange (f a)).obj (weilGroup U f I e H) :=
  e a ≪≫ (weilChart U f I e H a).symm

end Langlands.GroupScheme.FiniteAffinePermutationCoefficients
