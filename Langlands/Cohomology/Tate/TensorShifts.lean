import Langlands.Cohomology.Tate.ShiftDefinitions
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Abelian.ShortExact

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The linear automorphism given by an element of a group representation. -/
def actionLinearEquiv (A : Rep.{u} R G) (g : G) : A ≃ₗ[R] A :=
  LinearEquiv.ofLinearMap (A.ρ g) (A.ρ g⁻¹)
    (by ext a; simp [← Module.End.mul_apply, ← map_mul])
    (by ext a; simp [← Module.End.mul_apply, ← map_mul])

/-- The finite-product tensor comparison, twisted by the action on the second coefficient. -/
def coinducedTensorCoordinates (A B : Rep.{u} R G) :
    (coinduced A ⊗[R] B) ≃ₗ[R] coinduced (A ⊗ B) := by
  classical
  exact (TensorProduct.congr (coinducedFunctions A).symm (LinearEquiv.refl R B)).trans
    ((TensorProduct.piLeft R B (fun _ : G => A)).trans
      ((LinearEquiv.piCongrRight (fun g : G =>
        TensorProduct.congr (LinearEquiv.refl R A) (actionLinearEquiv B g))).trans
        (coinducedFunctions (A ⊗ B))))

lemma coinducedTensorCoordinates_tmul (A B : Rep.{u} R G)
    (f : coinduced A) (b : B) (g : G) :
    (coinducedTensorCoordinates A B (f ⊗ₜ[R] b)).1 g = f.1 g ⊗ₜ[R] B.ρ g b := by
  classical
  simp [coinducedTensorCoordinates, TensorProduct.piLeft, coinducedFunctions, actionLinearEquiv]

/-- Tensoring a coinduced coefficient by an arbitrary coefficient remains coinduced. -/
def coinducedTensorIso (A B : Rep.{u} R G) :
    coinduced A ⊗ B ≅ coinduced (A ⊗ B) :=
  Rep.mkIso (Representation.Equiv.mk (coinducedTensorCoordinates A B) (fun h => by
    apply TensorProduct.ext'
    intro f b
    change coinducedTensorCoordinates A B
      (TensorProduct.map ((coinduced A).ρ h) (B.ρ h) (f ⊗ₜ[R] b)) =
      (coinduced (A ⊗ B)).ρ h (coinducedTensorCoordinates A B (f ⊗ₜ[R] b))
    rw [TensorProduct.map_tmul]
    apply Subtype.ext
    funext g
    change (coinducedTensorCoordinates A B (((coinduced A).ρ h f) ⊗ₜ[R] B.ρ h b)).1 g =
      (coinducedTensorCoordinates A B (f ⊗ₜ[R] b)).1 (g * h)
    rw [coinducedTensorCoordinates_tmul, coinducedTensorCoordinates_tmul]
    change f.1 (g * h) ⊗ₜ[R] B.ρ g (B.ρ h b) =
      f.1 (g * h) ⊗ₜ[R] B.ρ (g * h) b
    rw [map_mul, Module.End.mul_apply]))

lemma coinducedTensor_tate_isZero (A B : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (coinduced A ⊗ B) n) :=
  (coinduced_tate_isZero (A ⊗ B) n).of_iso
    ((tateCohomologyFunctor n).mapIso (coinducedTensorIso A B))

lemma tensorCoinduced_tate_isZero (A B : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (A ⊗ coinduced B) n) :=
  (coinducedTensor_tate_isZero B A n).of_iso
    ((tateCohomologyFunctor n).mapIso (β_ A (coinduced B)))

omit [Fintype G] in
/-- A scalar splitting survives tensoring on the right, without a flatness assumption. -/
def scalarSplitting_tensorRight (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (B : Rep.{u} R G) :
    ((S.map (MonoidalCategory.tensorRight B)).map
      (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting := by
  change ((S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).map
    (MonoidalCategory.tensorRight (ModuleCat.of R B))).Splitting
  exact s.map _

omit [Fintype G] in
/-- A scalar splitting survives tensoring on the left, without a flatness assumption. -/
def scalarSplitting_tensorLeft (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (A : Rep.{u} R G) :
    ((S.map (MonoidalCategory.tensorLeft A)).map
      (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting := by
  change ((S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).map
    (MonoidalCategory.tensorLeft (ModuleCat.of R A))).Splitting
  exact s.map _

omit [Fintype G] in
lemma scalarSplit_tensorRight_shortExact (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (B : Rep.{u} R G) :
    (S.map (MonoidalCategory.tensorRight B)).ShortExact := by
  let t := scalarSplitting_tensorRight S s B
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
    { exact := t.exact, mono_f := t.mono_f, epi_g := t.epi_g }

omit [Fintype G] in
lemma scalarSplit_tensorLeft_shortExact (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (A : Rep.{u} R G) :
    (S.map (MonoidalCategory.tensorLeft A)).ShortExact := by
  let t := scalarSplitting_tensorLeft S s A
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
    { exact := t.exact, mono_f := t.mono_f, epi_g := t.epi_g }

/-- The connecting isomorphism for shifting the first tensor coefficient upwards. -/
def tensorShiftUpLeftIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (shiftUp A ⊗ B) n ≅ tateCohomology (A ⊗ B) (n + 1) := by
  let hS := scalarSplit_tensorRight_shortExact (shiftUpSequence A)
    (shiftUpSequence_scalarSplitting A) B
  have := tate_delta_isIso hS n
    (coinducedTensor_tate_isZero A B n) (coinducedTensor_tate_isZero A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

/-- The connecting isomorphism for shifting the second tensor coefficient upwards. -/
def tensorShiftUpRightIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (A ⊗ shiftUp B) n ≅ tateCohomology (A ⊗ B) (n + 1) := by
  let hS := scalarSplit_tensorLeft_shortExact (shiftUpSequence B)
    (shiftUpSequence_scalarSplitting B) A
  have := tate_delta_isIso hS n
    (tensorCoinduced_tate_isZero A B n) (tensorCoinduced_tate_isZero A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

/-- The connecting isomorphism for shifting the first tensor coefficient downwards. -/
def tensorShiftDownLeftIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (A ⊗ B) n ≅ tateCohomology (shiftDown A ⊗ B) (n + 1) := by
  let hS := scalarSplit_tensorRight_shortExact (shiftDownSequence A)
    (shiftDownSequence_scalarSplitting A) B
  have := tate_delta_isIso hS n
    (coinducedTensor_tate_isZero A B n) (coinducedTensor_tate_isZero A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

/-- The connecting isomorphism for shifting the second tensor coefficient downwards. -/
def tensorShiftDownRightIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (A ⊗ B) n ≅ tateCohomology (A ⊗ shiftDown B) (n + 1) := by
  let hS := scalarSplit_tensorLeft_shortExact (shiftDownSequence B)
    (shiftDownSequence_scalarSplitting B) A
  have := tate_delta_isIso hS n
    (tensorCoinduced_tate_isZero A B n) (tensorCoinduced_tate_isZero A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

end Langlands.Tate
