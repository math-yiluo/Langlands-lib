import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackAssembly
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.MultiplicationSign
import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # The degree of multiplication by `k` on an abelian variety -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.GroupScheme LineBundle

/-- The isomorphism class of a line bundle, for the proved tensor preservation. -/
local notation "cls" => LineBundle.isoClass pullbackTensorComparisonIsIso

/-- Pullback of isomorphism classes, for the proved tensor preservation. -/
local notation "pb" => LineBundle.pullbackHom pullbackTensorComparisonIsIso

section Symmetrization

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Multiplication by `-1` is an isomorphism of underlying schemes. -/
instance isIso_multiplication_neg_one_left :
    IsIso (multiplication A.toGrp (-1)).hom.hom.left :=
  inferInstanceAs (IsIso ((Grp.forget (Over S) ⋙ Over.forget S).map
    (multiplicationNegOneIso A.toGrp).hom))

/-- Multiplication by `-1` is an involution of the underlying scheme. -/
lemma multiplication_neg_one_left_comp :
    (multiplication A.toGrp (-1)).hom.hom.left ≫ (multiplication A.toGrp (-1)).hom.hom.left =
      𝟙 A.X.left :=
  congrArg (fun f => f.hom.hom.left) (multiplicationNegOneIso A.toGrp).hom_inv_id

/-- The symmetrization `H ⊗ (-1)^* H` of a line bundle `H`. -/
def symmetrization (H : LineBundle A.X.left) : LineBundle A.X.left :=
  LineBundle.tensor pullbackTensorComparisonIsIso H
    ((LineBundle.pullback (multiplication A.toGrp (-1)).hom.hom.left).obj H)

/-- The symmetrization of an ample line bundle is ample. -/
lemma isAmple_symmetrization (H : LineBundle A.X.left) (hH : H.IsAmple) :
    (symmetrization A H).IsAmple :=
  ampleTensor A.X.left H _ (symmetrization A H) ⟨Iso.refl _⟩ hH
    (closedImmersionPullbackAmple _ _ _ H inferInstance hH)

/-- The symmetrization is symmetric: `(-1)^* (H ⊗ (-1)^* H) ≅ H ⊗ (-1)^* H`. -/
lemma symmetrization_symmetric (H : LineBundle A.X.left) :
    Nonempty ((Scheme.Modules.pullback (multiplication A.toGrp (-1)).hom.hom.left).obj
      (symmetrization A H).obj ≅ (symmetrization A H).obj) := by
  have h : Nonempty ((LineBundle.pullback (multiplication A.toGrp (-1)).hom.hom.left).obj
      (symmetrization A H) ≅ symmetrization A H) := by
    refine (isoClass_eq_iff (preservation := pullbackTensorComparisonIsIso)).mp ?_
    change pb (multiplication A.toGrp (-1)).hom.hom.left
        (cls H * pb (multiplication A.toGrp (-1)).hom.hom.left (cls H)) =
      cls H * pb (multiplication A.toGrp (-1)).hom.hom.left (cls H)
    rw [map_mul, pullbackHom_comp_eq _ _ _ (multiplication_neg_one_left_comp A),
      pullbackHom_id, mul_comm]
  obtain ⟨e⟩ := h
  exact ⟨(LineBundle.forget _).mapIso e⟩

end Symmetrization

section Degree

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- A finite endomorphism of an abelian scheme over a field is locally of finite
presentation: the scheme is locally noetherian. -/
lemma locallyOfFinitePresentation_of_isFinite (f : A.X.left ⟶ A.X.left) [IsFinite f] :
    LocallyOfFinitePresentation f := by
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  infer_instance

/-- Multiplication by an integer `k` that is nonzero in the field is finite, flat and
locally of finite presentation. -/
lemma multiplication_finite_flat_of_ne_zero (k : ℕ) (hk : (k : K) ≠ 0) :
    IsFinite (multiplication A.toGrp (k : ℤ)).hom.hom.left ∧
      Flat (multiplication A.toGrp (k : ℤ)).hom.hom.left ∧
      LocallyOfFinitePresentation (multiplication A.toGrp (k : ℤ)).hom.hom.left := by
  obtain ⟨hfin, hflat, -⟩ := multiplication_isIsogeny_of_ne_zero A k hk
  exact ⟨hfin, hflat, @locallyOfFinitePresentation_of_isFinite _ _ A _ hfin⟩

/-- On an abelian variety of dimension `g` over an algebraically closed field which carries
an ample line bundle, multiplication by an integer `k` that is nonzero in the field has rank
`k ^ (2 * g)` at every point. The cube theorem is a hypothesis. -/
theorem finrank_multiplication_eq_of_ne_zero [IsAlgClosed K]
    (cube : FieldCubePullbackStatement.{u})
    (g : ℕ) (hg : A.HasRelativeDimension g) (H : LineBundle A.X.left) (hH : H.IsAmple)
    (k : ℕ) (hk : (k : K) ≠ 0) (x : A.X.left) :
    (multiplication A.toGrp (k : ℤ)).hom.hom.left.finrank x = k ^ (2 * g) := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
  obtain ⟨hfin, hflat, -⟩ := multiplication_finite_flat_of_ne_zero A k hk
  have hpow := fieldSymmetricMultiplicationPullbackOfCube cube K A.toGrp A.smooth A.proper
    A.geometricallyConnected (symmetrization A H) (symmetrization_symmetric A H) k hk0
  have h := polarizedFiniteFlatRank K A.X g hg inferInstance inferInstance
    (multiplication A.toGrp (k : ℤ)).hom.hom hfin hflat (symmetrization A H)
    (isAmple_symmetrization A H hH) (k * k) (Nat.mul_pos hk0 hk0) hpow x
  simpa only [← pow_two, ← pow_mul] using h

end Degree

end Langlands.AbelianScheme
