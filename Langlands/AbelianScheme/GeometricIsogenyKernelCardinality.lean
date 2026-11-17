import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Mathlib.RingTheory.Etale.Field

/-! # Geometric isogeny degree and actual kernel points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

private theorem formallyEtale_of_finite_reduced
    (k B : Type u) [Field k] [CharZero k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [_root_.IsReduced B] : Algebra.FormallyEtale k B := by
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let e := (IsArtinianRing.equivPi B).restrictScalars k
  have : Algebra.FormallyEtale k (∀ m : MaximalSpectrum B, B ⧸ m.asIdeal) := by
    rw [Algebra.FormallyEtale.pi_iff]
    intro m
    let := Ideal.Quotient.field m.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable k _
  exact Algebra.FormallyEtale.of_equiv e.symm

/-- A finite flat group scheme in characteristic zero has as many actual
geometric sections as its native rank. -/
theorem finiteGroup_natCard_sections_eq_finrank
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsFinite G.X.hom] [Flat G.X.hom] (x : Spec (CommRingCat.of k)) :
    Nat.card {z : Spec (CommRingCat.of k) ⟶ G.X.left // z ≫ G.X.hom = 𝟙 _} =
      G.X.hom.finrank x := by
  let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra G.X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : AlgebraicGeometry.IsReduced G.X.left :=
    GroupScheme.AffineCartierSmoothProof.isReduced G
  have : Module.Finite k Γ(G.X.left, ⊤) := by
    exact RingHom.Finite.comp G.X.hom.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have : Algebra.FormallyEtale k Γ(G.X.left, ⊤) :=
    formallyEtale_of_finite_reduced k _
  calc
    _ = Nat.card (Γ(G.X.left, ⊤) →ₐ[k] k) :=
      Nat.card_congr (Langlands.AlgebraicGeometry.FiniteEtale.sectionsAlgHomEquiv G.X.hom)
    _ = Module.finrank k Γ(G.X.left, ⊤) :=
      Langlands.AlgebraicGeometry.FiniteEtale.natCard_algHom_eq_finrank k _
    _ = G.X.hom.finrank x :=
      (Langlands.AlgebraicGeometry.FiniteEtale.homFinrank_eq_coordinateFinrank G.X.hom x).symm

variable {k : Type u} [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k))) (f : End A)

/-- Actual scheme sections of the kernel identify with the kernel of the
actual homomorphism on geometric points. -/
def kernelSectionsEquiv :
    {z : Spec (CommRingCat.of k) ⟶ (GroupScheme.kernel (groupHom f)).X.left //
      z ≫ (GroupScheme.kernel (groupHom f)).X.hom = 𝟙 _} ≃
      (GroupScheme.pointsHom (groupHom f) (Over.mk (𝟙 _))).ker :=
  (show {z : Spec (CommRingCat.of k) ⟶ (GroupScheme.kernel (groupHom f)).X.left //
      z ≫ (GroupScheme.kernel (groupHom f)).X.hom = 𝟙 _} ≃
      (Over.mk (𝟙 _) ⟶ (GroupScheme.kernel (groupHom f)).X) from
    { toFun z := Over.homMk z.val z.property
      invFun z := ⟨z.left, z.w⟩
      left_inv _ := rfl
      right_inv _ := rfl }).trans
    (GroupScheme.kernelPointsEquiv (groupHom f) (Over.mk (𝟙 _))).toEquiv

/-- The cardinality of an actual isogeny's point kernel is its native rank at
its identity fibre. This uses characteristic zero, without a Tate comparison. -/
theorem natCard_kernel_eq_nativeRank [IsAlgClosed k] [CharZero k]
    (hf : GroupScheme.IsIsogeny (groupHom f)) (x : Spec (CommRingCat.of k)) :
    Nat.card (GroupScheme.pointsHom (groupHom f) (Over.mk (𝟙 _))).ker =
      (hom f).finrank (η[A.X].left x) := by
  have : IsFinite (hom f) := hf.1
  have : Flat (hom f) := hf.2.1
  have : IsFinite (GroupScheme.kernel (groupHom f)).X.hom :=
    MorphismProperty.of_isPullback (GroupScheme.kernel_isPullback_scheme (groupHom f))
      (inferInstance : IsFinite (hom f))
  have : Flat (GroupScheme.kernel (groupHom f)).X.hom :=
    MorphismProperty.of_isPullback (GroupScheme.kernel_isPullback_scheme (groupHom f))
      (inferInstance : Flat (hom f))
  rw [← Nat.card_congr (kernelSectionsEquiv A f),
    finiteGroup_natCard_sections_eq_finrank _ x]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _
    (GroupScheme.kernel_isPullback_scheme (groupHom f)) x

end Langlands.AbelianScheme
