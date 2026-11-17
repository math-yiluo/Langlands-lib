import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.AffineCartierSmoothProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The degree of an isogeny in characteristic zero counts its kernel points

Over an algebraically closed field of characteristic zero, the kernel of an isogeny of abelian
schemes is finite and smooth, hence reduced. A finite reduced algebra over an algebraically
closed field is étale, so the number of rational points of the kernel equals the rank of its
coordinate algebra. That rank is the rank of the isogeny at the unit point, and the rank of a
finite flat morphism to a connected scheme is constant.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.IsogenyKernelCard

open Langlands.AlgebraicGeometry.FiniteEtale

/-- A finite reduced algebra over an algebraically closed field is formally étale. -/
theorem formallyEtale_of_isReduced (K A : Type u) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.FormallyEtale K A := by
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let : ∀ I : MaximalSpectrum A, Field (A ⧸ I.asIdeal) := fun I =>
    @Ideal.Quotient.field _ _ I.asIdeal I.isMaximal
  rw [Algebra.FormallyEtale.iff_exists_algEquiv_prod]
  exact ⟨MaximalSpectrum A, inferInstance, fun I => A ⧸ I.asIdeal, inferInstance,
    inferInstance, (IsArtinianRing.equivPi A).restrictScalars K, fun I => inferInstance⟩

/-- Over an algebraically closed field, the rational points of a finite flat reduced scheme are
counted by the rank of its structure morphism. -/
theorem natCard_sections_eq_finrank_of_isReduced {X : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsFinite f] [Flat f] [IsReduced X]
    (x : Spec (.of K)) :
    Nat.card {z : Spec (.of K) ⟶ X // z ≫ f = 𝟙 _} = f.finrank x := by
  let := coordinateAlgebra f
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite K Γ(X, ⊤) := by
    exact RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : Algebra.FormallyEtale K Γ(X, ⊤) := formallyEtale_of_isReduced K Γ(X, ⊤)
  exact (Nat.card_congr (sectionsAlgHomEquiv f)).trans
    ((natCard_algHom_eq_finrank K Γ(X, ⊤)).trans (homFinrank_eq_coordinateFinrank f x).symm)

/-- Points over the base of a scheme over the base are sections of its structure morphism. -/
def overPointsEquiv {S : Scheme.{u}} (X : Over S) :
    (Over.mk (𝟙 S) ⟶ X) ≃ {z : S ⟶ X.left // z ≫ X.hom = 𝟙 S} where
  toFun z := ⟨z.left, by simp⟩
  invFun z := Over.homMk z.1 z.2
  left_inv z := by
    apply Over.OverMorphism.ext
    rfl
  right_inv z := rfl

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- The rank of an isogeny over an algebraically closed field of characteristic zero, at every
point, is the number of rational points of its kernel. -/
theorem finrank_eq_natCard_ker
    {A B : AbelianScheme (Spec (CommRingCat.of k))} (α : A ⟶ B) (hα : IsIsogeny α)
    (y : B.X.left) :
    (hom α).finrank y =
      Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker := by
  obtain ⟨hfin, hflat, -⟩ := (isIsogeny_iff α).mp hα
  let f := groupHom α
  have : IsFinite f.hom.hom.left := hfin
  have : Flat f.hom.hom.left := hflat
  have hpb := GroupScheme.kernel_isPullback_scheme f
  let K := (GroupScheme.kernel f).X
  have : IsFinite K.hom := MorphismProperty.of_isPullback hpb inferInstance
  have : Flat K.hom := MorphismProperty.of_isPullback hpb inferInstance
  have : Smooth K.hom := GroupScheme.affineCartierSmooth k (GroupScheme.kernel f)
    inferInstance inferInstance
  have : IsReduced K.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k K.left K.hom
  have := field_isIntegral B
  have := field_isNoetherian B
  let x : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  -- the rank is constant on the connected scheme `B`
  have hconst : (hom α).finrank y = (hom α).finrank (η[B.X].left x) :=
    (Scheme.Hom.isLocallyConstant_finrank (hom α)).apply_eq_of_preconnectedSpace _ _
  rw [hconst]
  change f.hom.hom.left.finrank _ = _
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb x,
    ← natCard_sections_eq_finrank_of_isReduced K.hom x,
    ← Nat.card_congr (overPointsEquiv K)]
  exact Nat.card_congr (GroupScheme.kernelPointsEquiv f (Over.mk (𝟙 _))).toEquiv

end Langlands.AbelianScheme.IsogenyKernelCard
