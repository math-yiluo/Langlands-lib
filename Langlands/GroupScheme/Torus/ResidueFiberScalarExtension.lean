import Langlands.GroupScheme.Torus.FiniteDiagonalizableFibers
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Dominance of scalar-extended residue-fiber morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

/-- An integral projection between affine integral schemes cannot hide failure
of dominance of a map from an affine scheme. -/
theorem isDominant_of_comp_integral {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom g] [IsDominant (f ≫ g)] :
    IsDominant f := by
  have : IsSchemeTheoreticallyDominant (f ≫ g) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hinj : Function.Injective (f ≫ g).appTop := (f ≫ g).app_injective ⊤
  let : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  have : Algebra.IsIntegral Γ(Z, ⊤) Γ(Y, ⊤) :=
    ⟨g.isIntegral_app ⊤ (isAffineOpen_top Z)⟩
  have hker : (RingHom.ker f.appTop.hom).under Γ(Z, ⊤) = ⊥ := by
    change Ideal.comap g.appTop.hom (RingHom.ker f.appTop.hom) = ⊥
    change RingHom.ker ((f ≫ g).appTop.hom) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hzero : RingHom.ker f.appTop.hom = ⊥ :=
    Ideal.eq_bot_of_under_eq_bot hker
  exact isDominant_of_of_appTop_injective
    ((RingHom.injective_iff_ker_eq_bot _).mpr hzero)

variable (k : Type u) [Field k] (A : Type u) [AddCommGroup A]
    (X Y : Over (Spec (CommRingCat.of k)))

/-- The actual restriction of a morphism to a residue fiber, with target also
extended to that residue field. -/
def residueFiberMorphism
    (p : X ⊗ (groupScheme (CommRingCat.of k) A).X ⟶ Y)
    (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    (Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)))).obj X ⟶
    (Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)))).obj Y :=
  Over.homMk
    (pullback.lift (residueFiberInclusion k A X P ≫ p.left)
      (pullback.snd X.hom (Spec.map
        (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)))) (by
      rw [Category.assoc, Over.w]
      dsimp only [residueFiberInclusion]
      simp [← pullback.condition]))
    (by simp)

@[simp] theorem residueFiberMorphism_fst
    (p : X ⊗ (groupScheme (CommRingCat.of k) A).X ⟶ Y)
    (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    (residueFiberMorphism k A X Y p P).left ≫ pullback.fst Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField))) =
        residueFiberInclusion k A X P ≫ p.left := by
  simp [residueFiberMorphism]

/-- For an affine geometrically integral target, a dominant product map
remains dominant into the scalar-extended target on some residue fiber. -/
theorem exists_isDominant_residueFiberMorphism [Finite A]
    [IsAffine X.left] [IsAffine Y.left] [GeometricallyIntegral Y.hom]
    (p : X ⊗ (groupScheme (CommRingCat.of k) A).X ⟶ Y)
    [IsDominant p.left] :
    ∃ P : PrimeSpectrum (AddMonoidAlgebra k A),
      IsDominant (residueFiberMorphism k A X Y p P).left := by
  have : IsIntegral Y.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton Y.hom
  obtain ⟨P, hP⟩ := exists_isDominant_residueFiber k A X p.left
  let b := Spec.map (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField))
  have : IsFinite b := by
    apply (IsFinite.SpecMap_iff _).mpr
    change (algebraMap k P.asIdeal.ResidueField).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  have : IsAffine ((Over.pullback b).obj X).left := by
    change IsAffine (pullback X.hom b)
    infer_instance
  have : IsAffine ((Over.pullback b).obj Y).left := by
    change IsAffine (pullback Y.hom b)
    infer_instance
  have : IsIntegral ((Over.pullback b).obj Y).left := by
    exact GeometricallyIntegral.geometrically_isIntegral (f := Y.hom) b _ _
      (.of_hasPullback _ _)
  have : IsDominant
      ((residueFiberMorphism k A X Y p P).left ≫ pullback.fst Y.hom b) := by
    simpa only [b, residueFiberMorphism_fst] using hP
  exact ⟨P, isDominant_of_comp_integral
    (residueFiberMorphism k A X Y p P).left (pullback.fst Y.hom b)⟩

end Langlands.GroupScheme.Diagonalizable
