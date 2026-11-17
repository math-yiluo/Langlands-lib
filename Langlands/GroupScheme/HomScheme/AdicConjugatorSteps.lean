import Langlands.GroupScheme.HomScheme.AdicConjugacy
import Langlands.GroupScheme.HomScheme.AdicInfinitesimalSteps
import Langlands.AlgebraicGeometry.PointTopology.AdicSmoothPointLifting

/-! # Extending actual adic conjugators by one level -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Actual points of an affine smooth scheme lift along any nilpotent algebra surjection. -/
theorem surjective_changeRing_of_nilpotent_surjection
    (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] [Smooth X.hom]
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (φ : B →ₐ[R] C) (hφ : Function.Surjective φ)
    (hnil : IsNilpotent (RingHom.ker φ.toRingHom)) :
    Function.Surjective (fun p : RingPoint R X B ↦ p.changeRing φ) := by
  let := smooth_affineCoordinateRing R X
  intro p₀
  let f := (affineSchemePointEquiv R X C p₀).toAlgHom
  let F := Algebra.FormallySmooth.liftOfSurjective f φ hφ hnil
  refine ⟨(affineSchemePointEquiv R X B).symm (AlgPoint.ofAlgHom F), ?_⟩
  apply (affineSchemePointEquiv R X C).injective
  apply AlgPoint.ext
  intro x
  have h := affineSchemePointEquiv_changeRing R X B C φ
    ((affineSchemePointEquiv R X B).symm (AlgPoint.ofAlgHom F))
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun q : AffineCoordinateRing R X →ₐ[R] C ↦ q x)
    (h.trans (Algebra.FormallySmooth.comp_liftOfSurjective f φ hφ hnil))

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.HomScheme

/-- A base point on a pullback group whose restriction is the unit projects to a
test-valued point whose restriction is the unit. -/
theorem restrict_projected_point_eq_one {S : Scheme.{u}} (G : GroupScheme S)
    {T T' : Over S} (a : T' ⟶ T)
    (k : Over.mk (𝟙 T.left) ⟶ ((baseChange T.hom).obj G).X)
    (hk : ((baseChange T.hom).obj G).constantPoint k (Over.mk a.left) = 1) :
    a ≫ baseChangeBasePointsEquiv T.hom G k = 1 := by
  let e : T' ≅ (Over.map T.hom).obj (Over.mk a.left) :=
    Over.isoMk (Iso.refl _) (by simp)
  have hproj : e.hom ≫ baseChangePointsEquiv T.hom G (Over.mk a.left)
      (((baseChange T.hom).obj G).constantPoint k (Over.mk a.left)) =
      a ≫ baseChangeBasePointsEquiv T.hom G k := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, baseChangePointsEquiv_left, Over.comp_left,
      baseChangeBasePointsEquiv_left]
    change (𝟙 T'.left) ≫ ((a.left ≫ k.left) ≫ pullback.fst G.X.hom T.hom) =
      a.left ≫ (k.left ≫ pullback.fst G.X.hom T.hom)
    simp only [Category.id_comp, Category.assoc]
  rw [← hproj, hk, map_one, MonObj.comp_one]

namespace Adic

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- A successive adic transition as an algebra homomorphism over `A`. -/
def transitionAlgHom (n : ℕ) :
    A ⧸ I ^ (n + 1 + 1) →ₐ[A] A ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (n + 1).le_succ)

/-- Any point of a smooth affine group on an adic thickening lifts one level. -/
theorem point_step_surjective
    (G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (n : ℕ) :
    Function.Surjective (fun g : Over.mk (quotientMap I (n + 1)) ⟶ G.X ↦
      transitionOver I n ≫ g) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro g
  obtain ⟨g', hg'⟩ :=
    Langlands.AlgebraicGeometry.PointTopology.surjective_changeRing_of_nilpotent_surjection
      A G.X (transitionAlgHom I n) (transitionRingHom_surjective I n)
      ⟨2, transitionRingHom_ker_sq I n⟩ g
  exact ⟨g', hg'⟩

/-- An infinitesimal correction extends any conjugator on one adic quotient to the next,
while preserving its prescribed reduction. -/
theorem conjugator_step_of_infinitesimal
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (f f' : H ⟶ G) (n : ℕ) (g : Over.mk (quotientMap I n) ⟶ G.X)
    (hconj : (baseChange (quotientMap I n)).map f' = conjugationFamily f g) :
    ∃ g' : Over.mk (quotientMap I (n + 1)) ⟶ G.X,
      transitionOver I n ≫ g' = g ∧
        (baseChange (quotientMap I (n + 1))).map f' = conjugationFamily f g' := by
  let T := Over.mk (quotientMap I (n + 1))
  let a := transitionOver I n
  let H' := (baseChange T.hom).obj H
  let G' := (baseChange T.hom).obj G
  have : Smooth G'.X.hom := by
    change Smooth (pullback.snd G.X.hom (quotientMap I (n + 1)))
    infer_instance
  obtain ⟨q, hq⟩ := point_step_surjective I G n g
  change a ≫ q = g at hq
  let j : H' ⟶ G' := conjugationFamily f q
  let j' : H' ⟶ G' := (baseChange T.hom).map f'
  have heval : evaluate a j = evaluate a j' := by
    calc
      _ = conjugationFamily f (a ≫ q) := evaluate_conjugationFamily f q a
      _ = conjugationFamily f g := congrArg (conjugationFamily f) hq
      _ = (baseChange (quotientMap I n)).map f' := hconj.symm
      _ = _ := (evaluate_baseChange a f').symm
  have hraw : (baseChange a.left).map j = (baseChange a.left).map j' :=
    (evaluate_eq_iff_baseChange_eq a j j').mp heval
  obtain ⟨-, hc⟩ := infinitesimal_lifting_of_surjection hInf
    (transitionRingHom I n) (transitionRingHom_surjective I n)
    ⟨2, transitionRingHom_ker_sq I n⟩ H' G' (hH.baseChange T.hom)
  obtain ⟨k, hk, hj⟩ := hc j j' hraw
  let kT : Over.mk (𝟙 T.left) ⟶ ((baseChange T.hom).obj G).X := k
  let k₀ : T ⟶ G.X := baseChangeBasePointsEquiv T.hom G kT
  have hk₀ : a ≫ k₀ = 1 :=
    restrict_projected_point_eq_one G a k hk
  have hkp : RelativeLevi.pulledBackPoint G T k₀ = kT := by
    apply (baseChangeBasePointsEquiv T.hom G).injective
    rw [RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint]
  have hprod : RelativeLevi.pulledBackPoint G T (k₀ * q) =
      kT * RelativeLevi.pulledBackPoint G T q := by
    change RelativeLevi.pulledBackPointHom G T (k₀ * q) = _
    rw [map_mul]
    change RelativeLevi.pulledBackPoint G T k₀ * _ = _
    rw [hkp]
    rfl
  refine ⟨k₀ * q, ?_, ?_⟩
  · change a ≫ (k₀ * q) = g
    rw [MonObj.comp_mul, hk₀, hq, one_mul]
  · change j' = (baseChange T.hom).map f ≫
      (G'.innerIso (RelativeLevi.pulledBackPoint G T (k₀ * q))).hom
    rw [hprod, innerIso_mul_hom, ← Category.assoc]
    exact hj

/-- The infinitesimal proposition and adic Hom injectivity give global conjugacy by a
point reducing to the identity. -/
theorem conjugacy_of_infinitesimal_and_injective [IsAdicComplete I A]
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hinj : Function.Injective (System.restrict I H G))
    (f f' : H ⟶ G)
    (h₀ : (baseChange (quotientMap I 0)).map f =
      (baseChange (quotientMap I 0)).map f') :
    ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
      G.constantPoint q (Over.mk (quotientMap I 0)) = 1 ∧
        f' = f ≫ (G.innerIso q).hom :=
  exists_conjugator_of_step_lifting I hinj f f' h₀
    (conjugator_step_of_infinitesimal I hInf H G hH f f')

end Adic

end Langlands.GroupScheme.HomScheme
