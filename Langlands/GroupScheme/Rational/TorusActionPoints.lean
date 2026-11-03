import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.VectorGroupQuotient

/-! # The torus action on points over arbitrary test schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {I : Type u} [Finite I]

/-- Pulling back global functions along the unit of the affinization adjunction inverts the
identification of the global functions of a spectrum. -/
theorem unit_appTop_ΓSpecIso_inv (T : Over (Spec R)) (a : ((algΓ R).obj T).unop) :
    ((algΓAlgSpecAdjunction R).unit.app T).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ((algΓ R).obj T).unop)).inv a) = a := by
  have h := adjunction_homEquiv_symm_apply (B := ((algΓ R).obj T).unop)
    ((algΓAlgSpecAdjunction R).unit.app T) a
  rw [Adjunction.homEquiv_counit] at h
  have h2 : (algΓ R).map ((algΓAlgSpecAdjunction R).unit.app T) ≫
      (algΓAlgSpecAdjunction R).counit.app (op (unop ((algΓ R).obj T))) = 𝟙 _ :=
    (algΓAlgSpecAdjunction R).left_triangle_components T
  rw [h2] at h
  exact h.symm

/-- The unit coordinates of the affinization factor of a split-torus point are its unit
coordinates. -/
theorem algebraPointsEquiv_affinizationFactor [IsAffineHom (splitTorus (Spec R) I).X.hom]
    (T : Over (Spec R)) (s : T ⟶ (splitTorus (Spec R) I).X) :
    splitTorus.algebraPointsEquiv I ((algΓ R).obj T).unop
        (Lie.affinizationFactor (splitTorus (Spec R) I) s) =
      splitTorus.pointsEquiv I T s := by
  funext i
  apply Units.ext
  conv_rhs => rw [← Lie.unit_affinizationFactor (splitTorus (Spec R) I) s,
    splitTorus.pointsEquiv_naturality]
  have key : ∀ v : Γ(Spec (CommRingCat.of ((algΓ R).obj T).unop), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of ((algΓ R).obj T).unop)).hom v =
        ((algΓAlgSpecAdjunction R).unit.app T).left.appTop v := by
    intro v
    have h := unit_appTop_ΓSpecIso_inv T
      ((Scheme.ΓSpecIso (CommRingCat.of ((algΓ R).obj T).unop)).hom v)
    rw [Iso.hom_inv_id_apply] at h
    exact h.symm
  exact key _

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- On every test scheme, the automorphic action of the split torus is the coordinate action of
the unit coordinates of the torus point. -/
theorem pointsEquiv_act (b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e))
    (T : Over (Spec R)) (s : T ⟶ (splitTorus (Spec R) I).X) (x : T ⟶ (groupScheme F e).X) :
    pointsEquiv F e T (b.act s x) =
      (TorusAction.ofAutomorphicAction e b).act (splitTorus.pointsEquiv I T s)
        (pointsEquiv F e T x) := by
  have : IsAffineHom (splitTorus (Spec R) I).X.hom := isAffineHom_splitTorus_spec R I
  rw [← algebraPointsEquiv_affinizationFactor T s]
  conv_lhs => rw [← Lie.unit_affinizationFactor (splitTorus (Spec R) I) s,
    ← unit_comp_affineFactor e x, ← AutomorphicAction.naturality, pointsEquiv_unit_comp,
    affinePointsEquiv_act]
  conv_rhs => rw [← unit_comp_affineFactor e x, pointsEquiv_unit_comp]
  rfl

end Langlands.GroupScheme.Corepresented
