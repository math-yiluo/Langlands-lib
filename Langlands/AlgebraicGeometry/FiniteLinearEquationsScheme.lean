import Langlands.AlgebraicGeometry.FiniteLinearEquations
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Yoneda

/-! # Scheme representation of finite homogeneous linear equations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.FiniteLinearEquations

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {m n : ℕ} (a : Fin m → Fin n → R)

/-- The spectrum of the equation algebra, with its actual map to the coefficient spectrum. -/
abbrev equationsScheme : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.algebraMap R (CoordinateRing a))

instance equationsScheme_affine : IsAffineHom (equationsScheme a).hom := by
  dsimp [equationsScheme]
  infer_instance

instance equationsScheme_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (equationsScheme a).hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R _)))
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap R (CoordinateRing a)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

variable {a}

/-- The scalar map on global sections induced by the actual structure morphism. -/
def sectionScalars (T : Over (Spec (CommRingCat.of R))) : R →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom

/-- Global sections as an algebra of the coefficient ring. -/
@[instance_reducible]
def sectionsAlgebra (T : Over (Spec (CommRingCat.of R))) : Algebra R Γ(T.left, ⊤) :=
  (sectionScalars T).toAlgebra

attribute [local instance] sectionsAlgebra

/-- Pullback of global sections is compatible with the coefficient scalars. -/
def pullSections {T U : Over (Spec (CommRingCat.of R))} (q : T ⟶ U) :
    Γ(U.left, ⊤) →ₐ[R] Γ(T.left, ⊤) where
  __ := q.left.appTop.hom
  commutes' r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ U.hom.appTop ≫ q.left.appTop) r =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop) r
    rw [← Scheme.Hom.comp_appTop, Over.w]

variable (a)

/-- A scheme point gives its coordinate-algebra map on global sections. -/
def schemePointToAlgebra {T : Over (Spec (CommRingCat.of R))}
    (q : T ⟶ equationsScheme a) : CoordinateRing a →ₐ[R] Γ(T.left, ⊤) where
  __ := ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫ q.left.appTop).hom
  commutes' r := by
    change ((CommRingCat.ofHom (algebraMap R (CoordinateRing a)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv) ≫ q.left.appTop) r =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop) r
    rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop]
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (q.left ≫ (equationsScheme a).hom).appTop) r = _
    rw [Over.w]

/-- An algebra map on global sections gives an actual scheme point over the base. -/
def algebraToSchemePoint {T : Over (Spec (CommRingCat.of R))}
    (f : CoordinateRing a →ₐ[R] Γ(T.left, ⊤)) : T ⟶ equationsScheme a :=
  Over.homMk (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    apply ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      ((T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) ≫
        Spec.algebraMap R (CoordinateRing a)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
      Iso.inv_hom_id, Category.comp_id]
    ext r
    exact f.commutes r)

/-- The affine adjunction over the coefficient spectrum, valid on every scheme test. -/
def schemeAlgebraPointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ equationsScheme a) ≃ (CoordinateRing a →ₐ[R] Γ(T.left, ⊤)) where
  toFun := schemePointToAlgebra a
  invFun := algebraToSchemePoint a
  left_inv q := by
    apply Over.OverMorphism.ext
    apply ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫
      (T.left.toSpecΓ ≫ Spec.map
        (CommRingCat.ofHom (schemePointToAlgebra a q).toRingHom)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫ q.left.appTop
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  right_inv f := by
    ext r
    change ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫
      (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)).appTop) r = f r
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

/-- The global-section algebra map commutes with every restriction of scheme points. -/
lemma schemePointToAlgebra_comp {T U : Over (Spec (CommRingCat.of R))}
    (q : T ⟶ U) (g : U ⟶ equationsScheme a) :
    schemePointToAlgebra a (q ≫ g) = (pullSections q).comp (schemePointToAlgebra a g) := by
  ext r
  change ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫
    (q.left ≫ g.left).appTop) r =
    q.left.appTop (((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv ≫
      g.left.appTop) r)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- All scheme points of the equation spectrum are exactly global-section solutions. -/
def schemePointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ equationsScheme a) ≃ Solutions a Γ(T.left, ⊤) :=
  (schemeAlgebraPointsEquiv a T).trans (pointsEquiv a)

/-- The comparison evaluates the actual quotient coordinates. -/
@[simp]
lemma schemePointsEquiv_apply {T : Over (Spec (CommRingCat.of R))}
    (q : T ⟶ equationsScheme a) (i : Fin n) :
    (schemePointsEquiv a T q).val i = q.left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv
        (Ideal.Quotient.mk (equationsIdeal a) (MvPolynomial.X i))) := rfl

/-- The point-solution comparison respects every scheme morphism over the base. -/
lemma schemePointsEquiv_naturality {T U : Over (Spec (CommRingCat.of R))}
    (q : T ⟶ U) (g : U ⟶ equationsScheme a) :
    schemePointsEquiv a T (q ≫ g) =
      mapSolutions a (pullSections q) (schemePointsEquiv a U g) := by
  change pointsEquiv a (schemePointToAlgebra a (q ≫ g)) = _
  rw [schemePointToAlgebra_comp]
  rfl

/-- Global-section solutions on the full scheme slice, with the explicit value lift. -/
def solutionsPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift.{u + 1} (Solutions a Γ(T.unop.left, ⊤))
  map q := ↾fun x ↦ ULift.up (mapSolutions a (pullSections q.unop) x.down)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    funext i
    change (𝟙 T.unop.left : T.unop.left ⟶ T.unop.left).appTop (x.down.val i) = x.down.val i
    simp
  map_comp q r := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    funext i
    change (r.unop.left ≫ q.unop.left).appTop (x.down.val i) =
      r.unop.left.appTop (q.unop.left.appTop (x.down.val i))
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- The actual affine scheme represents all finite linear solutions on the entire slice. -/
def solutionsPresheafIso :
    (uliftYoneda.{u + 1}).obj (equationsScheme a) ≅ solutionsPresheaf a :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ulift.trans ((schemePointsEquiv a T.unop).trans Equiv.ulift.symm)).toIso)
    (by
      intro T U q
      ext x
      apply ULift.ext
      exact schemePointsEquiv_naturality a q.unop x.down)

/-- The natural isomorphism keeps the same explicit coordinates as the point comparison. -/
@[simp]
lemma solutionsPresheafIso_hom_apply {T : Over (Spec (CommRingCat.of R))}
    (q : T ⟶ equationsScheme a) (i : Fin n) :
    (((solutionsPresheafIso a).hom.app (op T)) (ULift.up q)).down.val i =
      q.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing a))).inv
        (Ideal.Quotient.mk (equationsIdeal a) (MvPolynomial.X i))) := rfl

end Langlands.AlgebraicGeometry.FiniteLinearEquations
