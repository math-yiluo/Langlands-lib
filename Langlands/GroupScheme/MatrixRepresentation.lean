import Langlands.GroupScheme.GeneralLinear

/-! # Finite free coefficient representations of actual group schemes -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}}

/-- A coefficient representation with a chosen finite coordinate basis is an actual
homomorphism of group schemes into the explicit general linear group scheme. -/
abbrev MatrixRepresentation (G : GroupScheme (Spec R)) (n : Type)
    [Fintype n] [DecidableEq n] := G ⟶ GeneralLinear.groupScheme n R

namespace MatrixRepresentation

variable {G H J : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- Restriction of a coefficient representation along an actual group-scheme morphism. -/
def restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G) : MatrixRepresentation H n :=
  f ≫ ρ

@[simp] theorem restrict_id (ρ : MatrixRepresentation G n) : ρ.restrict (𝟙 G) = ρ :=
  Category.id_comp ρ

theorem restrict_comp (ρ : MatrixRepresentation G n) (f : H ⟶ G) (g : J ⟶ H) :
    (ρ.restrict f).restrict g = ρ.restrict (g ≫ f) :=
  (Category.assoc g f ρ).symm

/-- Matrix coefficients on points over any test scheme. -/
def pointMatrix (ρ : MatrixRepresentation G n) (T : Over (Spec R)) :
    (T ⟶ G.X) →* GL n Γ(T.left, ⊤) :=
  (GeneralLinear.pointsEquiv n R T).toMonoidHom.comp ((pointsMap ρ).app (op T)).hom

@[simp] theorem pointMatrix_apply (ρ : MatrixRepresentation G n) (T : Over (Spec R))
    (x : T ⟶ G.X) :
    ρ.pointMatrix T x = GeneralLinear.pointsEquiv n R T (x ≫ ρ.hom.hom) := rfl

/-- Scheme pullback acts on every coefficient by pullback of global sections. -/
theorem pointMatrix_naturality (ρ : MatrixRepresentation G n) {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ G.X) :
    ρ.pointMatrix T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (ρ.pointMatrix T x) := by
  simpa only [pointMatrix_apply, Category.assoc] using
    GeneralLinear.pointsEquiv_naturality a (x ≫ ρ.hom.hom)

@[simp] theorem pointMatrix_restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G)
    (T : Over (Spec R)) (x : T ⟶ H.X) :
    (ρ.restrict f).pointMatrix T x = ρ.pointMatrix T (x ≫ f.hom.hom) := by
  simp only [pointMatrix_apply, restrict, Grp.comp_hom_hom, Category.assoc]

/-- Matrices on affine points, with entries in the test algebra itself. -/
def affineMatrix (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ G.X) →* GL n S :=
  (GeneralLinear.affinePointsEquiv n R S).toMonoidHom.comp
    ((pointsMap ρ).app (op ((algSpec R).obj (op S)))).hom

@[simp] theorem affineMatrix_apply (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    ρ.affineMatrix S x = GeneralLinear.affinePointsEquiv n R S (x ≫ ρ.hom.hom) := rfl

/-- Coefficient change is entrywise application of the algebra map. -/
theorem affineMatrix_naturality (ρ : MatrixRepresentation G n) {S T : CommAlgCat.{u} R}
    (f : S ⟶ T) (x : (algSpec R).obj (op S) ⟶ G.X) :
    ρ.affineMatrix T ((algSpec R).map f.op ≫ x) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ.affineMatrix S x) := by
  simpa only [affineMatrix_apply, Category.assoc] using
    GeneralLinear.affinePointsEquiv_naturality f (x ≫ ρ.hom.hom)

@[simp] theorem affineMatrix_restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ H.X) :
    (ρ.restrict f).affineMatrix S x = ρ.affineMatrix S (x ≫ f.hom.hom) := by
  simp only [affineMatrix_apply, restrict, Grp.comp_hom_hom, Category.assoc]

/-- The two point coordinates agree through the canonical affine section isomorphism. -/
theorem pointMatrix_eq_affineMatrix (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    ρ.pointMatrix ((algSpec R).obj (op S)) x =
      Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso S).inv.hom.toRingHom
        (ρ.affineMatrix S x) :=
  GeneralLinear.pointsEquiv_eq_affinePointsEquiv S (x ≫ ρ.hom.hom)

/-- The actual linear action on the finite free coordinate module of an affine test algebra. -/
def affineAction (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ G.X) →* ((n → S) ≃ₗ[S] (n → S)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv S (n → S)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (ρ.affineMatrix S))

@[simp] theorem affineAction_apply (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (v : n → S) :
    ρ.affineAction S x v = (ρ.affineMatrix S x : Matrix n n S) *ᵥ v := rfl

/-- Algebra change intertwines the actions on coordinate vectors. -/
theorem affineAction_naturality (ρ : MatrixRepresentation G n) {S T : CommAlgCat.{u} R}
    (f : S ⟶ T) (x : (algSpec R).obj (op S) ⟶ G.X) (v : n → S) :
    ρ.affineAction T ((algSpec R).map f.op ≫ x) (fun i => f.hom (v i)) =
      fun i => f.hom (ρ.affineAction S x v i) := by
  rw [affineAction_apply, affineMatrix_naturality]
  funext i
  exact (f.hom.toRingHom.map_mulVec _ _ i).symm

@[simp] theorem affineAction_restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ H.X) :
    (ρ.restrict f).affineAction S x = ρ.affineAction S (x ≫ f.hom.hom) := by
  ext v
  simp only [affineAction_apply, affineMatrix_restrict]

/-- The standard coefficient representation of the explicit general linear group scheme. -/
def standard (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) :
    MatrixRepresentation (GeneralLinear.groupScheme n R) n := 𝟙 _

@[simp] theorem standard_affineMatrix (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (GeneralLinear.groupScheme n R).X) :
    (standard n R).affineMatrix S x = GeneralLinear.affinePointsEquiv n R S x := by
  change GeneralLinear.affinePointsEquiv n R S (x ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- On a point classified by an invertible matrix, the standard action is matrix multiplication. -/
theorem standard_affineAction (S : CommAlgCat.{u} R) (g : GL n S) (v : n → S) :
    (standard n R).affineAction S ((GeneralLinear.affinePointsEquiv n R S).symm g) v =
      (g : Matrix n n S) *ᵥ v := by
  rw [affineAction_apply, standard_affineMatrix, MulEquiv.apply_symm_apply]

/-- The trivial coefficient representation is the constant identity group-scheme morphism. -/
def trivial (G : GroupScheme (Spec R)) (n : Type) [Fintype n] [DecidableEq n] :
    MatrixRepresentation G n :=
  Grp.homMk (CartesianMonoidalCategory.toUnit G.X ≫ η[(GeneralLinear.groupScheme n R).X])

@[simp] theorem trivial_pointMatrix (T : Over (Spec R)) (x : T ⟶ G.X) :
    (trivial G n).pointMatrix T x = 1 := by
  change GeneralLinear.pointsEquiv n R T
    (x ≫ (CartesianMonoidalCategory.toUnit G.X ≫ η[_])) = 1
  rw [← CategoryTheory.Hom.one_def, MonObj.comp_one, map_one]

@[simp] theorem trivial_affineMatrix (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    (trivial G n).affineMatrix S x = 1 := by
  change GeneralLinear.affinePointsEquiv n R S
    (x ≫ (CartesianMonoidalCategory.toUnit G.X ≫ η[_])) = 1
  rw [← CategoryTheory.Hom.one_def, MonObj.comp_one, map_one]

@[simp] theorem trivial_affineAction (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    (trivial G n).affineAction S x = 1 := by
  ext v
  simp only [affineAction_apply, trivial_affineMatrix,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rfl

end MatrixRepresentation
end Langlands.GroupScheme
