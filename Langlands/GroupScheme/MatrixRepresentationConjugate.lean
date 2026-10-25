import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.HomConjugacy

/-! # Changes of coordinates for actual group-scheme representations -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Change the coordinate basis using one point of GL over the base scheme. -/
def conjugate (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X) :
    MatrixRepresentation G n :=
  ρ ≫ ((GeneralLinear.groupScheme n R).innerIso g).hom

@[simp] theorem conjugate_restrict (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X) (f : H ⟶ G) :
    (ρ.restrict f).conjugate g = (ρ.conjugate g).restrict f :=
  Category.assoc f ρ _

/-- The underlying point action uses the actual inner scheme automorphism. -/
theorem comp_conjugate (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    x ≫ (ρ.conjugate g).hom.hom =
      (GeneralLinear.groupScheme n R).constantPoint g T * (x ≫ ρ.hom.hom) *
        ((GeneralLinear.groupScheme n R).constantPoint g T)⁻¹ := by
  change x ≫ (ρ.hom.hom ≫ _) = _
  rw [← Category.assoc, comp_innerIso_hom]

/-- The change is conjugation by the pullback of the same base point on every test scheme. -/
theorem conjugate_pointMatrix (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.conjugate g).pointMatrix T x =
      GeneralLinear.pointsEquiv n R T ((GeneralLinear.groupScheme n R).constantPoint g T) *
        ρ.pointMatrix T x *
        (GeneralLinear.pointsEquiv n R T
          ((GeneralLinear.groupScheme n R).constantPoint g T))⁻¹ := by
  simp only [pointMatrix_apply, comp_conjugate, map_mul, map_inv]

/-- The affine conjugating matrix is measured over the test algebra itself. -/
theorem conjugate_affineMatrix (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ G.X) :
    (ρ.conjugate g).affineMatrix S x =
      (standard n R).affineMatrix S
        ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S))) *
      ρ.affineMatrix S x *
      ((standard n R).affineMatrix S
        ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S))))⁻¹ := by
  simp only [standard_affineMatrix]
  simp only [affineMatrix_apply, comp_conjugate, map_mul, map_inv]

/-- The affine actions are conjugate by the standard action of the pulled-back base point. -/
theorem conjugate_affineAction (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ G.X) :
    (ρ.conjugate g).affineAction S x =
      (standard n R).affineAction S
        ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S))) *
      ρ.affineAction S x *
      ((standard n R).affineAction S
        ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S))))⁻¹ := by
  simp only [affineAction, MonoidHom.comp_apply, conjugate_affineMatrix, map_mul, map_inv]

/-- The coordinate change intertwines the full affine representations. -/
def conjugateAffineEquiv (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (S : CommAlgCat.{u} R) :
    (ρ.affineRepresentation S).Equiv ((ρ.conjugate g).affineRepresentation S) where
  toLinearEquiv := (standard n R).affineAction S
    ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S)))
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    change _ = (ρ.conjugate g).affineAction S x _
    rw [conjugate_affineAction]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl

@[simp] theorem conjugateAffineEquiv_apply (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    (S : CommAlgCat.{u} R) (v : n → S) :
    ρ.conjugateAffineEquiv g S v =
      (GeneralLinear.affinePointsEquiv n R S
        ((GeneralLinear.groupScheme n R).constantPoint g ((algSpec R).obj (op S))) :
          Matrix n n S) *ᵥ v := by
  change (standard n R).affineAction S _ v = _
  rw [affineAction_apply, standard_affineMatrix]

/-- The coordinate change commutes with algebra maps on vectors. -/
theorem conjugateAffineEquiv_naturality (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X)
    {S T : CommAlgCat.{u} R} (f : S ⟶ T) (v : n → S) :
    ρ.conjugateAffineEquiv g T (fun i => f.hom (v i)) =
      fun i => f.hom (ρ.conjugateAffineEquiv g S v i) := by
  change (standard n R).affineAction T _ _ =
    fun i => f.hom ((standard n R).affineAction S _ v i)
  rw [← constantPoint_naturality (GeneralLinear.groupScheme n R) g ((algSpec R).map f.op)]
  exact affineAction_naturality (standard n R) f _ v

@[simp] theorem conjugate_one (ρ : MatrixRepresentation G n) : ρ.conjugate 1 = ρ := by
  apply hom_ext_points
  intro T x
  simp only [comp_conjugate]
  have h := ((GeneralLinear.groupScheme n R).constantPointHom T).map_one
  simp only [constantPointHom_apply] at h
  rw [h, one_mul, inv_one, mul_one]

/-- Successive coordinate changes compose in the order of their linear actions. -/
theorem conjugate_mul (ρ : MatrixRepresentation G n)
    (g h : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X) :
    (ρ.conjugate g).conjugate h = ρ.conjugate (h * g) := by
  apply hom_ext_points
  intro T x
  simp only [comp_conjugate]
  have hm := ((GeneralLinear.groupScheme n R).constantPointHom T).map_mul h g
  simp only [constantPointHom_apply] at hm
  rw [hm]
  group

@[simp] theorem conjugate_inv (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X) :
    (ρ.conjugate g).conjugate g⁻¹ = ρ := by
  rw [conjugate_mul, inv_mul_cancel, conjugate_one]

/-- Scheme conjugacy yields an equivalence on each full affine coefficient module. -/
theorem nonempty_affineEquiv_of_homConjugate {ρ σ : MatrixRepresentation G n}
    (h : HomConjugate ρ σ) (S : CommAlgCat.{u} R) :
    Nonempty ((ρ.affineRepresentation S).Equiv (σ.affineRepresentation S)) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨ρ.conjugateAffineEquiv g S⟩

end Langlands.GroupScheme.MatrixRepresentation
