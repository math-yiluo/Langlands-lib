import Langlands.GroupScheme.Torus.OrderedProjectorRepresentation
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli

/-! # Subgroup families of the ordered projector schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J n : Type} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]
variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- The group of character-valued points of the fixed diagonalizable group after pullback. -/
def sourcePoints (T : Over (Spec R)) (Λ : Type u) [AddCommGroup Λ] (U : Over T.left) :
    (U ⟶ ((GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) ≃*
      (Multiplicative Λ →* Γ(U.left, ⊤)ˣ) :=
  (baseChangePointsEquiv T.hom (Diagonalizable.groupScheme R Λ).toGrp U).trans
    (Diagonalizable.characterPointsEquiv R Λ ((Over.map T.hom).obj U))

/-- The matrix group of points of the pulled-back general linear group. -/
def targetPoints (T : Over (Spec R)) (n : Type) [Fintype n] [DecidableEq n] (U : Over T.left) :
    (U ⟶ ((GroupScheme.baseChange T.hom).obj (GeneralLinear.groupScheme n R)).X) ≃*
      Matrix.GeneralLinearGroup n Γ(U.left, ⊤) :=
  (baseChangePointsEquiv T.hom (GeneralLinear.groupScheme n R) U).trans
    (GeneralLinear.pointsEquiv n R ((Over.map T.hom).obj U))

private theorem sourcePoints_naturality (T : Over (Spec R)) {U V : Over T.left} (a : V ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X)
    (m : Λ) :
    sourcePoints T Λ V (a ≫ x) (.ofAdd m) =
      Units.map a.left.appTop.hom.toMonoidHom (sourcePoints T Λ U x (.ofAdd m)) := by
  simp only [sourcePoints, MulEquiv.trans_apply, baseChangePointsEquiv_naturality]
  exact Diagonalizable.characterPointsEquiv_naturality R Λ ((Over.map T.hom).map a) _ m

private theorem targetPoints_naturality (T : Over (Spec R)) {U V : Over T.left} (a : V ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange T.hom).obj (GeneralLinear.groupScheme n R)).X) :
    targetPoints T n V (a ≫ x) = Matrix.GeneralLinearGroup.map a.left.appTop.hom
      (targetPoints T n U x) := by
  simp only [targetPoints, MulEquiv.trans_apply, baseChangePointsEquiv_naturality]
  exact GeneralLinear.pointsEquiv_naturality ((Over.map T.hom).map a) _

/-- Restriction of global projector families composes along scheme morphisms. -/
theorem map_appTop_comp {X Y Z : Scheme.{u}} (P : Family J n Γ(Z, ⊤))
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    (P.map b.appTop.hom).map a.appTop.hom = P.map (a ≫ b).appTop.hom := by
  apply Family.ext
  funext i
  ext j k
  change a.appTop (b.appTop (P.matrix i j k)) = (a ≫ b).appTop (P.matrix i j k)
  rw [Scheme.Hom.comp_appTop]
  rfl

variable (w : J → Λ) (T : Over (Spec R)) (P : Family J n Γ(T.left, ⊤))

private def subgroupPoints (U : Over T.left) :
    (U ⟶ ((GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) →*
      (U ⟶ ((GroupScheme.baseChange T.hom).obj (GeneralLinear.groupScheme n R)).X) :=
  let eval : (Multiplicative Λ →* Γ(U.left, ⊤)ˣ) →* (J → Γ(U.left, ⊤)ˣ) :=
    { toFun := fun χ i => χ (.ofAdd (w i))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  (targetPoints T n U).symm.toMonoidHom.comp
    ((weightedUnit (P.map U.hom.appTop.hom)).comp (eval.comp (sourcePoints T Λ U).toMonoidHom))

private theorem subgroupPoints_naturality {U V : Over T.left} (a : V ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) :
    subgroupPoints w T P V (a ≫ x) = a ≫ subgroupPoints w T P U x := by
  apply (targetPoints T n V).injective
  rw [targetPoints_naturality]
  simp only [subgroupPoints, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply, weightedUnit_map]
  change weightedUnit (P.map V.hom.appTop.hom)
      (fun i => sourcePoints T Λ V (a ≫ x) (.ofAdd (w i))) =
    weightedUnit ((P.map U.hom.appTop.hom).map a.left.appTop.hom)
      (fun i => Units.map a.left.appTop.hom.toMonoidHom (sourcePoints T Λ U x (.ofAdd (w i))))
  simp only [map_appTop_comp, Over.w a, sourcePoints_naturality]

/-- The actual homomorphism over a test base defined by a family of projectors in its
ring of global functions. -/
def subgroupHom : (GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp ⟶
    (GroupScheme.baseChange T.hom).obj (GeneralLinear.groupScheme n R) :=
  homOfPoints (subgroupPoints w T P) (subgroupPoints_naturality w T P)

/-- The matrix of the actual homomorphism on any test scheme. -/
theorem targetPoints_subgroupHom (U : Over T.left)
    (x : U ⟶ ((GroupScheme.baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) :
    targetPoints T n U (x ≫ (subgroupHom w T P).hom.hom) =
      weightedUnit (P.map U.hom.appTop.hom) (fun i => sourcePoints T Λ U x (.ofAdd (w i))) := by
  rw [subgroupHom, comp_homOfPoints]
  exact (targetPoints T n U).apply_symm_apply _

section AffineBase

variable {A : CommRingCat.{u}} (b : Spec A ⟶ Spec R)

/-- On any test scheme over an affine base, the algebraically constructed representation
has the prescribed weight matrix in global sections. -/
theorem representation_points (Q : Family J n A) (U : Over (Spec A))
    (x : U ⟶ (Diagonalizable.groupScheme A Λ).X) :
    GeneralLinear.pointsEquiv n A U (x ≫ (representation w Q).hom.hom) =
      weightedUnit (Q.map (scalarMap U))
        (fun i => Diagonalizable.characterPointsEquiv A Λ U x (.ofAdd (w i))) := by
  unfold GeneralLinear.pointsEquiv Diagonalizable.characterPointsEquiv representation
  erw [Corepresented.groupSchemeMap_points]
  rfl

/-- The subgroup homomorphism over `Spec A` agrees with the group-algebra construction
under the canonical affine base-change comparisons. -/
theorem subgroupHom_spec (Q : Family J n Γ(Spec A, ⊤)) :
    subgroupHom w (Over.mk b) Q =
      (Diagonalizable.baseChangeIso b Λ).hom ≫
        representation w (Q.map (Scheme.ΓSpecIso A).hom.hom) ≫
          (GeneralLinear.baseChangeIso n b).inv := by
  refine hom_ext_points fun U x => (targetPoints (Over.mk b) n U).injective ?_
  rw [targetPoints_subgroupHom]
  let y := x ≫ (Diagonalizable.baseChangeIso b Λ).hom.hom.hom
  let z := y ≫ (representation w (Q.map (Scheme.ΓSpecIso A).hom.hom)).hom.hom
  have hz : targetPoints (Over.mk b) n U (z ≫ (GeneralLinear.baseChangeIso n b).inv.hom.hom) =
      GeneralLinear.pointsEquiv n A U z := by
    change GeneralLinear.pointsEquiv n R ((Over.map b).obj U)
        (baseChangePointsEquiv b (GeneralLinear.groupScheme n R) U
          (z ≫ (GeneralLinear.baseChangeIso n b).inv.hom.hom)) =
      GeneralLinear.pointsEquiv n A U z
    have h := GeneralLinear.pointsEquiv_comp_baseChangeIso_hom b
      (z ≫ (GeneralLinear.baseChangeIso n b).inv.hom.hom)
    simpa only [Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using h.symm
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  change _ = targetPoints (Over.mk b) n U (z ≫ (GeneralLinear.baseChangeIso n b).inv.hom.hom)
  rw [hz, show z = y ≫ _ from rfl, representation_points]
  have hQ : Q.map U.hom.appTop.hom =
      (Q.map (Scheme.ΓSpecIso A).hom.hom).map (scalarMap U) := by
    apply Family.ext
    funext i
    ext j k
    change U.hom.appTop (Q.matrix i j k) =
      ((Scheme.ΓSpecIso A).hom ≫ (Scheme.ΓSpecIso A).inv ≫ U.hom.appTop) (Q.matrix i j k)
    rw [Iso.hom_inv_id_assoc]
    rfl
  rw [hQ]
  congr 1
  funext i
  exact congrArg (fun χ : Multiplicative Λ →* Γ(U.left, ⊤)ˣ => χ (.ofAdd (w i)))
    (Diagonalizable.characterPointsEquiv_baseChangeIso_hom b Λ U x).symm

/-- Generating weights give a closed subgroup over the affine test base. -/
theorem isClosedSubgroup_subgroupHom_spec (Q : Family J n Γ(Spec A, ⊤))
    (hw : AddSubgroup.closure (Set.range w) = ⊤) :
    IsClosedSubgroup (subgroupHom w (Over.mk b) Q) := by
  rw [subgroupHom_spec]
  have h : IsClosedImmersion
      (representation w (Q.map (Scheme.ΓSpecIso A).hom.hom)).hom.hom.left :=
    isClosedSubgroup_representation _ _ hw
  change IsClosedImmersion
    ((Diagonalizable.baseChangeIso b Λ).hom.hom.hom.left ≫
      (representation w (Q.map (Scheme.ΓSpecIso A).hom.hom)).hom.hom.left ≫
      (GeneralLinear.baseChangeIso n b).inv.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

end AffineBase

section Chart

/-- The ordered chart carries the actual subgroup homomorphism defined by its universal family. -/
def chartFamily :
    (GroupScheme.baseChange (scheme J n R).hom).obj (Diagonalizable.groupScheme R Λ).toGrp ⟶
      (GroupScheme.baseChange (scheme J n R).hom).obj (GeneralLinear.groupScheme n R) :=
  subgroupHom w (scheme J n R) (pointsEquiv J n R _ (𝟙 _))

/-- The family on the ordered chart is a closed subgroup when the weights generate. -/
theorem isClosedSubgroup_chartFamily (hw : AddSubgroup.closure (Set.range w) = ⊤) :
    IsClosedSubgroup (chartFamily (n := n) (R := R) w) := by
  exact isClosedSubgroup_subgroupHom_spec w (scheme J n R).hom
    (pointsEquiv J n R _ (𝟙 _)) hw

variable {M : Over (Spec R)} {K : GroupScheme M.left}
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme n R))
    (hu : TorusSubgroupModuli.IsUniversal j)
    (hw : AddSubgroup.closure (Set.range w) = ⊤)
    (hs : IsSplitTorus (Diagonalizable.groupScheme R Λ).toGrp)

include hw hs in
private theorem chartFamily_admissible :
    TorusSubgroupModuli.IsAdmissible (SubgroupFunctor.range (chartFamily (n := n) (R := R) w)) :=
  TorusSubgroupModuli.isAdmissible_range _ (isClosedSubgroup_chartFamily w hw)
    (RelativeTorus.IsTorus.of_isSplitTorus (hs.baseChange (scheme J n R).hom))

/-- The map from an ordered projector chart to a scheme parametrizing closed subtori. -/
def chartMap : scheme J n R ⟶ M :=
  (hu _ _ (chartFamily_admissible w hw hs)).exists.choose

theorem evaluate_chartMap :
    TorusSubgroupModuli.evaluate j (chartMap w j hu hw hs) =
      SubgroupFunctor.range (chartFamily (n := n) (R := R) w) :=
  (hu _ _ (chartFamily_admissible w hw hs)).exists.choose_spec

end Chart

end Langlands.GroupScheme.OrderedProjectorScheme
