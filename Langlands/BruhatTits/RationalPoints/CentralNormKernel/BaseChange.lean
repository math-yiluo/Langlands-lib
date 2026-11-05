import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Derived.CentralIntersection.BlockCharacter

/-! # Base change of central rational points and matrices to an algebraic closure

For a group scheme `M` over a field `F` with algebraic closure `K`, a rational point `z` of `M`
gives a rational point `z_K` of the base change `M_K`, central when `z` is; a matrix
representation `ρ` of `M` gives the representation `ρ_K` of `M_K` (base change followed by
`(GL_{n,F})_K ≅ GL_{n,K}`), a closed embedding when `ρ` is one, with
`ρ_K (z_K) = ρ (z)` entrywise in `K`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.CentralIntersection

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {F : Type u} [Field F] {M : GroupScheme (Spec (CommRingCat.of F))}
  {N : Type} [Fintype N] [DecidableEq N]

variable (F) in
/-- The base change morphism to the algebraic closure. -/
abbrev closureBase : Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ Spec (CommRingCat.of F) :=
  toAlgebraicClosure F

/-- The base change of `M` to the algebraic closure. -/
abbrev closureGroup (M : GroupScheme (Spec (CommRingCat.of F))) :
    GroupScheme (Spec (CommRingCat.of (AlgebraicClosure F))) :=
  (GroupScheme.baseChange (closureBase F)).obj M

/-- The base change of a matrix representation to the algebraic closure. -/
def closureRep (ρ : MatrixRepresentation M N) : MatrixRepresentation (closureGroup M) N :=
  (GroupScheme.baseChange (closureBase F)).map ρ ≫ (GeneralLinear.baseChangeIso N (closureBase F)).hom

theorem isClosedImmersion_closureRep (ρ : MatrixRepresentation M N)
    [IsClosedImmersion ρ.hom.hom.left] : IsClosedImmersion (closureRep ρ).hom.hom.left := by
  have h : IsClosedSubgroup ((GroupScheme.baseChange (closureBase F)).map ρ) :=
    IsClosedSubgroup.baseChange (closureBase F) (show IsClosedSubgroup ρ from ‹_›)
  have : IsClosedImmersion ((GroupScheme.baseChange (closureBase F)).map ρ).hom.hom.left := h
  have : IsIso (GeneralLinear.baseChangeIso N (closureBase F)).hom.hom.hom.left :=
    isIso_left_of_iso _
  change IsClosedImmersion (_ ≫ _)
  infer_instance

/-- The base change of a rational point to the algebraic closure. -/
def closurePoint (z : rationalPoints M) : rationalPoints (closureGroup M) :=
  (baseChangePointsEquiv (closureBase F) M (Over.mk (𝟙 _))).symm (toBase _ ≫ z)

theorem closurePoint_mem_center {z : rationalPoints M}
    (hz : z ∈ (center M).carrier (Over.mk (𝟙 _))) :
    closurePoint z ∈ (center (closureGroup M)).carrier (Over.mk (𝟙 _)) := by
  rw [center_baseChange, SubgroupFunctor.mem_baseChange, closurePoint, MulEquiv.apply_symm_apply]
  exact (center M).comp_mem _ hz

theorem appTop_closureBase (y : Γ(Spec (CommRingCat.of F), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom ((closureBase F).appTop y) =
      algebraMap F (AlgebraicClosure F) ((Scheme.ΓSpecIso (CommRingCat.of F)).hom y) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))
  exact congrArg (fun φ => φ.hom y) h

/-- The matrix of the base-changed point is the original matrix, entrywise in the closure. -/
theorem closureRep_rationalMatrix (ρ : MatrixRepresentation M N) (z : rationalPoints M) :
    (closureRep ρ).rationalMatrix (closurePoint z) =
      Matrix.GeneralLinearGroup.map (algebraMap F (AlgebraicClosure F)) (ρ.rationalMatrix z) := by
  set T' := (Over.map (closureBase F)).obj (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure F)))))
  have h1 : GeneralLinear.pointsEquiv N (CommRingCat.of (AlgebraicClosure F)) (Over.mk (𝟙 _))
      (closurePoint z ≫ (closureRep ρ).hom.hom) =
        GeneralLinear.pointsEquiv N (CommRingCat.of F) T' (toBase T' ≫ z ≫ ρ.hom.hom) := by
    rw [closureRep, Grp.comp_hom_hom, ← Category.assoc,
      GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp, closurePoint,
      MulEquiv.apply_symm_apply, Category.assoc]
  apply Units.ext
  ext i j
  rw [MatrixRepresentation.rationalMatrix_apply, Matrix.GeneralLinearGroup.map_apply, h1,
    GeneralLinear.pointsEquiv_naturality, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, MatrixRepresentation.rationalMatrix_apply,
    Matrix.GeneralLinearGroup.map_apply]
  have hb : (toBase T').left = closureBase F := by
    change 𝟙 _ ≫ closureBase F = closureBase F
    rw [Category.id_comp]
  rw [hb]
  exact appTop_closureBase _

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
