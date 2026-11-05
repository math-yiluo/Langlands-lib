import Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreadingStatement
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Absolute.BorelStatement

/-! # An integral parabolic model from a descended cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic.Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The explicit dynamic parabolic is smooth over a Noetherian base when the ambient group is. -/
theorem smooth_parabolicScheme [IsNoetherianRing R] [Smooth G.X.hom] :
    Smooth (parabolicScheme χ).X.hom := by
  have : Algebra.Smooth R (AffineCoordinates.algebra G) :=
    (DynamicSmooth.smooth_algSpec_iff (AffineCoordinates.algebra G)).1
      (smooth_of_over_iso ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))
        (inferInstance : Smooth G.X.hom))
  exact DynamicSmooth.smooth_parabolicScheme (cocharacter χ)

/-- Every base change of the explicit inclusion represents the changed dynamic subgroup. -/
theorem isRepresentedBy_parabolicHom_baseChange {S' : Scheme.{u}} (b : S' ⟶ Spec R) :
    (Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)).IsRepresentedBy
      ((baseChange b).map (parabolicHom χ)) := by
  rw [Dynamic.parabolic_baseChange]
  exact (isRepresentedBy_parabolicHom χ).baseChange b

end Dynamic.Affine

namespace IntegralModel.DynamicParabolic

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

variable (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
  (p : P ⟶ G) (hp : IsClosedSubgroup p)
  (hχ : SubgroupFunctor.range (p ≫ M.genericIso.inv) =
    Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ))

include hp hχ in
/-- The supplied subgroup and the generic dynamic subgroup represent the same functor. -/
theorem isRepresentedBy_generic :
    (Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ)).IsRepresentedBy
      (p ≫ M.genericIso.inv) := by
  have : IsClosedImmersion (p ≫ M.genericIso.inv).hom.hom.left :=
    hp.comp_iso M.genericIso.symm
  exact ⟨Over.mono_of_mono_left _, hχ⟩

/-- The actual generic-fibre identification, determined by the supplied inclusion. -/
def genericIso :
    (baseChange (Spec.algebraMap R K)).obj (Dynamic.Affine.parabolicScheme χ) ≅ P :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange χ (Spec.algebraMap R K)).isoOfIsRepresentedBy
    (isRepresentedBy_generic M χ p hp hχ)

/-- The generic identification preserves the original subgroup homomorphism. -/
theorem genericIso_hom_comp :
    (genericIso M χ p hp hχ).hom ≫ p =
      (baseChange (Spec.algebraMap R K)).map (Dynamic.Affine.parabolicHom χ) ≫
        M.genericIso.hom := by
  have h := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange χ (Spec.algebraMap R K))
    (isRepresentedBy_generic M χ p hp hχ)
  have h' := congrArg (fun f => f ≫ M.genericIso.hom) h
  simpa only [genericIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

variable [IsNoetherianRing R] [Smooth M.group.X.hom]

/-- A smooth affine integral model of the supplied subgroup, from the given cocharacter. -/
def model : IntegralModel R K P where
  group := Dynamic.Affine.parabolicScheme χ
  affine := by
    have : IsClosedImmersion (Dynamic.Affine.parabolicHom χ).hom.hom.left :=
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ
    rw [← (Dynamic.Affine.parabolicHom χ).hom.hom.w]
    infer_instance
  flat := by
    have := Dynamic.Affine.smooth_parabolicScheme χ
    infer_instance
  finiteType := by
    have := Dynamic.Affine.smooth_parabolicScheme χ
    infer_instance
  genericIso := genericIso M χ p hp hχ

/-- The actual dynamic inclusion extends the originally supplied generic arrow. -/
def inclusion : (model M χ p hp hχ).Hom M p where
  hom := Dynamic.Affine.parabolicHom χ
  generic_comm := (genericIso_hom_comp M χ p hp hχ).symm

theorem closedImmersion_inclusion :
    IsClosedImmersion (inclusion M χ p hp hχ).hom.hom.hom.left :=
  Dynamic.Affine.isClosedSubgroup_parabolicHom χ

theorem smooth_model : Smooth (model M χ p hp hχ).group.X.hom :=
  Dynamic.Affine.smooth_parabolicScheme χ

/-- Connectedness of each field fibre follows from ambient connected reductivity. -/
theorem fieldConnected (k : Type u) [Field k] [Algebra R k]
    (hG : IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj M.group)) :
    ConnectedSpace (((baseChange (Spec.algebraMap R k)).obj
      (model M χ p hp hχ).group).X.left) := by
  let := hG.smooth
  let := hG.isAffineHom
  let := hG.connectedSpace
  exact DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic _
    (Dynamic.baseChangeCocharacter (Spec.algebraMap R k) χ)
    (Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange χ (Spec.algebraMap R k))

/-- Geometric parabolicity uses the explicit dynamic-to-parabolic classification premise. -/
theorem fieldParabolic (hPD : ParabolicDynamicStatement.{u})
    (k : Type u) [Field k] [Algebra R k]
    (hG : IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj M.group)) :
    IsParabolicSubgroup ((baseChange (Spec.algebraMap R k)).map
      (inclusion M χ p hp hχ).hom) :=
  (hPD k _ hG _ _
    ((Dynamic.Affine.isClosedSubgroup_parabolicHom χ).baseChange (Spec.algebraMap R k))).2
      ⟨Dynamic.baseChangeCocharacter (Spec.algebraMap R k) χ,
        (Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange χ (Spec.algebraMap R k)).2⟩

/-- Assemble the exact simultaneous model data with all remaining prerequisites visible. -/
def modelData (hPD : ParabolicDynamicStatement.{u}) (hM : IsReductive M.group)
    (hfields : ∀ (k : Type u) [Field k] [Algebra R k],
      IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj M.group)) :
    ReductiveParabolicSpreading.ModelData R K p where
  ambient := M
  parabolic := model M χ p hp hχ
  inclusion := inclusion M χ p hp hχ
  closedImmersion := closedImmersion_inclusion M χ p hp hχ
  reductive := hM
  parabolicSmooth := smooth_model M χ p hp hχ
  fieldReductive := hfields
  fieldParabolic k := fieldParabolic M χ p hp hχ hPD k (hfields k)
  fieldConnected k := fieldConnected M χ p hp hχ k (hfields k)

end IntegralModel.DynamicParabolic
end Langlands.GroupScheme
