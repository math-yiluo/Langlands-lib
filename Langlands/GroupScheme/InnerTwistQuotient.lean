import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected

/-! # Descending a commutative quotient through an inner twist -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H Q : GroupScheme S} {U : Over S}
    (e : LocalGroupIso G H U) (q : G ⟶ Q)

private def localQuotient : LocalGroupHom H Q U where
  toFun a :=
    { toFun := fun h => (e.toFun a).symm h ≫ q.hom.hom
      map_one' := by rw [map_one, MonObj.one_comp]
      map_mul' h h' := by rw [map_mul, MonObj.mul_comp] }
  naturality t a h := by
    change (e.symm.toFun (t ≫ a)) (t ≫ h) ≫ q.hom.hom =
      t ≫ ((e.symm.toFun a) h ≫ q.hom.hom)
    rw [e.symm.naturality, Category.assoc]

variable [IsCommMonObj Q.X] (ζ : Cocycle G U)
    (he : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ζ)

include he in
private theorem localQuotient_independent : (localQuotient e q).IsIndependent := by
  intro Z a b h
  let g := (e.toFun b).symm h
  have hconj : e.toFun a (ζ.toFun a b * g * (ζ.toFun a b)⁻¹) = h := by
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
      g, MulEquiv.apply_symm_apply] using he a b g
  have hpre : (e.toFun a).symm h = ζ.toFun a b * g * (ζ.toFun a b)⁻¹ := by
    rw [← hconj, MulEquiv.symm_apply_apply]
  change (e.toFun a).symm h ≫ q.hom.hom = g ≫ q.hom.hom
  rw [hpre, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, mul_comm (_ ≫ q.hom.hom),
    mul_assoc, mul_inv_cancel, mul_one]

variable [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]

/-- The quotient homomorphism on the twisted group, obtained by fpqc descent
of the original homomorphism composed with each inverse local identification. -/
def descendInnerQuotient : H ⟶ Q :=
  (localQuotient e q).descend (localQuotient_independent e q ζ he)

/-- Each local identification commutes with the original and descended maps. -/
theorem comp_descendInnerQuotient {Z : Over S} (a : Z ⟶ U) (g : Z ⟶ G.X) :
    e.toFun a g ≫ (e.descendInnerQuotient q ζ he).hom.hom = g ≫ q.hom.hom := by
  change e.toFun a g ≫ ((localQuotient e q).descend
    (localQuotient_independent e q ζ he)).hom.hom = _
  rw [LocalGroupHom.comp_descend]
  have h := (localQuotient e q).comp_value (localQuotient_independent e q ζ he)
    (𝟙 Z) a (e.toFun a g)
  simp only [Category.id_comp] at h
  rw [h]
  change (e.toFun a).symm (e.toFun a g) ≫ q.hom.hom = g ≫ q.hom.hom
  rw [MulEquiv.symm_apply_apply]

/-- Over the cover, the recovered isomorphism identifies the two maps to the
same base-changed quotient. -/
theorem baseChange_descendInnerQuotient :
    e.toBaseChangeIso.hom ≫ (baseChange U.hom).map (e.descendInnerQuotient q ζ he) =
      (baseChange U.hom).map q := by
  apply hom_ext_points
  intro Z g
  apply (baseChangePointsEquiv U.hom Q Z).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, baseChangePointsEquiv_comp,
    baseChangePointsEquiv_comp, e.toBaseChangeIso_hom_points, e.comp_descendInnerQuotient]

/-- The descended homomorphism inherits smoothness and surjectivity from the
original over the fpqc cover. -/
theorem smooth_surjective_descendInnerQuotient
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left] :
    Smooth (e.descendInnerQuotient q ζ he).hom.hom.left ∧
      Surjective (e.descendInnerQuotient q ζ he).hom.hom.left := by
  let r := e.descendInnerQuotient q ζ he
  let f := e.toBaseChangeIso
  have hc : (baseChange U.hom).map r = f.inv ≫ (baseChange U.hom).map q := by
    rw [← e.baseChange_descendInnerQuotient q ζ he, Iso.inv_hom_id_assoc]
  have : IsIso f.inv.hom.hom.left :=
    ((Grp.forget (Over U.left)) ⋙ Over.forget U.left).map_isIso f.inv
  have : Smooth ((baseChange U.hom).map q).hom.hom.left :=
    MorphismProperty.of_isPullback (overBaseChange_isPullback U.hom q.hom.hom).flip inferInstance
  have : Surjective ((baseChange U.hom).map q).hom.hom.left :=
    MorphismProperty.of_isPullback (overBaseChange_isPullback U.hom q.hom.hom).flip inferInstance
  refine ⟨smooth_overHom_of_baseChange U.hom r.hom.hom ?_,
    surjective_overHom_of_baseChange U.hom r.hom.hom ?_⟩
  · change Smooth ((baseChange U.hom).map r).hom.hom.left
    rw [hc, Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  · change Surjective ((baseChange U.hom).map r).hom.hom.left
    rw [hc, Grp.comp_hom_hom, Over.comp_left]
    infer_instance

/-- Base changing the two actual kernels along the cover identifies them. -/
def kernelBaseChangeDescendInnerQuotientIso :
    (baseChange U.hom).obj (kernel q) ≅
      (baseChange U.hom).obj (kernel (e.descendInnerQuotient q ζ he)) := by
  let f := e.toBaseChangeIso
  let q' := (baseChange U.hom).map q
  let r := e.descendInnerQuotient q ζ he
  let r' := (baseChange U.hom).map r
  have hb : IsPullback f.hom q' r' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using
      e.baseChange_descendInnerQuotient q ζ he⟩
  have hp := (IsPullback.of_hasPullback q' (kernelUnit _)).paste_horiz hb
  rw [Category.comp_id] at hp
  exact kernelBaseChangeIso U.hom q ≪≫ hp.isoPullback ≪≫ (kernelBaseChangeIso U.hom r).symm

end Langlands.GroupScheme.LocalGroupIso

namespace Langlands.GroupScheme.LocalGroupIso

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Q.X]
    [QuasiCompact (Over.mk (algebraBaseMap k K)).hom]
    [Flat (Over.mk (algebraBaseMap k K)).hom]
    [Surjective (Over.mk (algebraBaseMap k K)).hom]
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k K))) (q : G ⟶ Q)
    (ζ : Cocycle G (Over.mk (algebraBaseMap k K)))
    (he : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ζ)

/-- Simple connectedness of the original kernel transfers to the twisted kernel
by comparison over the extension field and reflection back to the ground field. -/
theorem isSimplyConnected_kernel_descendInnerQuotient (h : IsSimplyConnected (kernel q)) :
    IsSimplyConnected (kernel (e.descendInnerQuotient q ζ he)) :=
  (isSimplyConnected_fieldExtension_iff (K := K) _).mp
    (IsSimplyConnected.of_iso (e.kernelBaseChangeDescendInnerQuotientIso q ζ he).symm
      ((isSimplyConnected_fieldExtension_iff (K := K) _).mpr h))

end Langlands.GroupScheme.LocalGroupIso
