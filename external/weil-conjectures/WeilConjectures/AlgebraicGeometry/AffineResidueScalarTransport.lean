/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar transport from the affine prime residue field

Source: Stacks Project, Tag 0098; naturality of scheme residue maps.
(blueprint: lem-sc-affine-residue-scalar-transport)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme

/-- The field transport in the affine chart equals extension by section evaluation.
Source: Stacks Project, Tag 0098 (sheaves-lemma-stalk-pullback), and the residue
map construction in Mathlib.AlgebraicGeometry.ResidueField.
(blueprint: lem-sc-affine-residue-scalar-transport)

Proof: Put A = Gamma(W,U), p = hU.isoSpec.hom z and k = kappa_W(z).
Naturality of evaluation under U.ι and hU.isoSpec.hom, together with
Spec.algebraMap_residueFieldIso_inv, gives e.hom composed with evaluation equal
to A -> kappa(p). Here e is invertible since both scheme maps are open immersions.
On a module M send b tensor m, after restricting scalars along e.hom, to
e.inv(b) tensor m in k tensor_A M. Its inverse sends a tensor m to e.hom(a)
tensor m. The preceding ring equality makes both maps balanced and k-linear.
The inverse equations hold on pure tensors, which generate the tensor products.
Both maps commute with module homomorphisms, giving the natural isomorphism.
No freeness, boundedness, derived category or flatness of A -> k is required. -/
theorem affine_residue_scalar_transport (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) (z : U) :
    let e := asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
        Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom z)
    Nonempty (ModuleCat.extendScalars.{v, v, v}
      (algebraMap Γ(W, U) (hU.isoSpec.hom z).asIdeal.ResidueField) ⋙
        ModuleCat.restrictScalars.{v, v, v} e.hom.hom ≅
      ModuleCat.extendScalars.{v, v, v} (W.evaluation U z z.property).hom) := by
  let e := asIso (U.ι.residueFieldMap z) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
      Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom z)
  have h : W.evaluation U z z.property ≫ e.hom =
      CommRingCat.ofHom
        (algebraMap Γ(W, U) (hU.isoSpec.hom z).asIdeal.ResidueField) := by
    apply (cancel_mono (Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom z)).inv).mp
    simp only [e, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    erw [← cancel_mono (hU.isoSpec.hom.residueFieldMap z)]
    simp only [Category.assoc, Iso.symm_hom, asIso_inv, asIso_hom,
      IsIso.inv_hom_id, Category.comp_id]
    erw [Spec.algebraMap_residueFieldIso_inv_assoc]
    change W.evaluation U z z.property ≫ U.ι.residueFieldMap z =
      (ΓSpecIso Γ(W, U)).inv ≫ (Spec Γ(W, U)).Γevaluation (hU.isoSpec.hom z) ≫
        hU.isoSpec.hom.residueFieldMap z
    erw [Γevaluation_naturality, hU.isoSpec_hom_appTop]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    change W.presheaf.germ U z z.property ≫ W.residue z ≫
      U.ι.residueFieldMap z = U.topIso.inv ≫
        U.toScheme.presheaf.germ ⊤ z trivial ≫ U.toScheme.residue z
    erw [residue_residueFieldMap, ← U.stalkIso_inv]
    simp only [← Category.assoc]
    congr 1
    erw [Iso.comp_inv_eq, Category.assoc, U.germ_stalkIso_hom]
    simp only [Scheme.Opens.topIso, Functor.mapIso_inv, Iso.op_inv]
    symm
    exact W.presheaf.germ_res _ z _
  let er := e.commRingCatIsoToRingEquiv
  let J := ModuleCat.restrictScalarsEquivalenceOfRingEquiv er
  let adj := (ModuleCat.extendRestrictScalarsAdj
    (algebraMap Γ(W, U) (hU.isoSpec.hom z).asIdeal.ResidueField)).comp
      J.toAdjunction
  let ψ := (W.evaluation U z z.property).hom
  have hh : er.symm.toRingHom.comp
      (algebraMap Γ(W, U) (hU.isoSpec.hom z).asIdeal.ResidueField) = ψ := by
    ext a
    have ha := ConcreteCategory.congr_hom h a
    change er.symm ((algebraMap Γ(W, U) _ ) a) = ψ a
    apply er.injective
    change er (ψ a) = (algebraMap Γ(W, U) _) a at ha
    simpa only [RingEquiv.apply_symm_apply] using ha.symm
  let η : J.inverse ⋙ ModuleCat.restrictScalars
      (algebraMap Γ(W, U) (hU.isoSpec.hom z).asIdeal.ResidueField) ≅
      ModuleCat.restrictScalars ψ :=
    (ModuleCat.restrictScalarsComp' _ _ ψ hh.symm).symm
  exact ⟨(conjugateIsoEquiv (ModuleCat.extendRestrictScalarsAdj ψ) adj).symm η.symm⟩

end AlgebraicGeometry.Scheme
