import Langlands.GroupScheme.Rational.NumberFieldWeilCocycleTransfer
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionProof

/-! # The number-field Hasse kernel reduces to absolutely almost-simple groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- The finite-Galois Hasse kernel for absolutely almost-simple simply connected groups. -/
def NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))), ξ.LocallyTrivial → ξ.IsTrivial

set_option backward.isDefEq.respectTransparency false in
/-- The almost-simple kernel follows from the absolutely almost-simple kernel. -/
theorem numberFieldAlmostSimpleSimplyConnectedGaloisHasseKernel_of_absolute
    (h : NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hsc hsimple L _ _ _ _ ξ hξ
  let : IsAffineHom G.X.hom := hsc.isSemisimple.isConnectedReductive.isAffineHom
  obtain ⟨B, _, _, _, _, H, _, _, hscH, habsH, ⟨e⟩⟩ :=
    simplyConnectedAlmostSimpleWeilRestriction F G hsc hsimple
  let : NumberField B := NumberField.of_module_finite F B
  let ζ : Cocycle (AffineWeil.groupScheme F B H) (ringTest F L) := ξ.map e.hom
  have hζ : ζ.LocallyTrivial := hξ.map e.hom
  obtain ⟨E, _, _, _, _, r, hlocal, hreflect⟩ := AffineWeil.exists_finiteGalois_transfer F B H ζ hζ
  have hζtriv : ζ.IsTrivial := hreflect (h B H hscH habsH E
    ((AffineWeil.transferCocycle F B H ζ).refine r) hlocal)
  obtain ⟨f, hf⟩ := hζtriv.map e.inv
  refine ⟨f, fun a c => ?_⟩
  have key := hf a c
  change (ξ.toFun a c ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = _ at key
  rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at key
  exact key

/-- The simply connected kernel over number fields follows from the absolutely almost-simple
case, by the product and Weil restriction reductions. -/
theorem numberFieldSimplyConnectedGaloisHasseKernel_of_absolute
    (h : NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u} :=
  numberFieldSimplyConnectedGaloisHasseKernel_of_almostSimple
    (numberFieldAlmostSimpleSimplyConnectedGaloisHasseKernel_of_absolute h)

end Langlands.GroupScheme
