import Langlands.GroupScheme.Rational.AdjointHasseAlmostSimple
import Langlands.GroupScheme.Rational.NumberFieldWeilCocycleTransfer
import Langlands.GroupScheme.AffineWeilAlgebraProduct
import Langlands.GroupScheme.Reductive.AffineAdjointWeilRestrictionStatement
import Langlands.GroupScheme.Reductive.AlmostSimpleGeometricBaseChange
import Langlands.GroupScheme.Reductive.GeometricNontrivial
import Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Unramified.Field

/-! # The number-field adjoint Hasse kernel reduces to absolutely almost-simple groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A field-valued pullback is absolutely almost simple if the geometric fibre at its image
is almost simple. -/
theorem isAbsolutelyAlmostSimple_fieldPoint_of_geometricFiber {S : Scheme.{u}}
    (G : GroupScheme S) {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (h : IsAlmostSimple (geometricFiber G (b (IsLocalRing.closedPoint k)))) :
    IsAbsolutelyAlmostSimple ((baseChange b).obj G) := by
  let s := b (IsLocalRing.closedPoint k)
  let E := S.residueField s
  let K := AlgebraicClosure k
  let U := (baseChange (S.fromSpecResidueField s)).obj G
  let e := Spec.map (fieldPointResidueMap b)
  let a := toAlgebraicClosure E
  let c := toAlgebraicClosure k
  let : Algebra E k := (fieldPointResidueMap b).hom.toAlgebra
  let : Algebra E K := ((algebraMap k K).comp (algebraMap E k)).toAlgebra
  let j : AlgebraicClosure E →ₐ[E] K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure E) K := j.toRingHom.toAlgebra
  let d := algebraBaseMap (AlgebraicClosure E) K
  have hU : IsAlmostSimple ((baseChange a).obj U) :=
    h.of_iso (baseChangeCompIso (S.fromSpecResidueField s) a G).symm
  have hsq : c ≫ e = d ≫ a := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => (j.commutes x).symm
  have hcomp : IsAlmostSimple ((baseChange (c ≫ e)).obj U) := by
    rw [hsq]
    exact (hU.baseChange_of_isAlgClosed (K := K)).of_iso (baseChangeCompIso a d U)
  have hpull : IsAlmostSimple ((baseChange c).obj ((baseChange e).obj U)) :=
    hcomp.of_iso (baseChangeCompIso e c U).symm
  have hgeom := hpull.of_iso ((baseChange c).mapIso (fieldPointFiberIso G b))
  exact ⟨IsAlmostSimple.of_fieldExtension hgeom, hgeom⟩

/-- The finite Galois number-field Hasse kernel for absolutely almost-simple adjoint groups. -/
def NumberFieldAbsolutelyAlmostSimpleAdjointGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsAdjoint G → IsAbsolutelyAlmostSimple G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))), ξ.LocallyTrivial → ξ.IsTrivial

private theorem fibrewiseAdjoint_nontrivial {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsAdjoint G) (hs : IsAlmostSimple G) :
    IsFibrewiseAdjoint G ∧ IsFibrewiseNontrivial G := by
  have hnt : HasNontrivialPoint G := by
    by_contra h
    apply hs.noncommutative
    intro T x y
    have hx : x = 1 := by
      by_contra hx
      exact h ⟨T, x, hx⟩
    rw [hx]
    exact Commute.one_left y
  suffices h : ∀ s : Spec (CommRingCat.of F),
      IsAdjoint (geometricFiber G s) ∧ HasNontrivialPoint (geometricFiber G s) from
    ⟨fun s => (h s).1, fun s => (h s).2⟩
  intro s
  let K := AlgebraicClosure ((Spec (CommRingCat.of F)).residueField s)
  obtain ⟨a, ha⟩ := Spec.map_surjective (geometricPoint _ s)
  let : Algebra F K := a.hom.toAlgebra
  change IsAdjoint ((baseChange (geometricPoint _ s)).obj G) ∧
    HasNontrivialPoint ((baseChange (geometricPoint _ s)).obj G)
  rw [← ha]
  exact ⟨hG.baseChange_fieldExtension, (hasNontrivialPoint_fieldExtension_iff G).mpr hnt⟩

set_option maxHeartbeats 800000 in
/-- Given the affine adjoint Weil presentation, the absolutely almost-simple arithmetic
kernel suffices for all almost-simple adjoint groups. -/
theorem numberFieldAlmostSimpleAdjointGaloisHasseKernel_of_absolute
    (hWeil : AffineAdjointWeilRestrictionStatement.{u})
    (h : NumberFieldAbsolutelyAlmostSimpleAdjointGaloisHasseKernelStatement.{u}) :
    NumberFieldAlmostSimpleAdjointGaloisHasseKernelStatement.{u} := by
  classical
  intro F _ _ G hG hs L _ _ _ _ ξ hξ
  obtain ⟨hfadj, hfnt⟩ := fibrewiseAdjoint_nontrivial hG hs
  obtain ⟨B, _, _, _, _, _, H, _, _, _, _, hfiber, ⟨e⟩⟩ :=
    (hWeil F G hG.isSemisimple.isConnectedReductive.isReductive hfadj hfnt).1
  let : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field F B
  let : IsArtinianRing B := IsArtinianRing.of_finite F B
  let I := MaximalSpectrum B
  let : Fintype I := Fintype.ofFinite I
  let D (i : I) := B ⧸ i.asIdeal
  let : ∀ i : I, Field (D i) := fun i => Ideal.Quotient.field i.asIdeal
  let : ∀ i : I, Module.Finite F (D i) := fun i => Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F i.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
  let : ∀ i : I, NumberField (D i) := fun _ => NumberField.of_module_finite F _
  have hb : Function.Bijective (AffineWeil.AlgebraProduct.productMap (A := F) (B := B) (D := D)) := by
    change Function.Bijective (fun (b : B) (i : I) => Ideal.Quotient.mk i.asIdeal b)
    exact (IsArtinianRing.equivPi B).bijective
  let W := AffineWeil.AlgebraProduct.component (A := F) (D := D) H
  let j : G ≅ pi W := e ≪≫ AffineWeil.AlgebraProduct.iso hb H
  have htriv : (ξ.map j.hom).IsTrivial := by
    apply Cocycle.isTrivial_of_pi
    intro i
    let H' := AffineWeil.AlgebraProduct.factor (D := D) H i
    let b := Spec.algebraMap B (D i)
    have hHadj : IsAdjoint H' := (fieldAdjoint_iff_geometricFiber H b).mpr (hfiber _).1
    have hHabs : IsAbsolutelyAlmostSimple H' :=
      isAbsolutelyAlmostSimple_fieldPoint_of_geometricFiber H b (hfiber _).2
    let c : Cocycle (AffineWeil.groupScheme F (D i) H') (ringTest F L) :=
      (ξ.map j.hom).map (Pi.π W i)
    have hc : c.LocallyTrivial := (hξ.map j.hom).map (Pi.π W i)
    obtain ⟨E, _, _, _, _, r, hl, hreflect⟩ := AffineWeil.exists_finiteGalois_transfer F (D i) H' c hc
    exact hreflect (h (D i) H' hHadj hHabs E ((AffineWeil.transferCocycle F (D i) H' c).refine r) hl)
  obtain ⟨c, hc⟩ := htriv.map j.inv
  refine ⟨c, fun a b => ?_⟩
  have he := hc a b
  change (ξ.toFun a b ≫ j.hom.hom.hom) ≫ j.inv.hom.hom = _ at he
  rw [Category.assoc, ← Grp.comp_hom_hom, j.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at he
  exact he

/-- The full adjoint kernel follows from the absolutely almost-simple kernel and the affine
adjoint Weil restriction presentation. -/
theorem numberFieldAdjointGaloisHasseKernel_of_absolute
    (hWeil : AffineAdjointWeilRestrictionStatement.{u})
    (h : NumberFieldAbsolutelyAlmostSimpleAdjointGaloisHasseKernelStatement.{u}) :
    NumberFieldAdjointGaloisHasseKernelStatement.{u} :=
  numberFieldAdjointGaloisHasseKernel_of_almostSimple
    (numberFieldAlmostSimpleAdjointGaloisHasseKernel_of_absolute hWeil h)

end Langlands.GroupScheme
