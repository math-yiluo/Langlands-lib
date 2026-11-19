import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProduct

/-! # Reduction of the simply connected Hasse kernel to almost-simple groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Cocycle

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A homomorphism sends a trivial cocycle to a trivial cocycle. -/
theorem IsTrivial.map {ξ : Cocycle G U} (h : ξ.IsTrivial) (q : G ⟶ H) :
    (ξ.map q).IsTrivial := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ≫ q.hom.hom, fun a c => ?_⟩
  change ξ.toFun a c ≫ q.hom.hom = _
  rw [hf, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc]

/-- Local triviality is preserved by every homomorphism of coefficient groups. -/
theorem LocallyTrivial.map {F : Type u} [Field F] [NumberField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    {ξ : Cocycle G U} (h : ξ.LocallyTrivial) (q : G ⟶ H) : (ξ.map q).LocallyTrivial := by
  intro v
  let b := algebraBaseMap F (Global.placeCompletion F v)
  let r := (Over.mapPullbackAdj b).counit.app U
  have hv : (ξ.baseChange b _ r).IsTrivial := h v
  obtain ⟨f, hf⟩ := hv.map ((GroupScheme.baseChange b).map q)
  refine ⟨f, fun a c => ?_⟩
  rw [baseChange_map_toFun]
  exact hf a c

/-- Trivializations of each finite product coordinate assemble into one trivialization. -/
theorem isTrivial_of_pi {I : Type u} [Finite I] {A : I → GroupScheme S}
    (ξ : Cocycle (pi A) U) (h : ∀ i, (ξ.map (Pi.π A i)).IsTrivial) :
    ξ.IsTrivial := by
  classical
  choose f hf using h
  let t := (piPointsEquiv A U).symm f
  refine ⟨t, fun {Z} a c => ?_⟩
  apply (piPointsEquiv A Z).injective
  rw [map_mul, map_inv]
  funext i
  change ξ.toFun a c ≫ (Pi.π A i).hom.hom =
    ((a ≫ t) ≫ (Pi.π A i).hom.hom) * ((c ≫ t) ≫ (Pi.π A i).hom.hom)⁻¹
  rw [Category.assoc a, Category.assoc c, piPointsEquiv_symm_π]
  exact hf i a c

end Cocycle

/-- The number-field finite Galois Hasse kernel for almost-simple simply connected groups. -/
def NumberFieldAlmostSimpleSimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G → IsAlmostSimple G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))), ξ.LocallyTrivial → ξ.IsTrivial

/-- The simply connected Hasse kernel follows from the almost-simple case. -/
theorem numberFieldSimplyConnectedGaloisHasseKernel_of_almostSimple
    (h : NumberFieldAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ hξ
  obtain ⟨D⟩ := hG.nonempty_almostSimpleProduct
  have hprod : (ξ.map D.iso.hom).IsTrivial := by
    apply Cocycle.isTrivial_of_pi
    intro i
    exact h F (D.factor i) (D.isSimplyConnected i) (D.isAlmostSimple i) L
      ((ξ.map D.iso.hom).map (Pi.π D.factor i)) ((hξ.map D.iso.hom).map (Pi.π D.factor i))
  obtain ⟨f, hf⟩ := hprod.map D.iso.inv
  refine ⟨f, fun a c => ?_⟩
  have hh := hf a c
  change (ξ.toFun a c ≫ D.iso.hom.hom.hom) ≫ D.iso.inv.hom.hom = _ at hh
  rw [Category.assoc, ← Grp.comp_hom_hom, D.iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at hh
  exact hh

end Langlands.GroupScheme
