import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Adjoin.FG

/-! # Descent of finitely many field-valued points of a finite scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

universe u

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Finitely many points valued in the field `K` of a scheme finite over
`Spec C` descend to one finitely generated subalgebra of `K` containing `C`. -/
def FiniteFieldPointDescentStatement : Prop :=
  ∀ (K : Type u) [Field K] (C : Subalgebra ℤ K), C.FG →
    ∀ (Y : Over (Spec (.of ↥C))) [IsFinite Y.hom]
      (I : Type u) [Finite I] (x : I → RingPoint ↥C Y K),
      ∃ (D : Subalgebra ℤ K) (hCD : C ≤ D), D.FG ∧
        letI : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
        letI : IsScalarTower ↥C ↥D K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        ∃ y : I → RingPoint ↥C Y ↥D,
          ∀ i, ringTestMap ↥C (IsScalarTower.toAlgHom ↥C ↥D K) ≫ y i = x i

/-- Adjoin the images of finitely many module generators under the supplied
coordinate maps, then use the same coordinate maps over the larger subalgebra. -/
theorem finiteFieldPointDescent : FiniteFieldPointDescentStatement.{u} := by
  intro K _ C hC Y _ I _ x
  classical
  let : Fintype I := Fintype.ofFinite I
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let A := AffineCoordinateRing ↥C Y
  let e := affineSchemeOverIso ↥C Y
  have hfin : IsFinite (Spec.algebraMap ↥C A) := by
    rw [affineCoordinateSpecMap]
    have : IsIso Y.left.isoSpec.inv := inferInstance
    infer_instance
  have : Module.Finite ↥C A :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ↥C) (M := A)
  let f (i : I) : A →ₐ[↥C] K := affineRingPointEquiv ↥C A K (x i ≫ e.hom)
  let T : Finset K := (Finset.univ ×ˢ s).image (fun a : I × A => f a.1 a.2)
  let D : Subalgebra ℤ K := C ⊔ Algebra.adjoin ℤ (T : Set K)
  have hCD : C ≤ D := le_sup_left
  have hTD : Algebra.adjoin ℤ (T : Set K) ≤ D := le_sup_right
  have hD : D.FG := hC.sup ⟨T, rfl⟩
  have hmem (i : I) (a : A) : f i a ∈ D := by
    have ha : a ∈ Submodule.span ↥C (s : Set A) := hs.symm ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun b _ => f i b ∈ D) ?_ ?_ ?_ ?_ ha
    · intro b hb
      exact hTD (Algebra.subset_adjoin
        (Finset.mem_image.mpr ⟨(i, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩))
    · rw [map_zero]
      exact D.zero_mem
    · intro b c _ _ hb hc
      rw [_root_.map_add]
      exact D.add_mem hb hc
    · intro r b _ hb
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      exact D.mul_mem (hCD r.property) hb
  refine ⟨D, hCD, hD, ?_⟩
  let : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
  let : IsScalarTower ↥C ↥D K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let fD (i : I) : A →ₐ[↥C] ↥D :=
    { toRingHom := (f i).toRingHom.codRestrict D (hmem i)
      commutes' := fun r => Subtype.ext ((f i).commutes r) }
  let y (i : I) : RingPoint ↥C Y ↥D := ringTestMap ↥C (fD i) ≫ e.inv
  refine ⟨y, fun i => ?_⟩
  change ringTestMap ↥C (IsScalarTower.toAlgHom ↥C ↥D K) ≫
    (ringTestMap ↥C (fD i) ≫ e.inv) = x i
  rw [← Category.assoc, ← ringTestMap_comp]
  change ringTestMap ↥C (f i) ≫ e.inv = x i
  rw [show ringTestMap ↥C (f i) = x i ≫ e.hom from ringTestMap_affineRingPointEquiv ↥C _,
    Category.assoc, e.hom_inv_id, Category.comp_id]

end Langlands.AlgebraicGeometry
