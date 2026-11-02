import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine fibre-product points

The fibre product is over an arbitrary affine `R`-scheme `Spec C`. Points of
`Spec S` have a fixed `R`-structure, but no fixed `C`-algebra structure on `S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

open _root_.AlgebraicGeometry

theorem specAlgebraMap_tower (R C A : Type u)
    [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra C A] [Algebra R A] [IsScalarTower R C A] :
    Spec.algebraMap C A ≫ Spec.algebraMap R C = Spec.algebraMap R A := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R C A r).symm

variable (R C A B S : Type u)
variable [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R C] [Algebra R A] [Algebra R B] [Algebra R S]
variable [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]

/-- Actual `S`-points over `R` of `Spec A ×[Spec C] Spec B`. -/
def SpecFiberProductPoint :=
  {p : Spec (CommRingCat.of S) ⟶
      pullback (Spec.algebraMap C A) (Spec.algebraMap C B) //
    p ≫ pullback.fst _ _ ≫ Spec.algebraMap R A = Spec.algebraMap R S}

/-- Pairs of actual `R`-points with the same underlying `Spec C`-point. -/
def CompatibleSpecPointPair :=
  {pq : SpecPoint R A S × SpecPoint R B S //
    pq.1.1 ≫ Spec.algebraMap C A = pq.2.1 ≫ Spec.algebraMap C B}

omit [Algebra R B] [IsScalarTower R C B] in
theorem specFiberProduct_hom_base :
    (pullbackSpecIso C A B).hom ≫ Spec.algebraMap R (A ⊗[C] B) =
      pullback.fst (Spec.algebraMap C A) (Spec.algebraMap C B) ≫
        Spec.algebraMap R A := by
  calc
    _ = ((pullbackSpecIso C A B).hom ≫ Spec.algebraMap C (A ⊗[C] B)) ≫
        Spec.algebraMap R C := by
      rw [Category.assoc, specAlgebraMap_tower]
    _ = (pullback.fst (Spec.algebraMap C A) (Spec.algebraMap C B) ≫
        Spec.algebraMap C A) ≫ Spec.algebraMap R C :=
      congrArg (fun f => f ≫ Spec.algebraMap R C) (pullbackSpecIso_hom_base C A B)
    _ = _ := by rw [Category.assoc, specAlgebraMap_tower]

/-- The actual pullback points compared with the tensor-coordinate affine points. -/
def specFiberProductTensorEquiv :
    SpecFiberProductPoint R C A B S ≃ SpecPoint R (A ⊗[C] B) S where
  toFun p := ⟨p.1 ≫ (pullbackSpecIso C A B).hom, by
    rw [Category.assoc]
    exact (congrArg (fun f => p.1 ≫ f)
      (specFiberProduct_hom_base R C A B)).trans p.2⟩
  invFun p := ⟨p.1 ≫ (pullbackSpecIso C A B).inv, by
    have hb : (pullbackSpecIso C A B).inv ≫
        pullback.fst (Spec.algebraMap C A) (Spec.algebraMap C B) ≫
          Spec.algebraMap R A = Spec.algebraMap R (A ⊗[C] B) := by
      rw [← specFiberProduct_hom_base R C A B, Iso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => p.1 ≫ f) hb).trans p.2)⟩
  left_inv p := by
    apply Subtype.ext
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv p := by
    apply Subtype.ext
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The affine evaluation topology transported from the tensor coordinate algebra. -/
instance [TopologicalSpace S] : TopologicalSpace (SpecFiberProductPoint R C A B S) :=
  TopologicalSpace.induced (specFiberProductTensorEquiv R C A B S) inferInstance

/-- Compatible pairs carry the subspace topology of the product of factor point spaces. -/
instance [TopologicalSpace S] : TopologicalSpace (CompatibleSpecPointPair R C A B S) :=
  inferInstanceAs (TopologicalSpace {pq : SpecPoint R A S × SpecPoint R B S //
    pq.1.1 ≫ Spec.algebraMap C A = pq.2.1 ≫ Spec.algebraMap C B})

/-- This homeomorphism records the transport of the tensor-coordinate topology. -/
def specFiberProductTensorHomeomorph [TopologicalSpace S] :
    SpecFiberProductPoint R C A B S ≃ₜ SpecPoint R (A ⊗[C] B) S :=
  (specFiberProductTensorEquiv R C A B S).toHomeomorphOfIsInducing ⟨rfl⟩

/-- Restrict an actual fibre-product point along the two scheme projections. -/
def specFiberProductPointPair (p : SpecFiberProductPoint R C A B S) :
    CompatibleSpecPointPair R C A B S := by
  unfold SpecFiberProductPoint at p
  refine ⟨(⟨p.1 ≫ pullback.fst _ _, p.2⟩,
    ⟨p.1 ≫ pullback.snd _ _, ?_⟩), ?_⟩
  · calc
      _ = (p.1 ≫ pullback.snd _ _ ≫ Spec.algebraMap C B) ≫
          Spec.algebraMap R C := by
        simp only [Category.assoc, specAlgebraMap_tower]
      _ = (p.1 ≫ pullback.fst _ _ ≫ Spec.algebraMap C A) ≫
          Spec.algebraMap R C :=
        congrArg (fun f => (p.1 ≫ f) ≫ Spec.algebraMap R C)
          (pullback.condition (f := Spec.algebraMap C A) (g := Spec.algebraMap C B)).symm
      _ = p.1 ≫ pullback.fst _ _ ≫ Spec.algebraMap R A := by
        simp only [Category.assoc, specAlgebraMap_tower]
      _ = _ := p.2
  · exact (Category.assoc _ _ _).trans <|
      ((congrArg (fun f => p.1 ≫ f)
        (pullback.condition (f := Spec.algebraMap C A) (g := Spec.algebraMap C B))).trans
          (Category.assoc _ _ _).symm)

/-- The categorical pullback lift of a compatible pair, retaining the equation over `R`. -/
def specFiberProductPointLift (pq : CompatibleSpecPointPair R C A B S) :
    SpecFiberProductPoint R C A B S :=
  ⟨pullback.lift pq.1.1.1 pq.1.2.1 pq.2, by
    rw [pullback.lift_fst_assoc]
    exact pq.1.1.2⟩

/-- The canonical bijection between actual fibre-product points and compatible pairs. -/
def specFiberProductPointPairEquiv :
    SpecFiberProductPoint R C A B S ≃ CompatibleSpecPointPair R C A B S where
  toFun := specFiberProductPointPair R C A B S
  invFun := specFiberProductPointLift R C A B S
  left_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv pq := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact pullback.lift_fst _ _ _
    · apply Subtype.ext
      exact pullback.lift_snd _ _ _

end Langlands.AlgebraicGeometry.PointTopology
