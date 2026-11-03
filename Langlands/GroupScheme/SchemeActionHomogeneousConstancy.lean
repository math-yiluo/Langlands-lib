import Langlands.GroupScheme.SchemeActionOrbitDescent
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof

/-! # Fixed sections from proper homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {k : Type u} [Field k]
    {H N : GroupScheme (Spec (CommRingCat.of k))}
    {X Q : Over (Spec (CommRingCat.of k))}

/-- A subgroup-fixed rational orbit descends through an actual fpqc homogeneous
scheme quotient. Only the implication from equal images to equal cosets is needed. -/
theorem exists_homogeneousOrbitMap_factor
    (a : SchemeAction H X) (j : N ⟶ H) (q : H.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ H.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) :
    ∃ ρ : Q ⟶ X, q ≫ ρ = a.orbitMap x := by
  exact FiniteIndexTransfer.exists_factor j (a.orbitMap x) q hq
    (fun _ g h he => a.comp_orbitMap_eq_of_inv_mul_mem_range j x hx g h he)

/-- The actual orbit morphism on a homogeneous scheme quotient. -/
def descendedHomogeneousOrbitMap
    (a : SchemeAction H X) (j : N ⟶ H) (q : H.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ H.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) : Q ⟶ X :=
  (a.exists_homogeneousOrbitMap_factor j q hq x hx).choose

/-- Pullback along the quotient recovers the original orbit. -/
theorem quotient_comp_descendedHomogeneousOrbitMap
    (a : SchemeAction H X) (j : N ⟶ H) (q : H.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ H.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) :
    q ≫ a.descendedHomogeneousOrbitMap j q hq x hx = a.orbitMap x :=
  (a.exists_homogeneousOrbitMap_factor j q hq x hx).choose_spec

/-- If a connected reduced group has a proper homogeneous quotient by a
subgroup fixing a point in an affine scheme, then the entire group fixes it. -/
theorem isFixed_of_proper_homogeneousQuotient
    [IsAlgClosed k] [ConnectedSpace H.X.left] [IsReduced H.X.left] [IsAffine X.left]
    (a : SchemeAction H X) (j : N ⟶ H) (q : H.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ H.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) : a.IsFixed x := by
  have : ConnectedSpace Q.left := q.left.surjective.connectedSpace q.left.continuous
  have : IsReduced Q.left :=
    Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
      q.left
  let ρ := a.descendedHomogeneousOrbitMap j q hq x hx
  have hρ : q ≫ ρ = a.orbitMap x :=
    a.quotient_comp_descendedHomogeneousOrbitMap j q hq x hx
  let s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) ≫ q
  have hsρ : s ≫ ρ = x := by
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) ≫ q ≫ ρ = x
    rw [hρ, a.comp_orbitMap, a.act_one]
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    rw [hu, Category.id_comp]
  have hc : ρ = toUnit Q ≫ s ≫ ρ := by
    apply Over.OverMorphism.ext
    exact Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced
      Q.hom s.left (Over.w s) ρ.left
  apply (a.isFixed_iff_orbitMap_eq x).2
  calc
    a.orbitMap x = q ≫ ρ := hρ.symm
    _ = q ≫ (toUnit Q ≫ s ≫ ρ) := congrArg (fun f => q ≫ f) hc
    _ = toUnit H.X ≫ x := by rw [comp_toUnit_assoc, hsρ]

end Langlands.GroupScheme.SchemeAction
