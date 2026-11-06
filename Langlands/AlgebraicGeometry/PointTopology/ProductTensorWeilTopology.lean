import Langlands.AlgebraicGeometry.PointTopology.ProductTensorWeilPoints
import Langlands.Global.AdelicLevelModelTopology

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {ι : Type u} (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
  (J : ι → Type u) [∀ i, Finite (J i)] (D : ∀ i, J i → Type u)
  [∀ i j, CommRing (D i j)] [∀ i j, Algebra (C i) (D i j)] [∀ i j, Algebra B (D i j)]
  [∀ i j, Module.Finite (C i) (D i j)] [∀ i j, Module.Projective (C i) (D i j)]
  [∀ i, TopologicalSpace (C i)] [∀ i, IsTopologicalRing (C i)]
  [∀ i, IsLocalRing (C i)] [∀ i, IsOpenUnits (C i)]
  [∀ i j, TopologicalSpace (D i j)] [∀ i j, IsTopologicalRing (D i j)]
  [∀ i j, IsLocalRing (D i j)] [∀ i j, IsOpenUnits (D i j)]
  [∀ i j, IsModuleTopology (C i) (D i j)]
  (e : ∀ i, C i ⊗[A] B ≃ₐ[C i] (∀ j, D i j))
  (he : ∀ i (b : B) (j : J i), e i (1 ⊗ₜ[A] b) j = algebraMap B (D i j) b)
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]
  [IsSeparated Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- The product of the original local Weil homeomorphisms, with the original local base changes. -/
def productTensorWeilLocalPointHomeomorph (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : ∀ i, TopologicalSpace
        (RingPoint (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)) :=
      fun i => schemePointTopology (C i)
        (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)
    letI : ∀ z : Σ i, J i, TopologicalSpace (RingPoint B Y (D z.1 z.2)) :=
      fun z => schemePointTopology B Y (D z.1 z.2)
    (∀ i, RingPoint (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)) ≃ₜ
      (∀ z : Σ i, J i, RingPoint B Y (D z.1 z.2)) := by
  letI : ∀ i, TopologicalSpace
      (RingPoint (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)) :=
    fun i => schemePointTopology (C i)
      (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)
  letI : ∀ i, TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) (C i)) :=
    fun i => schemePointTopology A (affineChartWeilRestriction A B Y) (C i)
  letI : ∀ i j, TopologicalSpace (RingPoint B Y (D i j)) :=
    fun i j => schemePointTopology B Y (D i j)
  letI : ∀ z : Σ i, J i, TopologicalSpace (RingPoint B Y (D z.1 z.2)) :=
    fun z => schemePointTopology B Y (D z.1 z.2)
  let curryHomeo : (∀ i, ∀ j : J i, RingPoint B Y (D i j)) ≃ₜ
      (∀ z : Σ i, J i, RingPoint B Y (D z.1 z.2)) :=
    { toFun := fun x z => x z.1 z.2
      invFun := fun x i j => x ⟨i, j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun z =>
        (continuous_apply z.2).comp (continuous_apply z.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
        continuous_apply (⟨i, j⟩ : Σ i, J i) }
  exact (Homeomorph.piCongrRight fun i =>
      (schemePointBaseChangeHomeomorph A (C i) (C i)
        (affineChartWeilRestriction A B Y)).symm).trans
    ((Homeomorph.piCongrRight fun i =>
      completedTensorWeilRestrictionPointHomeomorph A B (C i) (D i) (e i) (he i) Y hY).trans
        curryHomeo)

/-- The product homeomorphism acts on the actual global coordinate map by the proved global point map. -/
theorem productTensorWeilLocalPointHomeomorph_localProductPointMap
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) (i : ι) (j : J i) :
    productTensorWeilLocalPointHomeomorph A B C J D e he Y hY
        (localProductPointMap A C (affineChartWeilRestriction A B Y) p) ⟨i, j⟩ =
      productTensorWeilPointEquiv A B C J D e he Y hY p ⟨i, j⟩ := by
  let : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) (C i)) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) (C i)
  let : TopologicalSpace
      (RingPoint (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)) :=
    schemePointTopology (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)
  let : ∀ j : J i, TopologicalSpace (RingPoint B Y (D i j)) :=
    fun j => schemePointTopology B Y (D i j)
  rw [productTensorWeilPointEquiv_local]
  change completedTensorWeilRestrictionPointHomeomorph A B (C i) (D i) (e i) (he i) Y hY
      ((schemePointBaseChangeHomeomorph A (C i) (C i)
        (affineChartWeilRestriction A B Y)).symm
        (ringPointBaseChangeEquiv A (C i) (C i) (affineChartWeilRestriction A B Y)
          (p.changeRing (Pi.evalAlgHom A C i)))) j = _
  rw [← schemePointBaseChangeHomeomorph_apply, Homeomorph.symm_apply_apply,
    completedTensorWeilRestrictionPointHomeomorph_counit]
  rfl

/-- The existing product-induced topology on actual global Weil points gives the original upper product topology. -/
def productTensorWeilPointHomeomorph (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) :=
      localProductPointTopology A C (affineChartWeilRestriction A B Y)
    letI : ∀ z : Σ i, J i, TopologicalSpace (RingPoint B Y (D z.1 z.2)) :=
      fun z => schemePointTopology B Y (D z.1 z.2)
    RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i) ≃ₜ
      (∀ z : Σ i, J i, RingPoint B Y (D z.1 z.2)) := by
  letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) :=
    localProductPointTopology A C (affineChartWeilRestriction A B Y)
  letI : ∀ i, TopologicalSpace
      (RingPoint (C i) (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)) :=
    fun i => schemePointTopology (C i)
      (ringBaseChange A (C i) (affineChartWeilRestriction A B Y)) (C i)
  letI : ∀ z : Σ i, J i, TopologicalSpace (RingPoint B Y (D z.1 z.2)) :=
    fun z => schemePointTopology B Y (D z.1 z.2)
  let E := productTensorWeilPointEquiv A B C J D e he Y hY
  let H := productTensorWeilLocalPointHomeomorph A B C J D e he Y hY
  have hmap : (E : _ → _) =
      H ∘ localProductPointMap A C (affineChartWeilRestriction A B Y) := by
    funext p z
    exact (productTensorWeilLocalPointHomeomorph_localProductPointMap
      A B C J D e he Y hY p z.1 z.2).symm
  have hind : IsInducing (E : _ → _) := by
    rw [hmap]
    exact H.isInducing.comp (localProductPointMap_isInducing A C
      (affineChartWeilRestriction A B Y))
  exact IsHomeomorph.homeomorph E
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, E.injective⟩, E.surjective⟩)

/-- The topology construction retains exactly the already proved original global Weil point equivalence. -/
@[simp]
theorem productTensorWeilPointHomeomorph_apply (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) :
    productTensorWeilPointHomeomorph A B C J D e he Y hY p =
      productTensorWeilPointEquiv A B C J D e he Y hY p := rfl

end Langlands.AlgebraicGeometry.PointTopology
