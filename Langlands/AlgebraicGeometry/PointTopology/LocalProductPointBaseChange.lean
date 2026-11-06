import Langlands.Global.AdelicLevelModelTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorTopology

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- The original pullback-adjunction point equivalence commutes with a literal
map of value algebras, with the lower scalar action restricted. -/
theorem ringPointBaseChangeEquiv_changeRing
    (A B S T : Type u) [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B S] [Algebra B T]
    [IsScalarTower A B S] [IsScalarTower A B T]
    (X : Over (Spec (CommRingCat.of A))) (f : S →ₐ[B] T) (p : RingPoint A X S) :
    ringPointBaseChangeEquiv A B T X (p.changeRing (f.restrictScalars A)) =
      (ringPointBaseChangeEquiv A B S X p).changeRing f := by
  apply (ringPointBaseChangeEquiv A B T X).symm.injective
  apply RingPoint.ext
  rw [Equiv.symm_apply_apply, ringPointBaseChangeEquiv_symm_left]
  change (p.changeRing (f.restrictScalars A)).left =
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (ringPointBaseChangeEquiv A B S X p).left) ≫ _
  rw [Category.assoc, ringPointBaseChangeEquiv_left_fst]
  rfl

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)]
  [∀ i, Algebra A (R i)] [∀ i, Algebra B (R i)] [∀ i, IsScalarTower A B (R i)]
  (X : Over (Spec (CommRingCat.of A)))

/-- Every original product coordinate commutes with actual scheme base change. -/
theorem productPointMap_ringPointBaseChangeEquiv
    (p : RingPoint A X (∀ i, R i)) (i : ι) :
    productPointMap B R (ringBaseChange A B X)
        (ringPointBaseChangeEquiv A B (∀ i, R i) X p) i =
      ringPointBaseChangeEquiv A B (R i) X (productPointMap A R X p i) := by
  exact (ringPointBaseChangeEquiv_changeRing A B (∀ i, R i) (R i) X
    (Pi.evalAlgHom B R i) p).symm

variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
  [∀ i, IsLocalRing (R i)] [∀ i, IsOpenUnits (R i)]

/-- Original relative point factors and the original local model factors have
the same independently constructed product topology. -/
def localFactorPointHomeomorph :
    letI : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
      fun i => schemePointTopology A X (R i)
    letI := localModelPointProductTopology A R X
    (∀ i, RingPoint A X (R i)) ≃ₜ
      (∀ i, RingPoint (R i) (ringBaseChange A (R i) X) (R i)) := by
  letI : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
    fun i => schemePointTopology A X (R i)
  letI : ∀ i, TopologicalSpace
      (RingPoint (R i) (ringBaseChange A (R i) X) (R i)) :=
    fun i => schemePointTopology (R i) (ringBaseChange A (R i) X) (R i)
  exact Homeomorph.piCongrRight fun i => schemePointBaseChangeHomeomorph A (R i) (R i) X

/-- The literal relative coordinate map induces the existing local-model
product topology, without any scheme finiteness or separation premise. -/
theorem productPointMap_isInducing_localProductPointTopology :
    let := localProductPointTopology A R X
    let : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
      fun i => schemePointTopology A X (R i)
    IsInducing (productPointMap A R X) := by
  let := localProductPointTopology A R X
  let : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
    fun i => schemePointTopology A X (R i)
  let := localModelPointProductTopology A R X
  let H := localFactorPointHomeomorph A R X
  apply H.isInducing.of_comp_iff.mp
  exact localProductPointMap_isInducing A R X

/-- Actual scheme base change preserves the independently defined product
point topologies, using the original pullback-adjunction point map. -/
def localProductPointBaseChangeHomeomorph :
    letI := localProductPointTopology A R X
    letI := localProductPointTopology B R (ringBaseChange A B X)
    RingPoint A X (∀ i, R i) ≃ₜ
      RingPoint B (ringBaseChange A B X) (∀ i, R i) := by
  letI := localProductPointTopology A R X
  letI := localProductPointTopology B R (ringBaseChange A B X)
  letI : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
    fun i => schemePointTopology A X (R i)
  letI : ∀ i, TopologicalSpace (RingPoint B (ringBaseChange A B X) (R i)) :=
    fun i => schemePointTopology B (ringBaseChange A B X) (R i)
  let E := ringPointBaseChangeEquiv A B (∀ i, R i) X
  let H := Homeomorph.piCongrRight fun i => schemePointBaseChangeHomeomorph A B (R i) X
  have hmap : productPointMap B R (ringBaseChange A B X) ∘ E =
      H ∘ productPointMap A R X := by
    funext p i
    exact productPointMap_ringPointBaseChangeEquiv A B R X p i
  have hcomp : IsInducing (productPointMap B R (ringBaseChange A B X) ∘ E) := by
    rw [hmap]
    exact H.isInducing.comp (productPointMap_isInducing_localProductPointTopology A R X)
  have hind : IsInducing E :=
    (productPointMap_isInducing_localProductPointTopology B R
      (ringBaseChange A B X)).of_comp_iff.mp hcomp
  exact E.toHomeomorphOfIsInducing hind

/-- The topological comparison retains precisely the original point equivalence. -/
@[simp]
theorem localProductPointBaseChangeHomeomorph_apply (p : RingPoint A X (∀ i, R i)) :
    localProductPointBaseChangeHomeomorph A B R X p =
      ringPointBaseChangeEquiv A B (∀ i, R i) X p := rfl

end Langlands.AlgebraicGeometry.PointTopology
