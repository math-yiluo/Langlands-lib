import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.Topology.QuotientLocalSections

/-! # Algebraic sections on actual scheme point spaces -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Each actual value-ring point lies in an open subscheme with a section of `f`. -/
def HasOpenSectionsAtPoints {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) : Prop :=
  ∀ p : RingPoint R Y S, ∃ U : Y.left.Opens, Set.range p.left ⊆ U ∧
    ∃ s : openOver R Y U ⟶ X, s ≫ f = openOverι R Y U

variable [TopologicalSpace S] [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]

/-- Actual open-subscheme points with the final topology are the image-contained
locus with its ambient subspace topology. -/
def schemeOpenPointHomeomorph (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens) :
    letI : TopologicalSpace (RingPoint R (openOver R Y U) S) :=
      schemePointTopology R (openOver R Y U) S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    RingPoint R (openOver R Y U) S ≃ₜ
      {p : RingPoint R Y S // Set.range p.left ⊆ U} := by
  letI : TopologicalSpace (RingPoint R (openOver R Y U) S) :=
    schemePointTopology R (openOver R Y U) S
  letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  exact (openPointEquiv R Y S U).toHomeomorphOfIsInducing
    (IsInducing.subtypeVal.of_comp_iff.mp (schemeOpenPoint_proof R S Y U).isInducing)

@[simp] theorem schemeOpenPointHomeomorph_apply
    (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens)
    (p : RingPoint R (openOver R Y U) S) :
    (schemeOpenPointHomeomorph R S Y U p).val = openPointMap R Y S U p := rfl

/-- The locus of actual points contained in an open subscheme is topologically open. -/
theorem isOpen_schemePointLocus (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens) :
    IsOpen[schemePointTopology R Y S] {p : RingPoint R Y S | Set.range p.left ⊆ U} := by
  let : TopologicalSpace (RingPoint R (openOver R Y U) S) :=
    schemePointTopology R (openOver R Y U) S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  have hr : Set.range (openPointMap R Y S U) =
      {p : RingPoint R Y S | Set.range p.left ⊆ U} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact (openPointEquiv R Y S U q).property
    · intro hp
      exact ⟨openPointLift R Y S U p hp, openPointMap_lift R Y S U p hp⟩
  rw [← hr]
  exact (schemeOpenPoint_proof R S Y U).isOpen_range

/-- Algebraic open sections through all actual points induce continuous local
sections of the actual postcomposition map with its canonical point topologies. -/
theorem hasContinuousLocalSections_schemePointMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (hs : HasOpenSectionsAtPoints R S f) :
    @Langlands.Topology.HasContinuousLocalSections (RingPoint R X S) (RingPoint R Y S)
      (schemePointTopology R X S) (schemePointTopology R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  intro p
  obtain ⟨U, hp, s, hsf⟩ := hs p
  let : TopologicalSpace (RingPoint R (openOver R Y U) S) :=
    schemePointTopology R (openOver R Y U) S
  let V : Set (RingPoint R Y S) := {q | Set.range q.left ⊆ U}
  let e := schemeOpenPointHomeomorph R S Y U
  let t : V → RingPoint R X S := fun q => e.symm q ≫ s
  refine ⟨V, isOpen_schemePointLocus R S Y U, hp, t, ?_, ?_⟩
  · exact (schemePointContinuity_proof R S _ _ s).comp e.symm.continuous
  · intro q
    change (e.symm q ≫ s) ≫ f = q.val
    exact (Category.assoc (e.symm q) s f).trans
      ((congrArg (fun a : openOver R Y U ⟶ Y => e.symm q ≫ a) hsf).trans
        (congrArg Subtype.val (e.apply_symm_apply q)))

/-- The actual point map is surjective when algebraic open sections exist at all points. -/
theorem surjective_schemePointMap_of_open_sections
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (hs : HasOpenSectionsAtPoints R S f) :
    Function.Surjective (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  exact (hasContinuousLocalSections_schemePointMap R S f hs).surjective

/-- The target canonical topology is precisely the quotient topology of the
actual point map when algebraic open sections exist at every point. -/
theorem isQuotientMap_schemePointMap_of_open_sections
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (hs : HasOpenSectionsAtPoints R S f) :
    @IsQuotientMap (RingPoint R X S) (RingPoint R Y S)
      (schemePointTopology R X S) (schemePointTopology R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  exact (hasContinuousLocalSections_schemePointMap R S f hs).isQuotientMap
    (schemePointContinuity_proof R S X Y f)

end Langlands.AlgebraicGeometry.PointTopology
