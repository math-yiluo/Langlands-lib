import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPoints
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions

/-!
# Final topologies on actual scheme-point colimits

Stage topologies are specified independently. In the adelic application these
must be the global product topologies of Conrad Theorem 3.6.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable {J : Type u} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} R)
variable (X : Over (Spec (CommRingCat.of R)))
variable (τ : ∀ j : J, TopologicalSpace (RingPoint R X (F.obj j)))

/-- The final topology from the actual stage maps into their type colimit. -/
@[instance_reducible]
def ringPointColimitTopology : TopologicalSpace (RingPointColimit R F X) :=
  ⨆ j : J, @TopologicalSpace.coinduced _ _ (ringPointColimitι R F X j) (τ j)

/-- The final topology from actual stage points into points over the cocone algebra. -/
@[instance_reducible]
def ringPointCoconeTopology (c : Cocone F) : TopologicalSpace (RingPoint R X c.pt) :=
  ⨆ j : J, @TopologicalSpace.coinduced _ _
    ((ringPointCocone R F X c).ι.app j) (τ j)

theorem ringPointColimitTopology_isOpen_iff (V : Set (RingPointColimit R F X)) :
    IsOpen[ringPointColimitTopology R F X τ] V ↔
      ∀ j, IsOpen[τ j] ((ringPointColimitι R F X j) ⁻¹' V) := by
  rw [ringPointColimitTopology, isOpen_iSup_iff]
  rfl

theorem ringPointCoconeTopology_isOpen_iff (c : Cocone F)
    (V : Set (RingPoint R X c.pt)) :
    IsOpen[ringPointCoconeTopology R F X τ c] V ↔
      ∀ j, IsOpen[τ j] ((fun p : RingPoint R X (F.obj j) =>
        p.changeRing (c.ι.app j).hom) ⁻¹' V) := by
  rw [ringPointCoconeTopology, isOpen_iSup_iff]
  rfl

/-- Each stage map is continuous by the definition of the final topology. -/
theorem ringPointColimitTopology_continuous_ι (j : J) :
    Continuous[τ j, ringPointColimitTopology R F X τ] (ringPointColimitι R F X j) :=
  continuous_iSup_rng (i := j) continuous_coinduced_rng

theorem ringPointCoconeTopology_continuous_ι (c : Cocone F) (j : J) :
    Continuous[τ j, ringPointCoconeTopology R F X τ c]
      (fun p : RingPoint R X (F.obj j) => p.changeRing (c.ι.app j).hom) :=
  continuous_iSup_rng (i := j) continuous_coinduced_rng

/-- Maps out of the point quotient are continuous exactly when all restrictions are. -/
theorem ringPointColimitTopology_continuous_iff {Y : Type v} [TopologicalSpace Y]
    (f : RingPointColimit R F X → Y) :
    Continuous[ringPointColimitTopology R F X τ, inferInstance] f ↔
      ∀ j, Continuous[τ j, inferInstance] (f ∘ ringPointColimitι R F X j) := by
  unfold ringPointColimitTopology
  rw [continuous_iSup_dom]
  exact forall_congr' (fun _ => continuous_coinduced_dom)

theorem ringPointCoconeTopology_continuous_iff (c : Cocone F)
    {Y : Type v} [TopologicalSpace Y] (f : RingPoint R X c.pt → Y) :
    Continuous[ringPointCoconeTopology R F X τ c, inferInstance] f ↔
      ∀ j, Continuous[τ j, inferInstance]
        (f ∘ fun p : RingPoint R X (F.obj j) => p.changeRing (c.ι.app j).hom) := by
  unfold ringPointCoconeTopology
  rw [continuous_iSup_dom]
  exact forall_congr' (fun _ => continuous_coinduced_dom)

/-- Coinducing along the canonical comparison gives the independently defined
final topology on the cocone-algebra points. No bijectivity is used here. -/
theorem ringPointColimitMap_coinduced (c : Cocone F) :
    TopologicalSpace.coinduced (ringPointColimitMap R F X c)
      (ringPointColimitTopology R F X τ) = ringPointCoconeTopology R F X τ c := by
  unfold ringPointColimitTopology ringPointCoconeTopology
  rw [coinduced_iSup]
  apply iSup_congr
  intro j
  rw [coinduced_compose]
  rfl

theorem ringPointColimitMap_continuous (c : Cocone F) :
    Continuous[ringPointColimitTopology R F X τ, ringPointCoconeTopology R F X τ c]
      (ringPointColimitMap R F X c) := by
  apply continuous_iff_coinduced_le.mpr
  rw [ringPointColimitMap_coinduced]

/-- If the actual comparison is surjective, its final-topology map is a quotient map. -/
theorem ringPointColimitMap_isQuotientMap (c : Cocone F)
    (h : Function.Surjective (ringPointColimitMap R F X c)) :
    @IsQuotientMap _ _ (ringPointColimitTopology R F X τ)
      (ringPointCoconeTopology R F X τ c) (ringPointColimitMap R F X c) := by
  let := ringPointColimitTopology R F X τ
  let := ringPointCoconeTopology R F X τ c
  exact
    { eq_coinduced := (ringPointColimitMap_coinduced R F X τ c).symm
      surjective := h }

/-- Upgrade an independently proved bijection to the final-topology comparison. -/
def ringPointColimitHomeomorph (c : Cocone F)
    (h : Function.Bijective (ringPointColimitMap R F X c)) :
    @Homeomorph (RingPointColimit R F X) (RingPoint R X c.pt)
      (ringPointColimitTopology R F X τ) (ringPointCoconeTopology R F X τ c) := by
  letI := ringPointColimitTopology R F X τ
  letI := ringPointCoconeTopology R F X τ c
  exact (Equiv.ofBijective (ringPointColimitMap R F X c) h).toHomeomorph
    (fun _ => (ringPointColimitMap_isQuotientMap R F X τ c h.2).isOpen_preimage)

@[simp]
theorem ringPointColimitHomeomorph_apply (c : Cocone F)
    (h : Function.Bijective (ringPointColimitMap R F X c)) (p : RingPointColimit R F X) :
    ringPointColimitHomeomorph R F X τ c h p = ringPointColimitMap R F X c p := rfl

/-- The actual image of a stage, before assigning it the quotient topology. -/
abbrev RingPointColimitStageImage (j : J) :=
  Set.range (ringPointColimitι R F X j)

/-- The surjection from a stage onto its actual image in the point quotient. -/
def ringPointColimitStageProjection (j : J) :
    RingPoint R X (F.obj j) → RingPointColimitStageImage R F X j :=
  Set.rangeFactorization (ringPointColimitι R F X j)

/-- The topology on a stage image is coinduced from the stage, without injectivity. -/
@[instance_reducible]
def ringPointColimitStageImageTopology (j : J) :
    TopologicalSpace (RingPointColimitStageImage R F X j) :=
  @TopologicalSpace.coinduced _ _ (ringPointColimitStageProjection R F X j) (τ j)

theorem ringPointColimitStageProjection_isQuotientMap (j : J) :
    @IsQuotientMap _ _ (τ j) (ringPointColimitStageImageTopology R F X τ j)
      (ringPointColimitStageProjection R F X j) := by
  let := τ j
  let := ringPointColimitStageImageTopology R F X τ j
  exact
    { eq_coinduced := rfl
      surjective := Set.rangeFactorization_surjective }

end Langlands.AlgebraicGeometry.PointTopology
