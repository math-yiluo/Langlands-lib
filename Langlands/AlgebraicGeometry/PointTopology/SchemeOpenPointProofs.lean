import Langlands.AlgebraicGeometry.PointTopology.AffineOpenEmbeddingProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointStatements

/-!
# Gluing and functoriality on actual scheme point spaces
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Lift an actual relative morphism whose image lies in an open subscheme. -/
def relativeOpenLift {Y X : Over (Spec (CommRingCat.of R))}
    (f : Y ⟶ X) (U : X.left.Opens) (hf : Set.range f.left ⊆ U) :
    Y ⟶ openOver R X U := by
  let q : Y.left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι f.left (by rw [Scheme.Opens.range_ι]; exact hf)
  exact Over.homMk q (by
    change q ≫ (U.ι ≫ X.hom) = Y.hom
    calc
      _ = (q ≫ U.ι) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = f.left ≫ X.hom := congrArg (fun g : Y.left ⟶ X.left => g ≫ X.hom)
        (IsOpenImmersion.lift_fac U.ι f.left _)
      _ = _ := Over.w f)

@[simp] theorem relativeOpenLift_fac {Y X : Over (Spec (CommRingCat.of R))}
    (f : Y ⟶ X) (U : X.left.Opens) (hf : Set.range f.left ⊆ U) :
    relativeOpenLift R f U hf ≫ openOverι R X U = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac U.ι f.left _

variable (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S]
variable [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]

/-- A map from an affine source to any scheme is continuous on actual points. -/
theorem continuous_affineToSchemePointMap
    {Y X : Over (Spec (CommRingCat.of R))} [IsAffine Y.left] (f : Y ⟶ X) :
    Continuous[inferInstance, schemePointTopology R X S]
      (fun p : RingPoint R Y S => (p ≫ f : RingPoint R X S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  change Continuous (X := RingPoint R Y S) (Y := RingPoint R X S)
    (fun p => p ≫ f)
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨V, hV, hpV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := f.left (p.left (IsLocalRing.closedPoint S))) (U := ⊤) (by trivial)
  let : IsAffine V := hV
  have hpPre : p.left (IsLocalRing.closedPoint S) ∈ f.left ⁻¹ᵁ V := hpV
  obtain ⟨D, hD, hpD, hDPre⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := p.left (IsLocalRing.closedPoint S))
    (U := f.left ⁻¹ᵁ V) hpPre
  let : IsAffine D := hD
  let a : openOver R Y D ⟶ X := openOverι R Y D ≫ f
  have ha : Set.range a.left ⊆ V := by
    rintro z ⟨d, rfl⟩
    exact hDPre d.property
  let F : openOver R Y D ⟶ openOver R X V := relativeOpenLift R a V ha
  have hF : F ≫ openOverι R X V = openOverι R Y D ≫ f :=
    relativeOpenLift_fac R a V ha
  let g : RingPoint R Y S → RingPoint R X S := fun q => q ≫ f
  let k : RingPoint R (openOver R Y D) S → RingPoint R (openOver R X V) S :=
    fun q => q ≫ F
  have hk : Continuous k := continuous_affineSchemePointMap R S F
  have hcV : Continuous (X := RingPoint R (openOver R X V) S) (Y := RingPoint R X S)
      (openPointMap R X S V) :=
    schemePointTopology_continuous_chart R X S ⟨V, hV⟩
  have heq : g ∘ openPointMap R Y S D = openPointMap R X S V ∘ k := by
    funext q
    dsimp only [RingPoint] at q
    change (q ≫ openOverι R Y D) ≫ f = (q ≫ F) ≫ openOverι R X V
    exact (Category.assoc q _ _).trans
      ((congrArg (fun t => q ≫ t) hF.symm).trans (Category.assoc q _ _).symm)
  have hc : Continuous (g ∘ openPointMap R Y S D) := by
    rw [heq]
    exact hcV.comp hk
  have hr : Set.range p.left ⊆ D :=
    (range_subset_open_iff_closedPoint R Y S D p).mpr hpD
  let q := openPointLift R Y S D p hr
  have hq : openPointMap R Y S D q = p := openPointMap_lift R Y S D p hr
  have ht := (isOpenEmbedding_affineOpenPointMap R Y S D).continuousAt_iff.mp
    (hc.continuousAt (x := q))
  rw [hq] at ht
  exact ht

/-- Actual postcomposition is continuous between the final point topologies. -/
theorem schemePointContinuity_proof : SchemePointContinuityProperty R S := by
  intro X Y f
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  change Continuous (X := RingPoint R X S) (Y := RingPoint R Y S)
    (fun p => p ≫ f)
  refine ⟨?_⟩
  intro W hW
  apply (schemePointTopology_isOpen_iff R X S _).mpr
  intro U
  let : IsAffine (openOver R X U.val).left := U.property
  have hc := continuous_affineToSchemePointMap R S (openOverι R X U.val ≫ f)
  have heq : (fun p : RingPoint R (openOver R X U.val) S =>
      ((p ≫ openOverι R X U.val) ≫ f : RingPoint R Y S)) =
      (fun p : RingPoint R (openOver R X U.val) S => p ≫ (openOverι R X U.val ≫ f)) := by
    funext p
    dsimp only [RingPoint] at p
    exact Category.assoc _ _ _
  change IsOpen ((fun p : RingPoint R (openOver R X U.val) S =>
    ((p ≫ openOverι R X U.val) ≫ f : RingPoint R Y S)) ⁻¹' W)
  rw [heq]
  exact hc.isOpen_preimage W hW

/-- An open-subscheme inclusion is open for the final scheme-point topologies. -/
theorem isOpenMap_schemeOpenPointMap
    (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens) :
    letI : TopologicalSpace (RingPoint R (openOver R X U) S) :=
      schemePointTopology R (openOver R X U) S
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    IsOpenMap (openPointMap R X S U) := by
  let : TopologicalSpace (RingPoint R (openOver R X U) S) :=
    schemePointTopology R (openOver R X U) S
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  intro W hW
  apply (schemePointTopology_isOpen_iff R X S _).mpr
  intro V
  let : IsAffine (openOver R X V.val).left := V.property
  apply isOpen_iff_forall_mem_open.mpr
  intro q hq
  obtain ⟨p, hpW, hpq⟩ := hq
  have hpoint : (openPointMap R X S U p).left (IsLocalRing.closedPoint S) =
      (openPointMap R X S V.val q).left (IsLocalRing.closedPoint S) :=
    congrArg (fun z : RingPoint R X S => z.left (IsLocalRing.closedPoint S)) hpq
  have hxU : q.left (IsLocalRing.closedPoint S) ∈ (openOverι R X V.val).left ⁻¹ᵁ U := by
    have hpU : (openPointMap R X S U p).left (IsLocalRing.closedPoint S) ∈ U :=
      (p.left (IsLocalRing.closedPoint S)).property
    change (openPointMap R X S V.val q).left (IsLocalRing.closedPoint S) ∈ U
    exact hpoint ▸ hpU
  obtain ⟨B, hB, hqB, hBU⟩ := exists_isAffineOpen_mem_and_subset
    (X := (openOver R X V.val).left) (x := q.left (IsLocalRing.closedPoint S))
    (U := (openOverι R X V.val).left ⁻¹ᵁ U) hxU
  let : IsAffine B := hB
  let a : openOver R (openOver R X V.val) B ⟶ X :=
    openOverι R (openOver R X V.val) B ≫ openOverι R X V.val
  have ha : Set.range a.left ⊆ U := by
    rintro z ⟨b, rfl⟩
    exact hBU b.property
  let F : openOver R (openOver R X V.val) B ⟶ openOver R X U :=
    relativeOpenLift R a U ha
  have hF : F ≫ openOverι R X U = a := relativeOpenLift_fac R a U ha
  let k : RingPoint R (openOver R (openOver R X V.val) B) S →
      RingPoint R (openOver R X U) S := fun r => r ≫ F
  have hk : Continuous k := continuous_affineToSchemePointMap R S F
  have hfg : openPointMap R X S U ∘ k =
      openPointMap R X S V.val ∘ openPointMap R (openOver R X V.val) S B := by
    funext r
    dsimp only [RingPoint] at r
    change (r ≫ F) ≫ openOverι R X U =
      (r ≫ openOverι R (openOver R X V.val) B) ≫ openOverι R X V.val
    exact (Category.assoc r _ _).trans
      ((congrArg (fun t => r ≫ t) hF).trans (Category.assoc r _ _).symm)
  have hr : Set.range q.left ⊆ B :=
    (range_subset_open_iff_closedPoint R (openOver R X V.val) S B q).mpr hqB
  let r := openPointLift R (openOver R X V.val) S B q hr
  have hrq : openPointMap R (openOver R X V.val) S B r = q :=
    openPointMap_lift R (openOver R X V.val) S B q hr
  have hkr : k r = p := (openPointMap_injective R X S U)
    ((congrFun hfg r).trans
      ((congrArg (openPointMap R X S V.val) hrq).trans hpq.symm))
  refine ⟨openPointMap R (openOver R X V.val) S B '' (k ⁻¹' W), ?_, ?_, ?_⟩
  · rintro z ⟨t, htW, rfl⟩
    exact ⟨k t, htW, congrFun hfg t⟩
  · exact (isOpenEmbedding_affineOpenPointMap R (openOver R X V.val) S B).isOpenMap _
      (hW.preimage hk)
  · exact ⟨r, by change k r ∈ W; rw [hkr]; exact hpW, hrq⟩

/-- The arbitrary-open part of the actual point gluing theorem. -/
theorem schemeOpenPoint_proof : SchemeOpenPointProperty R S := by
  intro X U
  let : TopologicalSpace (RingPoint R (openOver R X U) S) :=
    schemePointTopology R (openOver R X U) S
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨schemePointContinuity_proof R S _ _ (openOverι R X U),
    openPointMap_injective R X S U, isOpenMap_schemeOpenPointMap R S X U⟩

/-- The affine evaluation topology on a chart maps as an open subspace of the
final scheme-point topology. -/
theorem isOpenEmbedding_schemeAffineChart
    (X : Over (Spec (CommRingCat.of R))) (U : X.left.affineOpens) :
    letI : IsAffine (openOver R X U.val).left := U.property
    @IsOpenEmbedding (RingPoint R (openOver R X U.val) S) (RingPoint R X S)
      inferInstance (schemePointTopology R X S) (openPointMap R X S U.val) := by
  let : IsAffine (openOver R X U.val).left := U.property
  have h := schemeOpenPoint_proof R S X U.val
  change @IsOpenEmbedding (RingPoint R (openOver R X U.val) S) (RingPoint R X S)
    (schemePointTopology R (openOver R X U.val) S) (schemePointTopology R X S)
    (openPointMap R X S U.val) at h
  rw [schemePointTopology_eq_affine R (openOver R X U.val) S] at h
  exact h

/-- The grouped open-chart and functoriality target on actual scheme points. -/
theorem schemeOpenPointProperties_proof
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] :
    SchemeOpenPointProperties R S := by
  refine ⟨?_, schemeOpenPoint_proof R S, schemePointContinuity_proof R S⟩
  intro X _ U _
  exact isOpenEmbedding_affineOpenPointMap R X S U

end Langlands.AlgebraicGeometry.PointTopology
