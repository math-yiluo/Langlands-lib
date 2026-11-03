import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-! # Gluing the topology comparison for actual scheme base change -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
variable [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]

/-- Base change preserves the actual open chart maps. -/
theorem isOpenImmersion_ringBaseChangeMap
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    [IsOpenImmersion f.left] :
    IsOpenImmersion ((Over.pullback (Spec.algebraMap C D)).map f).left := by
  have heq : ((Over.pullback (Spec.algebraMap C D)).map f).left =
      pullback.map X.hom (Spec.algebraMap C D) Y.hom (Spec.algebraMap C D)
        f.left (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using (Over.w f).symm)
        (by simp) := by
    simp only [Over.pullback_map_left, pullback.map, Category.comp_id]
  rw [heq]
  infer_instance

variable [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A] [IsOpenUnits A]

/-- The actual adjunction equivalence is continuous, tested on affine source charts. -/
theorem continuous_schemePointBaseChangeEquiv
    (X : Over (Spec (CommRingCat.of C))) :
    Continuous[schemePointTopology C X A,
      schemePointTopology D (ringBaseChange C D X) A]
      (ringPointBaseChangeEquiv C D A X) := by
  let : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
  let : TopologicalSpace (RingPoint D (ringBaseChange C D X) A) :=
    schemePointTopology D (ringBaseChange C D X) A
  refine ⟨?_⟩
  intro W hW
  apply (schemePointTopology_isOpen_iff C X A _).mpr
  intro U
  let : IsAffine (openOver C X U.val).left := U.property
  let f : ringBaseChange C D (openOver C X U.val) ⟶ ringBaseChange C D X :=
    (Over.pullback (Spec.algebraMap C D)).map (openOverι C X U.val)
  have hc := (continuous_affineToSchemePointMap D A f).comp
    (isHomeomorph_ringPointBaseChangeEquiv C D A (openOver C X U.val)).continuous
  have heq : ringPointBaseChangeEquiv C D A X ∘ openPointMap C X A U.val =
      (fun p => p ≫ f) ∘ ringPointBaseChangeEquiv C D A (openOver C X U.val) := by
    funext p
    exact ringPointBaseChangeEquiv_natural C D A (openOverι C X U.val) p
  change IsOpen ((ringPointBaseChangeEquiv C D A X ∘
    openPointMap C X A U.val) ⁻¹' W)
  rw [heq]
  exact hc.isOpen_preimage W hW

/-- Images of opens are unions of open images through base-changed affine charts. -/
theorem isOpenMap_schemePointBaseChangeEquiv
    (X : Over (Spec (CommRingCat.of C))) :
    letI : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
    letI : TopologicalSpace (RingPoint D (ringBaseChange C D X) A) :=
      schemePointTopology D (ringBaseChange C D X) A
    IsOpenMap (ringPointBaseChangeEquiv C D A X) := by
  let : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
  let : TopologicalSpace (RingPoint D (ringBaseChange C D X) A) :=
    schemePointTopology D (ringBaseChange C D X) A
  intro W hW
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨p, hpW, rfl⟩
  obtain ⟨U, q, hq⟩ := exists_affineOpenPoint C X A p
  let : IsAffine (openOver C X U.val).left := U.property
  let f : ringBaseChange C D (openOver C X U.val) ⟶ ringBaseChange C D X :=
    (Over.pullback (Spec.algebraMap C D)).map (openOverι C X U.val)
  let g := ringPointBaseChangeEquiv C D A (openOver C X U.val)
  let k : RingPoint D (ringBaseChange C D (openOver C X U.val)) A →
      RingPoint D (ringBaseChange C D X) A := fun r => r ≫ f
  let : IsOpenImmersion (openOverι C X U.val).left :=
    inferInstanceAs (IsOpenImmersion U.val.ι)
  have hf : IsOpenImmersion f.left :=
    isOpenImmersion_ringBaseChangeMap C D (openOverι C X U.val)
  have hk : IsOpenEmbedding k := by
    have h := isOpenEmbedding_schemePointMap D A f
    change @IsOpenEmbedding (RingPoint D (ringBaseChange C D (openOver C X U.val)) A)
      (RingPoint D (ringBaseChange C D X) A)
      (schemePointTopology D (ringBaseChange C D (openOver C X U.val)) A)
      (schemePointTopology D (ringBaseChange C D X) A) k at h
    rw [schemePointTopology_eq_affine] at h
    exact h
  let V := openPointMap C X A U.val ⁻¹' W
  have hV : IsOpen V := (schemePointTopology_isOpen_iff C X A W).mp hW U
  let B := k '' (g '' V)
  refine ⟨B, ?_, ?_, ?_⟩
  · rintro z ⟨r, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨openPointMap C X A U.val s, hs, ?_⟩
    exact ringPointBaseChangeEquiv_natural C D A (openOverι C X U.val) s
  · exact hk.isOpenMap _
      ((isHomeomorph_ringPointBaseChangeEquiv C D A (openOver C X U.val)).isOpenMap V hV)
  · refine ⟨g q, ⟨q, ?_, rfl⟩, ?_⟩
    · change openPointMap C X A U.val q ∈ W
      rw [hq]
      exact hpW
    · exact (ringPointBaseChangeEquiv_natural C D A (openOverι C X U.val) q).symm.trans
        (congrArg (ringPointBaseChangeEquiv C D A X) hq)

/-- The independently constructed final topologies agree under actual base change. -/
theorem schemeBaseChangeTopology_proof : SchemeBaseChangeTopologyProperty C D A := by
  intro X
  let : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
  let : TopologicalSpace (RingPoint D (ringBaseChange C D X) A) :=
    schemePointTopology D (ringBaseChange C D X) A
  exact ⟨continuous_schemePointBaseChangeEquiv C D A X,
    isOpenMap_schemePointBaseChangeEquiv C D A X,
    (ringPointBaseChangeEquiv C D A X).bijective⟩

end Langlands.AlgebraicGeometry.PointTopology
