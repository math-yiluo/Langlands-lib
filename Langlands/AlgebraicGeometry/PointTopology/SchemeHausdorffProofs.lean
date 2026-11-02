import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Langlands.AlgebraicGeometry.PointTopology.SchemeHausdorffStatements

/-! # Hausdorffness of actual points of separated schemes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]
variable [T2Space S]

/-- The actual final point topology of a separated relative scheme is Hausdorff. -/
theorem t2Space_schemePointTopology
    (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom] :
    @T2Space (RingPoint R X S) (schemePointTopology R X S) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let B : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let e : X ⟶ B := Over.homMk X.hom (Category.comp_id X.hom)
  let c := relativeSchemePullback R e e
  let hc := relativeSchemePullbackIsLimit R e e
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  let δ : X ⟶ c.pt := Over.homMk (pullback.diagonal X.hom) (by
    change pullback.diagonal X.hom ≫
      (pullback.fst X.hom X.hom ≫ X.hom) = X.hom
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp])
  let : IsClosedImmersion δ.left :=
    inferInstanceAs (IsClosedImmersion (pullback.diagonal X.hom))
  have hδfst : δ ≫ c.fst = 𝟙 X := by
    apply Over.OverMorphism.ext
    exact pullback.diagonal_fst X.hom
  have hδsnd : δ ≫ c.snd = 𝟙 X := by
    apply Over.OverMorphism.ext
    exact pullback.diagonal_snd X.hom
  have hbase (p q : RingPoint R X S) : p ≫ e = q ≫ e := by
    apply Over.OverMorphism.ext
    exact (Over.w p).trans (Over.w q).symm
  let η : RingPoint R X S × RingPoint R X S →
      {q : RingPoint R X S × RingPoint R X S // q.1 ≫ e = q.2 ≫ e} :=
    fun q => ⟨q, hbase q.1 q.2⟩
  have hη : Continuous η := continuous_id.subtype_mk _
  let H := schemePullbackPointHomeomorph R S c hc
  have hdiag (p : RingPoint R X S) : H (p ≫ δ) = η (p, p) := by
    apply Subtype.ext
    apply Prod.ext
    · change (p ≫ δ) ≫ c.fst = p
      exact (Category.assoc p δ c.fst).trans
        ((congrArg (fun t : X ⟶ X => p ≫ t) hδfst).trans (Category.comp_id p))
    · change (p ≫ δ) ≫ c.snd = p
      exact (Category.assoc p δ c.snd).trans
        ((congrArg (fun t : X ⟶ X => p ≫ t) hδsnd).trans (Category.comp_id p))
  let j := H.symm ∘ η
  have hj : Continuous j := H.symm.continuous.comp hη
  have hclosed := (isClosedEmbedding_schemeClosedPointMap R S δ).isClosed_range.preimage hj
  have hrange : j ⁻¹' Set.range
      (fun p : RingPoint R X S => (p ≫ δ : RingPoint R c.pt S)) =
      Set.diagonal (RingPoint R X S) := by
    ext q
    constructor
    · rintro ⟨p, hp⟩
      have hpq : (p, p) = q := congrArg Subtype.val
        ((hdiag p).symm.trans ((congrArg H hp).trans (H.apply_symm_apply (η q))))
      exact (congrArg Prod.fst hpq).symm.trans (congrArg Prod.snd hpq)
    · intro hq
      change q.1 = q.2 at hq
      refine ⟨q.1, ?_⟩
      apply H.injective
      exact (hdiag q.1).trans ((congrArg η
        (show (q.1, q.1) = q from Prod.ext rfl hq)).trans
        (H.apply_symm_apply (η q)).symm)
  exact t2_iff_isClosed_diagonal.mpr (hrange ▸ hclosed)

/-- The exact proposition-valued Hausdorff target. -/
theorem schemePointHausdorff_proof : SchemePointHausdorffProperty R S := by
  intro X _
  exact t2Space_schemePointTopology R S X

end Langlands.AlgebraicGeometry.PointTopology
