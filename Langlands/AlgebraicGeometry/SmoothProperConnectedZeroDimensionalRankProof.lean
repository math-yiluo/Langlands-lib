import Langlands.AlgebraicGeometry.SmoothProperConnectedZeroDimensionalRankStatement
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Topology.Connected.Clopen

/-! # Native endomorphism rank in relative dimension zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

private theorem isOpenImmersion_section_of_etale {X S : Scheme.{u}}
    (p : X ⟶ S) [Etale p] (s : S ⟶ X) (hs : s ≫ p = 𝟙 S) :
    IsOpenImmersion s := by
  let : MorphismProperty.HasOfPostcompProperty
      @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      fun _ _ _ _ ↦ inferInstanceAs (IsOpenImmersion _)
  have : IsOpenImmersion (s ≫ p) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp @IsOpenImmersion (W' := @Etale) s p
    inferInstance inferInstance

/-- A connected separated etale scheme over a separably closed field is
isomorphic to that field's spectrum. -/
theorem isIso_of_connected_separated_etale {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    [Etale p] [IsSeparated p] [ConnectedSpace X] :
    IsIso p := by
  let x : X := Classical.choice inferInstance
  obtain ⟨s, hs, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p
    (𝟙 _) x (Subsingleton.elim _ _)
  have : IsOpenImmersion s := isOpenImmersion_section_of_etale p s hs
  have : IsClosedImmersion (s ≫ p) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s p
  have hrange : Set.range s = Set.univ :=
    (show IsClopen (Set.range s) from
      ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩).eq_univ
        (Set.range_nonempty s)
  have : Epi s.base := (TopCat.epi_iff_surjective _).mpr
    (Set.range_eq_univ.mp hrange)
  have : IsIso s := IsOpenImmersion.isIso s
  have : IsIso (s ≫ p) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s p

/-- The complete native rank-one statement in relative dimension zero. -/
theorem smoothProperConnectedZeroDimensionalRank :
    SmoothProperConnectedZeroDimensionalRankStatement.{u} := by
  intro K _ _ X hs hp hc
  let := hs
  let := hp
  let := hc
  have : Etale X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).mpr hs
  have : ConnectedSpace X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton X.hom
  have : IsIso X.hom := isIso_of_connected_separated_etale X.hom
  refine ⟨inferInstance, fun f ↦ ?_⟩
  have hf : f.left = 𝟙 X.left := by
    apply (cancel_mono X.hom).mp
    simp
  refine ⟨hf, fun x ↦ ?_⟩
  rw [hf]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X.left)) x

end Langlands.AlgebraicGeometry
