import Langlands.AlgebraicGeometry.RelationEtaleSliceGlobalizationStatement

/-! # Globalizing local slices of a scheme relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A point closed in an open subscheme has a locally finite type residue-field morphism
into the ambient scheme. -/
theorem locallyOfFiniteType_residueField_of_closed_in_open
    {V U : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
    (x : V) (hx : IsClosed ({x} : Set V)) :
    LocallyOfFiniteType (U.fromSpecResidueField (i x)) := by
  have : IsClosedImmersion (V.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have H : LocallyOfFiniteType (V.fromSpecResidueField x ≫ i) := inferInstance
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at H
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @LocallyOfFiniteType) (Spec.map (i.residueFieldMap x))
      (U.fromSpecResidueField (i x))).mp H

/-- An open subset containing every finite type point of a scheme is the whole scheme. -/
theorem isOpen_eq_univ_of_contains_finiteTypePoints
    (U : Scheme.{u}) (W : Set U) (hW : IsOpen W)
    (hpoints : ∀ x : U, LocallyOfFiniteType (U.fromSpecResidueField x) → x ∈ W) :
    W = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  obtain ⟨j, y, hy⟩ := U.affineCover.exists_eq x
  have HC : IsClosed ((U.affineCover.f j) ⁻¹' W)ᶜ :=
    (hW.preimage (U.affineCover.f j).continuous).isClosed_compl
  obtain ⟨z, hz, hclosed⟩ := HC.exists_closed_singleton
    ⟨y, by change U.affineCover.f j y ∉ W; simpa only [hy] using hx⟩
  exact hz (hpoints _
    (locallyOfFiniteType_residueField_of_closed_in_open (U.affineCover.f j) z hclosed))

set_option backward.isDefEq.respectTransparency false in
/-- Local etale slices meeting every finite type point assemble to an etale surjective
slice. No equivalence-relation hypothesis is needed for this globalization step. -/
theorem exists_etale_surjective_slice_of_finiteTypePoint_slices
    {U R : Scheme.{u}} (t s : R ⟶ U)
    (H : ∀ x : U, LocallyOfFiniteType (U.fromSpecResidueField x) →
      ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
        Etale (pullback.snd g t ≫ s) ∧ x ∈ Set.range (pullback.snd g t ≫ s)) :
    ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
      Etale (pullback.snd g t ≫ s) ∧ Surjective (pullback.snd g t ≫ s) := by
  classical
  let I := {x : U // LocallyOfFiniteType (U.fromSpecResidueField x)}
  choose V g hg he hx using fun x : I ↦ H x.1 x.2
  let G : (∐ V) ⟶ U := Sigma.desc g
  have hG : LocallyOfFiniteType G :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) hg
  have hE : Etale (pullback.snd G t ≫ s) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale)
      ((sigmaOpenCover V).pullback₂ (pullback.fst G t))
    intro i
    change Etale (pullback.snd (Sigma.ι V i) (pullback.fst G t) ≫
      (pullback.snd G t ≫ s))
    rw [← pullbackRightPullbackFstIso_hom_snd_assoc]
    have : Etale (pullback.snd (Sigma.ι V i ≫ G) t ≫ s) := by
      dsimp only [G]
      rw [Sigma.ι_comp_desc]
      exact he i
    infer_instance
  have hRange : Set.range (pullback.snd G t ≫ s) = Set.univ := by
    apply isOpen_eq_univ_of_contains_finiteTypePoints U _
      (pullback.snd G t ≫ s).isOpenMap.isOpen_range
    intro x hfin
    let i : I := ⟨x, hfin⟩
    obtain ⟨z, hz⟩ := hx i
    let k : pullback (g i) t ⟶ pullback G t :=
      pullback.map (g i) t G t (Sigma.ι V i) (𝟙 R) (𝟙 U)
        (by simp [G]) (by simp)
    refine ⟨k z, ?_⟩
    change (k ≫ (pullback.snd G t ≫ s)) z = x
    simpa [k] using hz
  exact ⟨∐ V, G, hG, hE, ⟨Set.range_eq_univ.mp hRange⟩⟩

/-- Globalization of local slices meeting every finite type point. -/
theorem relationEtaleSliceGlobalization : RelationEtaleSliceGlobalizationStatement.{u} := by
  intro U R t s H
  exact exists_etale_surjective_slice_of_finiteTypePoint_slices t s H

end Langlands.AlgebraicGeometry
