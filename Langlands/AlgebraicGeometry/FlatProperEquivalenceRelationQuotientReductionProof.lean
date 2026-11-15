import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement
import Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Quotient
import Langlands.AlgebraicGeometry.HQuasiProjectiveDisjointUnion
import Langlands.AlgebraicGeometry.ProjectiveSpace.FlatStructure
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement

/-! # Effective quotients by flat proper equivalence relations from the Hilbert scheme

This file proves `FlatProperEquivalenceRelationQuotientReductionStatement`: the Hilbert scheme
statement `HilbertSchemeUniversalFamilyStatement` implies
`FlatProperEquivalenceRelationQuotientStatement`. This is Nitsure, *Construction of Hilbert
and Quot schemes*, Theorem 6.8.

Let `Z` be H-quasi-projective over a noetherian ring `A`, with a quasi-compact immersion
`i : Z ⟶ P = ℙⁿ_A`. The Hilbert scheme `H` of `P ⟶ Spec A` classifies the family
`R ⟶ P ×_A Z`, `r ↦ (i (t r), s r)`, by a morphism `φ : Z ⟶ H`. The quotient `Q` is the
scheme-theoretic image of `φ` in the open locus of `H` constructed in
`Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Quotient`. It is H-quasi-projective over
`Spec A`, because it is quasi-compact and immerses into `H`, which is a disjoint union of
H-projective opens.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.FlatEquivalenceRelation

open _root_.AlgebraicGeometry

/-- A morphism locally of finite type into a locally noetherian scheme is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp
    (HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› U V e)

/-- A scheme admitting a surjective morphism from a quasi-compact scheme is quasi-compact. -/
theorem compactSpace_of_surjective {X Y : Scheme.{u}} [CompactSpace X] (g : X ⟶ Y)
    [Surjective g] : CompactSpace Y := by
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr g.surjective]
  exact isCompact_range g.continuous

/-- **Nitsure, Theorem 6.8, from the Hilbert scheme.** The Hilbert scheme statement
`HilbertSchemeUniversalFamilyStatement` yields effective H-quasi-projective quotients by flat
proper equivalence relations on H-quasi-projective schemes over noetherian rings. -/
theorem flatProperEquivalenceRelationQuotient_of_hilbertScheme :
    FlatProperEquivalenceRelationQuotientReductionStatement.{u} := by
  intro HGP A _ _ Z R p s t h hqp hmono hEq hflat hprop
  have hZc : CompactSpace Z := hqp.compactSpace
  obtain ⟨n, i, hi_imm, hi_qc, hi⟩ := hqp
  -- the Hilbert scheme of `ℙⁿ_A`, embedded in itself by the identity
  obtain ⟨𝓛, h𝓛, h𝓛s⟩ :=
    (Picard.exists_closedImmersionBySections_iff_isHProjective (projectiveSpaceToSpec A n)).mpr
      ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨H, πH, W, -, hsep, hfam, U, hUdisj, hUcov, hU⟩ :=
    HGP A (projectiveSpaceToSpec A n) 𝓛 inferInstance inferInstance h𝓛 h𝓛s
  let C : Classifier (projectiveSpaceToSpec A n) :=
    ⟨H, πH, W, fun T sT g hg => (hfam T sT).1 g hg, fun T sT I => (hfam T sT).2 I⟩
  have : IsSeparated C.πH := hsep
  have : IsImmersion i := hi_imm
  have : QuasiCompact i := hi_qc
  have : QuasiCompact p := by rw [← hi]; infer_instance
  have : LocallyOfFiniteType p := by rw [← hi]; infer_instance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : LocallyOfFinitePresentation s := locallyOfFinitePresentation_of_locallyOfFiniteType s
  have : IsClosedImmersion (family s t i hi h) := isClosedImmersion_family s t i hi h
  -- the classifying morphism of the family `R ⟶ ℙⁿ_A ×_A Z`
  obtain ⟨φ, ⟨hφ, hW⟩, -⟩ := C.unique Z p (family s t i hi h).ker
    (flat_ker_family s t i hi h) (locallyOfFinitePresentation_ker_family s t i hi h)
  have hEq' : ∀ T : Scheme.{u}, Equivalence (@Rel R Z s t T) := hEq
  have := surjective_π C hEq' hW
  have : CompactSpace (Q C hEq' hW) := compactSpace_of_surjective (π C hEq' hW)
  refine ⟨Q C hEq' hW, (ιQ C hEq' hW ≫ (C.locus i.coborderRange).ι) ≫ C.πH, π C hEq' hW,
    ?_, ?_, flat_π C hEq' hW, surjective_π C hEq' hW, isProper_π C hEq' hW,
    locallyOfFinitePresentation_π C hEq' hW, isPullback_s_t C hEq' hW⟩
  · exact isHQuasiProjective_of_isImmersion_of_disjoint_cover _ C.πH U hUdisj hUcov
      fun θ => (hU θ).1
  · calc π C hEq' hW ≫ (ιQ C hEq' hW ≫ (C.locus i.coborderRange).ι) ≫ C.πH
        = (π C hEq' hW ≫ ιQ C hEq' hW ≫ (C.locus i.coborderRange).ι) ≫ C.πH := by
          simp only [Category.assoc]
      _ = p := by rw [π_ι_ι]; exact hφ

end Langlands.AlgebraicGeometry.FlatEquivalenceRelation
