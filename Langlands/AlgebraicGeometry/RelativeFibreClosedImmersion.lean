import Langlands.AlgebraicGeometry.ProperFibreClosedImmersion

/-! # Closed immersion of proper maps detected on relative base fibres -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {X Y S X' Y' : Scheme.{u}}

/-- Surjectivity on stalks gives surjectivity on the actual residue fields. -/
lemma residueFieldMap_surjective_of_surjectiveOnStalks
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  have h : Function.Surjective (Y.residue (f x) ≫ f.residueFieldMap x) := by
    rw [Scheme.residue_residueFieldMap]
    exact (X.residue_surjective x).comp (f.stalkMap_surjective x)
  change Function.Surjective ((f.residueFieldMap x) ∘ (Y.residue (f x))) at h
  exact Function.Surjective.of_comp h

/-- The actual residue-field isomorphism induced by a morphism surjective on
stalks. -/
def residueFieldIsoOfSurjectiveOnStalks (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Y.residueField (f x) ≅ X.residueField x :=
  (RingEquiv.ofBijective (f.residueFieldMap x).hom
    ⟨(f.residueFieldMap x).hom.injective,
      residueFieldMap_surjective_of_surjectiveOnStalks f x⟩).toCommRingCatIso

@[simp]
lemma residueFieldIsoOfSurjectiveOnStalks_hom
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    (residueFieldIsoOfSurjectiveOnStalks f x).hom = f.residueFieldMap x := rfl

instance (priority := 100) isIso_residueFieldMap_of_surjectiveOnStalks
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    IsIso (f.residueFieldMap x) :=
  (residueFieldIsoOfSurjectiveOnStalks f x).isIso_hom

/-- Target residue-fibre closed immersion is invariant under a Cartesian
change with the same residue field at the point in question. -/
lemma fibreClosedImmersion_iff_of_isPullback_of_residueIso
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
    (h : IsPullback a f' f b) (y' : Y') [IsIso (b.residueFieldMap y')] :
    IsClosedImmersion (f'.fiberToSpecResidueField y') ↔
      IsClosedImmersion (f.fiberToSpecResidueField (b y')) := by
  have hs := isPullback_fiberToSpecResidueField_of_isPullback h y'
  let aF := pullback.map f' (Y'.fromSpecResidueField y')
    f (Y.fromSpecResidueField (b y')) a (Spec.map (b.residueFieldMap y')) b
    h.w.symm (by simp)
  have : IsIso (Spec.map (b.residueFieldMap y')) := inferInstance
  have : IsIso aF := hs.isIso_fst_of_isIso
  exact MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk' _ _ (asIso aF) (asIso (Spec.map (b.residueFieldMap y'))) hs.w)

/-- A proper morphism is a closed immersion exactly when the actual induced
morphisms on all residue fibres over any common base are closed immersions. -/
lemma isClosedImmersion_iff_relativeFibre_of_isProper
    (f : X ⟶ Y) (q : Y ⟶ S) [IsProper f] :
    IsClosedImmersion f ↔
      ∀ s : S, IsClosedImmersion (relativeFibreMap f q s) := by
  constructor
  · intro hf s
    exact MorphismProperty.of_isPullback (isPullback_relativeFibreMap f q s) hf
  intro H
  apply (isClosedImmersion_iff_fibre_of_isProper f).mpr
  intro y
  have hrel : IsClosedImmersion
      ((relativeFibreMap f q (q y)).fiberToSpecResidueField (q.asFiber y)) :=
    MorphismProperty.pullback_snd _ _ (H (q y))
  have h := (fibreClosedImmersion_iff_of_isPullback_of_residueIso
    (isPullback_relativeFibreMap f q (q y)) (q.asFiber y)).mp hrel
  exact Eq.mp (congrArg
    (fun z : Y ↦ IsClosedImmersion (f.fiberToSpecResidueField z))
    (q.fiberι_asFiber y)) h

end Langlands.AlgebraicGeometry
