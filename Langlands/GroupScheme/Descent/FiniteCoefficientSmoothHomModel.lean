import Langlands.GroupScheme.Descent.FiniteCoefficientReductiveModel

/-! # Smooth affine simultaneous models of group homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

private theorem smoothModel_fg_tower {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : Subalgebra R A) (U : Subalgebra T A) (hT : T.FG) (hU : U.FG) :
    (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem smoothModel_spec_comp (R B A : Type u) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- A simultaneous model in which both groups are smooth and affine. -/
structure SmoothAffineHomModel (f : G ⟶ H) extends SimultaneousHomModel R A f where
  targetAffine : IsAffineHom target.X.hom
  targetSmooth : Smooth target.X.hom

variable {R A}

/-- Both smooth affine structures survive enlargement along actual inclusions. -/
def SmoothAffineHomModel.enlargeTo {f : G ⟶ H} (D : SmoothAffineHomModel R A f)
    (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C) :
    SmoothAffineHomModel R A f where
  toSimultaneousHomModel := D.toSimultaneousHomModel.enlargeTo C hC hDC
  targetAffine := by
    let := D.targetAffine
    change IsAffineHom (pullback.snd D.target.X.hom _)
    infer_instance
  targetSmooth := by
    let := D.targetSmooth
    change Smooth (pullback.snd D.target.X.hom _)
    infer_instance

/-- Supplied homomorphism descent combines two smooth affine group models. -/
theorem exists_smoothAffineHomModel (hHom : HomGeneralStatement.{u})
    (f : G ⟶ H) [IsAffine G.X.left] [Smooth G.X.hom]
    [IsAffine H.X.left] [Smooth H.X.hom] (s : Finset A) :
    ∃ D : SmoothAffineHomModel R A f, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨DG, hs⟩ := exists_groupModel R A G s
  obtain ⟨DH, -⟩ := exists_groupModel DG.coefficients A H ∅
  let U := DH.coefficients
  have hU : (U.restrictScalars R).FG :=
    smoothModel_fg_tower DG.coefficients DH.coefficients DG.finite DH.finite
  let G₀ := (baseChange (Spec.algebraMap DG.coefficients U)).obj DG.group
  let eG : G ≅ (baseChange (Spec.algebraMap U A)).obj G₀ :=
    DG.iso ≪≫ (pullbackComparison (Spec.algebraMap DG.coefficients U)
      (Spec.algebraMap U A) (Spec.algebraMap DG.coefficients A)
      (smoothModel_spec_comp DG.coefficients U A) DG.group).symm
  let eH : H ≅ (baseChange (Spec.algebraMap U A)).obj DH.group := DH.iso
  let := DG.affine
  let := DG.smooth
  let := DH.affine
  let := DH.smooth
  have hGaff : IsAffineHom G₀.X.hom := by
    change IsAffineHom (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  have hGsm : Smooth G₀.X.hom := by
    change Smooth (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  let := hGaff
  let := hGsm
  obtain ⟨T, hT, -, g, hg⟩ := hHom U A G₀ DH.group (eG.inv ≫ f ≫ eH.hom) ∅
  let cG := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (smoothModel_spec_comp U T A) G₀
  let cH := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (smoothModel_spec_comp U T A) DH.group
  let D : SmoothAffineHomModel R A f :=
    { coefficients := T.restrictScalars R
      finite := smoothModel_fg_tower (U.restrictScalars R) T hU hT
      source := (baseChange (Spec.algebraMap U T)).obj G₀
      target := (baseChange (Spec.algebraMap U T)).obj DH.group
      sourceAffine := by
        change IsAffineHom (pullback.snd G₀.X.hom (Spec.algebraMap U T))
        infer_instance
      sourceSmooth := by
        change Smooth (pullback.snd G₀.X.hom (Spec.algebraMap U T))
        infer_instance
      targetSeparated := by
        change IsSeparated (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetFinitePresentation := by
        change LocallyOfFinitePresentation (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetQuasiCompact := by
        change QuasiCompact (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetAffine := by
        change IsAffineHom (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetSmooth := by
        change Smooth (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      hom := g
      sourceIso := eG ≪≫ cG.symm
      targetIso := eH ≪≫ cH.symm
      comm := by
        change (eG ≪≫ cG.symm).hom ≫ (baseChange (Spec.algebraMap T A)).map g =
          f ≫ (eH ≪≫ cH.symm).hom
        apply (cancel_mono cH.hom).mp
        change (baseChange (Spec.algebraMap T A)).map g ≫ cH.hom =
          cG.hom ≫ (eG.inv ≫ f ≫ eH.hom) at hg
        have he := congrArg (fun k => eG.hom ≫ cG.inv ≫ k) hg
        simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
          Category.comp_id] using he }
  refine ⟨D, ?_⟩
  intro x hx
  have hxG : x ∈ DG.coefficients := hs hx
  have hxH : x ∈ DH.coefficients := DH.coefficients.algebraMap_mem ⟨x, hxG⟩
  exact T.algebraMap_mem ⟨x, hxH⟩

end Langlands.GroupScheme.Descent.FiniteCoefficient
