import Langlands.GroupScheme.Descent.FiniteCoefficientGroup
import Langlands.GroupScheme.Descent.FiniteCoefficientSeparatedGroup
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneralStatement
import Langlands.AlgebraicGeometry.FiniteCoefficientMonomorphismStatement

/-! # Simultaneous finite coefficient models of group homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

private theorem model_fg_tower {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : Subalgebra R A) (U : Subalgebra T A) (hT : T.FG) (hU : U.FG) :
    (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem model_spec_comp (R B A : Type u) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- Actual source, target, and homomorphism over one finite coefficient algebra,
with geometric properties and a commuting recovery square. -/
structure SimultaneousHomModel (f : G ⟶ H) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  source : GroupScheme (Spec (CommRingCat.of coefficients))
  target : GroupScheme (Spec (CommRingCat.of coefficients))
  sourceAffine : IsAffineHom source.X.hom
  sourceSmooth : Smooth source.X.hom
  targetSeparated : IsSeparated target.X.hom
  targetFinitePresentation : LocallyOfFinitePresentation target.X.hom
  targetQuasiCompact : QuasiCompact target.X.hom
  hom : source ⟶ target
  sourceIso : G ≅ (baseChange (Spec.algebraMap coefficients A)).obj source
  targetIso : H ≅ (baseChange (Spec.algebraMap coefficients A)).obj target
  comm : sourceIso.hom ≫ (baseChange (Spec.algebraMap coefficients A)).map hom =
    f ≫ targetIso.hom

variable {R A}

/-- Enlarge a simultaneous model while retaining exact recovery. -/
def SimultaneousHomModel.enlarge {f : G ⟶ H} (D : SimultaneousHomModel R A f)
    (T : Subalgebra D.coefficients A) (hT : T.FG) : SimultaneousHomModel R A f where
  coefficients := T.restrictScalars R
  finite := model_fg_tower D.coefficients T D.finite hT
  source := (baseChange (Spec.algebraMap D.coefficients T)).obj D.source
  target := (baseChange (Spec.algebraMap D.coefficients T)).obj D.target
  sourceAffine := by
    let := D.sourceAffine
    change IsAffineHom (pullback.snd D.source.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  sourceSmooth := by
    let := D.sourceSmooth
    change Smooth (pullback.snd D.source.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetSeparated := by
    let := D.targetSeparated
    change IsSeparated (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetFinitePresentation := by
    let := D.targetFinitePresentation
    change LocallyOfFinitePresentation
      (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetQuasiCompact := by
    let := D.targetQuasiCompact
    change QuasiCompact (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  hom := (baseChange (Spec.algebraMap D.coefficients T)).map D.hom
  sourceIso := D.sourceIso ≪≫
    (pullbackComparison (Spec.algebraMap D.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap D.coefficients A) (model_spec_comp D.coefficients T A) D.source).symm
  targetIso := D.targetIso ≪≫
    (pullbackComparison (Spec.algebraMap D.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap D.coefficients A) (model_spec_comp D.coefficients T A) D.target).symm
  comm := by
    let cG := pullbackComparison (Spec.algebraMap D.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap D.coefficients A)
      (model_spec_comp D.coefficients T A) D.source
    let cH := pullbackComparison (Spec.algebraMap D.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap D.coefficients A)
      (model_spec_comp D.coefficients T A) D.target
    change (D.sourceIso ≪≫ cG.symm).hom ≫
        (baseChange (Spec.algebraMap T A)).map
          ((baseChange (Spec.algebraMap D.coefficients T)).map D.hom) =
      f ≫ (D.targetIso ≪≫ cH.symm).hom
    apply (cancel_mono cH.hom).mp
    have hn : (baseChange (Spec.algebraMap T A)).map
        ((baseChange (Spec.algebraMap D.coefficients T)).map D.hom) ≫ cH.hom =
        cG.hom ≫ (baseChange (Spec.algebraMap D.coefficients A)).map D.hom :=
      pullbackComparison_naturality _ _ _ _ D.hom
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hn,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact D.comm

/-- Monicity over the supplied algebra follows from the exact recovery square. -/
theorem SimultaneousHomModel.mono_over_algebra {f : G ⟶ H} (D : SimultaneousHomModel R A f)
    [Mono f.hom.hom.left] :
    Mono ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom).hom.hom.left := by
  have he : (baseChange (Spec.algebraMap D.coefficients A)).map D.hom =
      D.sourceIso.inv ≫ f ≫ D.targetIso.hom := by
    rw [← D.comm, Iso.inv_hom_id_assoc]
  rw [he]
  change Mono (D.sourceIso.inv.hom.hom.left ≫ f.hom.hom.left ≫
    D.targetIso.hom.hom.hom.left)
  infer_instance

/-- Homomorphism descent combines the separate source and target models into
one model over finite coefficients. -/
theorem exists_homModel (hHom : HomGeneralStatement.{u})
    (f : G ⟶ H) [IsAffine G.X.left] [Smooth G.X.hom]
    [IsSeparated H.X.hom] [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (s : Finset A) :
    ∃ D : SimultaneousHomModel R A f, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨DG, hs⟩ := exists_groupModel R A G s
  obtain ⟨DH, -⟩ := exists_separatedGroupModel DG.coefficients A H ∅
  let U := DH.coefficients
  have hU : (U.restrictScalars R).FG :=
    model_fg_tower DG.coefficients DH.coefficients DG.finite DH.finite
  let G₀ := (baseChange (Spec.algebraMap DG.coefficients U)).obj DG.group
  let eG : G ≅ (baseChange (Spec.algebraMap U A)).obj G₀ :=
    DG.iso ≪≫ (pullbackComparison (Spec.algebraMap DG.coefficients U)
      (Spec.algebraMap U A) (Spec.algebraMap DG.coefficients A)
      (model_spec_comp DG.coefficients U A) DG.group).symm
  let eH : H ≅ (baseChange (Spec.algebraMap U A)).obj DH.group := DH.iso
  let := DG.affine
  let := DG.smooth
  let := DH.separated
  let := DH.finitePresentation
  let := DH.quasiCompact
  have hGaff : IsAffineHom G₀.X.hom := by
    change IsAffineHom (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  have hGsm : Smooth G₀.X.hom := by
    change Smooth (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  let := hGaff
  let := hGsm
  obtain ⟨T, hT, -, g, hg⟩ := hHom U A G₀ DH.group (eG.inv ≫ f ≫ eH.hom) ∅
  have : IsScalarTower U T A := IsScalarTower.subalgebra' U A A T
  let cG := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (model_spec_comp U T A) G₀
  let cH := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (model_spec_comp U T A) DH.group
  let D : SimultaneousHomModel R A f :=
    { coefficients := T.restrictScalars R
      finite := model_fg_tower (U.restrictScalars R) T hU hT
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

/-- Scheme monicity descent makes a simultaneous model monic. -/
theorem SimultaneousHomModel.exists_mono
    (hMono : Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u})
    {f : G ⟶ H} [Mono f.hom.hom.left] (D : SimultaneousHomModel R A f) :
    ∃ E : SimultaneousHomModel R A f, Mono E.hom.hom.hom.left := by
  let := D.sourceAffine
  let := D.sourceSmooth
  let := D.targetSeparated
  obtain ⟨T, hT, -, hm⟩ := hMono D.coefficients A D.source.X D.target.X D.hom.hom.hom
    D.mono_over_algebra ∅
  exact ⟨D.enlarge T hT, hm⟩

end Langlands.GroupScheme.Descent.FiniteCoefficient
