import Langlands.GroupScheme.Descent.FiniteCoefficientFlatAffineGroup
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral

/-! # Finite coefficient models of homomorphisms of affine flat groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

private theorem flatHom_fg_tower {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : Subalgebra R A) (U : Subalgebra T A) (hT : T.FG) (hU : U.FG) :
    (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem flatHom_spec_comp (R B A : Type u) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- A homomorphism of affine flat finitely presented groups over one
finite coefficient subalgebra, with a commuting recovery square. -/
structure FlatAffineHomModel (f : G ⟶ H) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  source : GroupScheme (Spec (CommRingCat.of coefficients))
  target : GroupScheme (Spec (CommRingCat.of coefficients))
  sourceAffine : IsAffineHom source.X.hom
  sourceFlat : Flat source.X.hom
  sourceFinitePresentation : LocallyOfFinitePresentation source.X.hom
  targetAffine : IsAffineHom target.X.hom
  targetFlat : Flat target.X.hom
  targetFinitePresentation : LocallyOfFinitePresentation target.X.hom
  sourceCommutative : IsCommMonObj G.X → IsCommMonObj source.X
  targetCommutative : IsCommMonObj H.X → IsCommMonObj target.X
  hom : source ⟶ target
  sourceIso : G ≅ (baseChange (Spec.algebraMap coefficients A)).obj source
  targetIso : H ≅ (baseChange (Spec.algebraMap coefficients A)).obj target
  comm : sourceIso.hom ≫ (baseChange (Spec.algebraMap coefficients A)).map hom =
    f ≫ targetIso.hom

variable {R A}

/-- Coefficient enlargement preserves the full model and its recovery square. -/
def FlatAffineHomModel.enlarge {f : G ⟶ H} (D : FlatAffineHomModel R A f)
    (T : Subalgebra D.coefficients A) (hT : T.FG) : FlatAffineHomModel R A f where
  coefficients := T.restrictScalars R
  finite := flatHom_fg_tower D.coefficients T D.finite hT
  source := (baseChange (Spec.algebraMap D.coefficients T)).obj D.source
  target := (baseChange (Spec.algebraMap D.coefficients T)).obj D.target
  sourceAffine := by
    let := D.sourceAffine
    change IsAffineHom (pullback.snd D.source.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  sourceFlat := by
    let := D.sourceFlat
    change Flat (pullback.snd D.source.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  sourceFinitePresentation := by
    let := D.sourceFinitePresentation
    change LocallyOfFinitePresentation
      (pullback.snd D.source.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetAffine := by
    let := D.targetAffine
    change IsAffineHom (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetFlat := by
    let := D.targetFlat
    change Flat (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetFinitePresentation := by
    let := D.targetFinitePresentation
    change LocallyOfFinitePresentation
      (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  sourceCommutative := fun h => by
    let := D.sourceCommutative h
    exact inferInstanceAs
      (IsCommMonObj ((baseChange (Spec.algebraMap D.coefficients T)).obj D.source).X)
  targetCommutative := fun h => by
    let := D.targetCommutative h
    exact inferInstanceAs
      (IsCommMonObj ((baseChange (Spec.algebraMap D.coefficients T)).obj D.target).X)
  hom := (baseChange (Spec.algebraMap D.coefficients T)).map D.hom
  sourceIso := D.sourceIso ≪≫
    (pullbackComparison (Spec.algebraMap D.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap D.coefficients A) (flatHom_spec_comp D.coefficients T A) D.source).symm
  targetIso := D.targetIso ≪≫
    (pullbackComparison (Spec.algebraMap D.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap D.coefficients A) (flatHom_spec_comp D.coefficients T A) D.target).symm
  comm := by
    let cG := pullbackComparison (Spec.algebraMap D.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap D.coefficients A)
      (flatHom_spec_comp D.coefficients T A) D.source
    let cH := pullbackComparison (Spec.algebraMap D.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap D.coefficients A)
      (flatHom_spec_comp D.coefficients T A) D.target
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

variable (R A)

/-- A homomorphism of affine flat finitely presented groups descends to
finite coefficients containing any prescribed finite subset. -/
theorem exists_flatAffineHomModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] (s : Finset A) :
    ∃ D : FlatAffineHomModel R A f, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨DG, hs⟩ := exists_flatAffineGroupModel R A G s
  obtain ⟨DH, -⟩ := exists_flatAffineGroupModel DG.coefficients A H ∅
  let U := DH.coefficients
  have hU : (U.restrictScalars R).FG :=
    flatHom_fg_tower DG.coefficients DH.coefficients DG.finite DH.finite
  let G₀ := (baseChange (Spec.algebraMap DG.coefficients U)).obj DG.group
  let eG : G ≅ (baseChange (Spec.algebraMap U A)).obj G₀ :=
    DG.iso ≪≫ (pullbackComparison (Spec.algebraMap DG.coefficients U)
      (Spec.algebraMap U A) (Spec.algebraMap DG.coefficients A)
      (flatHom_spec_comp DG.coefficients U A) DG.group).symm
  let eH : H ≅ (baseChange (Spec.algebraMap U A)).obj DH.group := DH.iso
  let := DG.affine
  let := DG.flat
  let := DG.finitePresentation
  let := DH.affine
  let := DH.flat
  let := DH.finitePresentation
  have hGaff : IsAffineHom G₀.X.hom := by
    change IsAffineHom (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  have hGflat : Flat G₀.X.hom := by
    change Flat (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  have hGfp : LocallyOfFinitePresentation G₀.X.hom := by
    change LocallyOfFinitePresentation
      (pullback.snd DG.group.X.hom (Spec.algebraMap DG.coefficients U))
    infer_instance
  let := hGaff
  let := hGflat
  let := hGfp
  obtain ⟨T, hT, -, g, hg⟩ := homGeneral U A G₀ DH.group (eG.inv ≫ f ≫ eH.hom) ∅
  have : IsScalarTower U T A := IsScalarTower.subalgebra' U A A T
  let cG := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (flatHom_spec_comp U T A) G₀
  let cH := pullbackComparison (Spec.algebraMap U T) (Spec.algebraMap T A)
    (Spec.algebraMap U A) (flatHom_spec_comp U T A) DH.group
  let D : FlatAffineHomModel R A f :=
    { coefficients := T.restrictScalars R
      finite := flatHom_fg_tower (U.restrictScalars R) T hU hT
      source := (baseChange (Spec.algebraMap U T)).obj G₀
      target := (baseChange (Spec.algebraMap U T)).obj DH.group
      sourceAffine := by
        change IsAffineHom (pullback.snd G₀.X.hom (Spec.algebraMap U T))
        infer_instance
      sourceFlat := by
        change Flat (pullback.snd G₀.X.hom (Spec.algebraMap U T))
        infer_instance
      sourceFinitePresentation := by
        change LocallyOfFinitePresentation (pullback.snd G₀.X.hom (Spec.algebraMap U T))
        infer_instance
      targetAffine := by
        change IsAffineHom (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetFlat := by
        change Flat (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      targetFinitePresentation := by
        change LocallyOfFinitePresentation (pullback.snd DH.group.X.hom (Spec.algebraMap U T))
        infer_instance
      sourceCommutative := fun h => by
        let := DG.commutative h
        have : IsCommMonObj G₀.X := inferInstanceAs
          (IsCommMonObj ((baseChange (Spec.algebraMap DG.coefficients U)).obj DG.group).X)
        exact inferInstanceAs (IsCommMonObj ((baseChange (Spec.algebraMap U T)).obj G₀).X)
      targetCommutative := fun h => by
        let := DH.commutative h
        exact inferInstanceAs
          (IsCommMonObj ((baseChange (Spec.algebraMap U T)).obj DH.group).X)
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

/-- Choose a simultaneous flat affine model of the supplied homomorphism. -/
def flatAffineHomModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] : FlatAffineHomModel R A f :=
  Classical.choose (exists_flatAffineHomModel R A f ∅)

/-- The common coefficient ring is noetherian over any noetherian ground ring. -/
theorem FlatAffineHomModel.noetherian [IsNoetherianRing R]
    {f : G ⟶ H} (D : FlatAffineHomModel R A f) : IsNoetherianRing D.coefficients := by
  have : Algebra.FiniteType R D.coefficients :=
    (Subalgebra.fg_iff_finiteType _).mp D.finite
  exact Algebra.FiniteType.isNoetherianRing R D.coefficients

end Langlands.GroupScheme.Descent.FiniteCoefficient
