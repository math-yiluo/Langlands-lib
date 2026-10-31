import Langlands.Geometry.Analytic.GeneralizedAffinoid.EquivariantFiniteEtaleUnder
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteEtaleUnderTransport

/-! # Structural-base transport of relative finite étale positive-polyradius actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G]
  {X Y Z : NormContinuousAction K G}

/-- An equivariant base isomorphism retains both bounded inverse maps. -/
theorem NormContinuousAction.iso_hom_algebraicallyFiniteEtale (e : X ≅ Y) :
    (NormContinuousAction.homMap e.hom).AlgebraicallyFiniteEtale :=
  Langlands.Analytic.PresentedAffinoidAlgebra.iso_hom_algebraicallyFiniteEtale
    (NormContinuousAction.forget.mapIso e)

namespace AlgebraicallyFiniteEtaleActionUnder

/-- Precompose the structural arrow along an actual finite étale equivariant map. -/
def reindex (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    AlgebraicallyFiniteEtaleActionUnder Y ⥤
      AlgebraicallyFiniteEtaleActionUnder X :=
  (algebraicallyFiniteEtaleActionUnderProperty X).lift
    (inclusion Y ⋙ Under.map f) (fun W => W.property.comp hf)

@[simp]
theorem reindex_obj_right (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (W : AlgebraicallyFiniteEtaleActionUnder Y) :
    ((reindex f hf).obj W).obj.right = W.obj.right :=
  rfl

@[simp]
theorem reindex_obj_baseHom (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (W : AlgebraicallyFiniteEtaleActionUnder Y) :
    ((reindex f hf).obj W).baseHom = f ≫ W.baseHom :=
  rfl

@[simp]
theorem reindex_obj_baseMap (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (W : AlgebraicallyFiniteEtaleActionUnder Y) :
    ((reindex f hf).obj W).baseMap =
      W.baseMap.comp (NormContinuousAction.homMap f) :=
  rfl

@[simp]
theorem reindex_map_homAction (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    {W V : AlgebraicallyFiniteEtaleActionUnder Y} (h : W ⟶ V) :
    homAction ((reindex f hf).map h) = homAction h :=
  rfl

@[simp]
theorem reindex_map_homMap (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    {W V : AlgebraicallyFiniteEtaleActionUnder Y} (h : W ⟶ V) :
    homMap ((reindex f hf).map h) = homMap h :=
  rfl

instance (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    (reindex f hf).Faithful where
  map_injective {W} {V} h k heq := by
    apply hom_ext
    exact congrArg (fun q : (reindex f hf).obj W ⟶ (reindex f hf).obj V => homMap q) heq

/-- Forgetting the structural arrow retains exactly the original actions and maps. -/
theorem reindex_comp_forget (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    reindex f hf ⋙ forget X = forget Y :=
  rfl

/-- Forgetting actions gives precisely the published non-equivariant precomposition. -/
theorem reindex_comp_forgetAction (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    reindex f hf ⋙ forgetAction X =
      forgetAction Y ⋙
        AlgebraicallyFiniteEtaleUnder.reindex
          (NormContinuousAction.homMap f) hf :=
  rfl

/-- Identity precomposition has the identity equivariant map on each target. -/
def reindexId (X : NormContinuousAction K G) :
    reindex (𝟙 X) BoundedAlgHom.algebraicallyFiniteEtale_id ≅
      𝟭 (AlgebraicallyFiniteEtaleActionUnder X) :=
  NatIso.ofComponents
    (fun W => ObjectProperty.isoMk (algebraicallyFiniteEtaleActionUnderProperty X)
      ((Under.mapId X).app W.obj))
    (by intro W V h; apply hom_ext; rfl)

/-- Successive structural precomposition agrees with precomposition by the composite. -/
def reindexComp (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (g : Y ⟶ Z)
    (hg : (NormContinuousAction.homMap g).AlgebraicallyFiniteEtale) :
    reindex (f ≫ g) (hg.comp hf) ≅ reindex g hg ⋙ reindex f hf :=
  NatIso.ofComponents
    (fun W => ObjectProperty.isoMk (algebraicallyFiniteEtaleActionUnderProperty X)
      (Under.isoMk (Iso.refl W.obj.right) (by
        change (f ≫ g) ≫ W.obj.hom ≫ 𝟙 _ = f ≫ g ≫ W.obj.hom
        simp only [Category.comp_id, Category.assoc])))
    (by intro W V h; apply hom_ext; rfl)

/-- Change the structural base along an existing bounded equivariant isomorphism. -/
def transport (e : X ≅ Y) :
    AlgebraicallyFiniteEtaleActionUnder Y ⥤
      AlgebraicallyFiniteEtaleActionUnder X :=
  reindex e.hom (NormContinuousAction.iso_hom_algebraicallyFiniteEtale e)

@[simp]
theorem transport_obj_baseMap (e : X ≅ Y)
    (W : AlgebraicallyFiniteEtaleActionUnder Y) :
    ((transport e).obj W).baseMap =
      W.baseMap.comp (NormContinuousAction.homMap e.hom) :=
  rfl

@[simp]
theorem transport_map_homMap (e : X ≅ Y)
    {W V : AlgebraicallyFiniteEtaleActionUnder Y} (h : W ⟶ V) :
    homMap ((transport e).map h) = homMap h :=
  rfl

/-- Lift the actual undercategory unit, retaining the identity on target actions. -/
def transportUnit (e : X ≅ Y) :
    𝟭 (AlgebraicallyFiniteEtaleActionUnder Y) ≅
      transport e ⋙ transport e.symm :=
  NatIso.ofComponents
    (fun W => ObjectProperty.isoMk (algebraicallyFiniteEtaleActionUnderProperty Y)
      ((Under.mapIso e).unitIso.app W.obj))
    (by intro W V h; apply hom_ext; rfl)

/-- Lift the actual undercategory counit with the same identity target maps. -/
def transportCounit (e : X ≅ Y) :
    transport e.symm ⋙ transport e ≅
      𝟭 (AlgebraicallyFiniteEtaleActionUnder X) :=
  NatIso.ofComponents
    (fun W => ObjectProperty.isoMk (algebraicallyFiniteEtaleActionUnderProperty X)
      ((Under.mapIso e).counitIso.app W.obj))
    (by intro W V h; apply hom_ext; rfl)

/-- Both bounded equivariant directions give an equivalence of relative categories. -/
def transportEquivalence (e : X ≅ Y) :
    AlgebraicallyFiniteEtaleActionUnder Y ≌
      AlgebraicallyFiniteEtaleActionUnder X where
  functor := transport e
  inverse := transport e.symm
  unitIso := transportUnit e
  counitIso := transportCounit e
  functor_unitIso_comp W := by apply hom_ext; rfl

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable [IsTopologicalGroup G]

/-- Precomposition retains exactly the target continuous spectra and their maps. -/
theorem reindex_op_comp_spectrumFunctor (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    (reindex f hf).op ⋙ spectrumFunctor X = spectrumFunctor Y :=
  rfl

/-- The new structural spectrum map is the old one followed by the base spectrum map. -/
def spectrumReindexIso (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale) :
    (reindex f hf).op ⋙ spectrumOverFunctor X ≅
      spectrumOverFunctor Y ⋙
        Over.map (NormContinuousAction.spectrumFunctor.map f.op) :=
  NatIso.ofComponents
    (fun W => Over.isoMk (Iso.refl _) (by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      apply BanachSpectrum.ext
      intro a
      rfl))
    (by
      intro W V h
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      rfl)

@[simp]
theorem spectrumReindexIso_hom_apply (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (W : AlgebraicallyFiniteEtaleActionUnder Y)
    (x : BanachSpectrum W.obj.right.obj.V) :
    ((spectrumReindexIso f hf).hom.app (Opposite.op W)).left.hom.hom x = x :=
  rfl

@[simp]
theorem spectrumReindexIso_inv_apply (f : X ⟶ Y)
    (hf : (NormContinuousAction.homMap f).AlgebraicallyFiniteEtale)
    (W : AlgebraicallyFiniteEtaleActionUnder Y)
    (x : BanachSpectrum W.obj.right.obj.V) :
    ((spectrumReindexIso f hf).inv.app (Opposite.op W)).left.hom.hom x = x :=
  rfl

end Spectrum

end AlgebraicallyFiniteEtaleActionUnder

end Langlands.Analytic.PresentedAffinoidAlgebra
