import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteEtaleUnder

/-! # Finite étale positive-polyradius objects under a bounded base isomorphism -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q R : PresentedAffinoidAlgebra K}

/-- A categorical isomorphism already supplies both bounded inverse maps.
Its forward map is therefore algebraically finite étale. -/
theorem iso_hom_algebraicallyFiniteEtale
    (e : P ≅ Q) : e.hom.AlgebraicallyFiniteEtale := by
  apply BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
  have hleft : Function.LeftInverse (fun b : Q => e.inv.toAlgHom b)
      (fun a : P => e.hom.toAlgHom a) :=
    fun a => congrArg (fun f : BoundedAlgHom K P P => f a) e.hom_inv_id
  have hright : Function.RightInverse (fun b : Q => e.inv.toAlgHom b)
      (fun a : P => e.hom.toAlgHom a) :=
    fun a => congrArg (fun f : BoundedAlgHom K Q Q => f a) e.inv_hom_id
  exact ⟨hleft.injective, hright.surjective⟩

namespace AlgebraicallyFiniteEtaleUnder

/-- Restrict actual undercategory precomposition to finite étale structural
maps. The target algebra and every compatible bounded arrow are retained. -/
def reindex (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale) :
    AlgebraicallyFiniteEtaleUnder Q ⥤
      AlgebraicallyFiniteEtaleUnder P :=
  (algebraicallyFiniteEtaleUnderProperty P).lift
    (inclusion Q ⋙ Under.map f) (fun X => X.property.comp hf)

@[simp]
theorem reindex_obj_right (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    (X : AlgebraicallyFiniteEtaleUnder Q) :
    ((reindex f hf).obj X).obj.right = X.obj.right :=
  rfl

@[simp]
theorem reindex_baseMap (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    (X : AlgebraicallyFiniteEtaleUnder Q) :
    ((reindex f hf).obj X).baseMap = X.baseMap.comp f :=
  rfl

@[simp]
theorem reindex_homMap (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    {X Y : AlgebraicallyFiniteEtaleUnder Q} (h : X ⟶ Y) :
    homMap ((reindex f hf).map h) = homMap h :=
  rfl

instance (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale) :
    (reindex f hf).Faithful where
  map_injective {X} {Y} h k heq := by
    apply hom_ext
    exact congrArg (fun q : (reindex f hf).obj X ⟶ (reindex f hf).obj Y => homMap q) heq

/-- The forgetful functor retains exactly the same targets and bounded maps. -/
theorem reindex_comp_forget (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale) :
    reindex f hf ⋙ forget P = forget Q :=
  rfl

/-- Reindexing by the identity has identity maps on every target algebra. -/
def reindexId (P : PresentedAffinoidAlgebra K) :
    reindex (𝟙 P) BoundedAlgHom.algebraicallyFiniteEtale_id ≅
      𝟭 (AlgebraicallyFiniteEtaleUnder P) :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (algebraicallyFiniteEtaleUnderProperty P)
      ((Under.mapId P).app X.obj))
    (by intro X Y h; apply hom_ext; rfl)

/-- Successive precomposition agrees with precomposition by the composite,
through identity maps of the unchanged target algebras. -/
def reindexComp (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    (g : Q ⟶ R) (hg : g.AlgebraicallyFiniteEtale) :
    reindex (f ≫ g) (hg.comp hf) ≅ reindex g hg ⋙ reindex f hf :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (algebraicallyFiniteEtaleUnderProperty P)
      (Under.isoMk (Iso.refl X.obj.right) (by
        change (f ≫ g) ≫ X.obj.hom ≫ 𝟙 _ = f ≫ g ≫ X.obj.hom
        simp only [Category.comp_id, Category.assoc])))
    (by intro X Y h; apply hom_ext; rfl)

/-- Transport the structural map along an existing bounded base isomorphism. -/
def transport (e : P ≅ Q) :
    AlgebraicallyFiniteEtaleUnder Q ⥤
      AlgebraicallyFiniteEtaleUnder P :=
  reindex e.hom (iso_hom_algebraicallyFiniteEtale e)

@[simp]
theorem transport_baseMap (e : P ≅ Q)
    (X : AlgebraicallyFiniteEtaleUnder Q) :
    ((transport e).obj X).baseMap = X.baseMap.comp e.hom :=
  rfl

@[simp]
theorem transport_homMap (e : P ≅ Q)
    {X Y : AlgebraicallyFiniteEtaleUnder Q} (h : X ⟶ Y) :
    homMap ((transport e).map h) = homMap h :=
  rfl

/-- The unit is the existing undercategory unit, lifted to the full
finite étale subcategories. -/
def transportUnit (e : P ≅ Q) :
    𝟭 (AlgebraicallyFiniteEtaleUnder Q) ≅
      transport e ⋙ transport e.symm :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (algebraicallyFiniteEtaleUnderProperty Q)
      ((Under.mapIso e).unitIso.app X.obj))
    (by intro X Y h; apply hom_ext; rfl)

/-- The counit retains the identity bounded map of each target. -/
def transportCounit (e : P ≅ Q) :
    transport e.symm ⋙ transport e ≅
      𝟭 (AlgebraicallyFiniteEtaleUnder P) :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (algebraicallyFiniteEtaleUnderProperty P)
      ((Under.mapIso e).counitIso.app X.obj))
    (by intro X Y h; apply hom_ext; rfl)

/-- Bounded base isomorphisms give an actual equivalence of the fixed-base
finite étale categories, with the specified inverse transport. -/
def transportEquivalence (e : P ≅ Q) :
    AlgebraicallyFiniteEtaleUnder Q ≌
      AlgebraicallyFiniteEtaleUnder P where
  functor := transport e
  inverse := transport e.symm
  unitIso := transportUnit e
  counitIso := transportCounit e
  functor_unitIso_comp X := by apply hom_ext; rfl

/-- The unchanged target algebras also give the same actual spectrum functor. -/
theorem reindex_op_comp_spectrumFunctor
    (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale) :
    (reindex f hf).op ⋙ spectrumFunctor P = spectrumFunctor Q :=
  rfl

/-- The structural spectrum arrow of a precomposed object is its original
arrow followed by the actual spectrum map of the base arrow. -/
def spectrumReindexIso (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale) :
    (reindex f hf).op ⋙ spectrumOverFunctor P ≅
      spectrumOverFunctor Q ⋙ Over.map ((affinoidSpectrumFunctor K).map f.op) :=
  NatIso.ofComponents
    (fun X => Over.isoMk (Iso.refl _) (by
      apply TopCat.ext
      intro x
      apply BanachSpectrum.ext
      intro a
      rfl))
    (by
      intro X Y h
      apply Over.OverMorphism.ext
      apply TopCat.ext
      intro x
      rfl)

@[simp]
theorem spectrumReindexIso_hom_apply (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    (X : AlgebraicallyFiniteEtaleUnder Q) (x : BanachSpectrum X.obj.right) :
    ((spectrumReindexIso f hf).hom.app (Opposite.op X)).left x = x :=
  rfl

@[simp]
theorem spectrumReindexIso_inv_apply (f : P ⟶ Q) (hf : f.AlgebraicallyFiniteEtale)
    (X : AlgebraicallyFiniteEtaleUnder Q) (x : BanachSpectrum X.obj.right) :
    ((spectrumReindexIso f hf).inv.app (Opposite.op X)).left x = x :=
  rfl

end AlgebraicallyFiniteEtaleUnder

end Langlands.Analytic.PresentedAffinoidAlgebra
