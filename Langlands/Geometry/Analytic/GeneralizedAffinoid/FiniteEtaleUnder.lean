import Langlands.Geometry.Analytic.FiniteEtaleUnder
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach

/-! # Algebraically finite étale positive-polyradius quotients under a base -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Actual bounded structural maps that are finite and étale as ring maps. -/
def algebraicallyFiniteEtaleUnderProperty (P : PresentedAffinoidAlgebra K) :
    ObjectProperty (Under P) :=
  fun X => X.hom.AlgebraicallyFiniteEtale

/-- The full category of algebraically finite étale structural maps between
actual positive-polyradius quotients, retaining every bounded triangle. -/
abbrev AlgebraicallyFiniteEtaleUnder (P : PresentedAffinoidAlgebra K) :=
  (algebraicallyFiniteEtaleUnderProperty P).FullSubcategory

namespace AlgebraicallyFiniteEtaleUnder

variable {P : PresentedAffinoidAlgebra K}

/-- Bundle a specified finite étale bounded structural map. -/
def mk {Q : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K P Q)
    (hf : f.AlgebraicallyFiniteEtale) : AlgebraicallyFiniteEtaleUnder P :=
  ⟨Under.mk f, hf⟩

/-- The actual bounded structural map. -/
abbrev baseMap (X : AlgebraicallyFiniteEtaleUnder P) :
    BoundedAlgHom K P X.obj.right :=
  X.obj.hom

/-- The actual bounded map retained by an arrow over the base. -/
abbrev homMap {X Y : AlgebraicallyFiniteEtaleUnder P} (h : X ⟶ Y) :
    BoundedAlgHom K X.obj.right Y.obj.right :=
  h.hom.right

/-- Every bounded commuting triangle defines an arrow. -/
def homMk {X Y : AlgebraicallyFiniteEtaleUnder P}
    (h : BoundedAlgHom K X.obj.right Y.obj.right)
    (comm : h.comp X.baseMap = Y.baseMap) : X ⟶ Y :=
  ObjectProperty.homMk (Under.homMk h comm)

@[simp]
theorem homMap_homMk {X Y : AlgebraicallyFiniteEtaleUnder P}
    (h : BoundedAlgHom K X.obj.right Y.obj.right)
    (comm : h.comp X.baseMap = Y.baseMap) : homMap (homMk h comm) = h :=
  rfl

/-- The triangle equation holds for each retained bounded map. -/
theorem homMap_comp_baseMap {X Y : AlgebraicallyFiniteEtaleUnder P}
    (h : X ⟶ Y) : (homMap h).comp X.baseMap = Y.baseMap :=
  Under.w h.hom

@[ext]
theorem hom_ext {X Y : AlgebraicallyFiniteEtaleUnder P} {h k : X ⟶ Y}
    (heq : homMap h = homMap k) : h = k :=
  ObjectProperty.hom_ext (algebraicallyFiniteEtaleUnderProperty P)
    (Under.UnderMorphism.ext heq)

/-- Finite étaleness of each arrow follows by cancellation of its base map. -/
theorem homMap_algebraicallyFiniteEtale
    {X Y : AlgebraicallyFiniteEtaleUnder P} (h : X ⟶ Y) :
    (homMap h).AlgebraicallyFiniteEtale := by
  apply BoundedAlgHom.AlgebraicallyFiniteEtale.of_comp X.property
  rw [homMap_comp_baseMap]
  exact Y.property

/-- The identity structural map is an object over every presentation. -/
def base (P : PresentedAffinoidAlgebra K) : AlgebraicallyFiniteEtaleUnder P :=
  mk (BoundedAlgHom.id K P) BoundedAlgHom.algebraicallyFiniteEtale_id

/-- The full inclusion retains all compatible bounded triangles. -/
def inclusion (P : PresentedAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleUnder P ⥤ Under P :=
  (algebraicallyFiniteEtaleUnderProperty P).ι

instance (P : PresentedAffinoidAlgebra K) : (inclusion P).Full :=
  inferInstanceAs (algebraicallyFiniteEtaleUnderProperty P).ι.Full

instance (P : PresentedAffinoidAlgebra K) : (inclusion P).Faithful :=
  inferInstanceAs (algebraicallyFiniteEtaleUnderProperty P).ι.Faithful

/-- Forget the structural map and retain the actual target quotient algebra. -/
def forget (P : PresentedAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleUnder P ⥤ PresentedAffinoidAlgebra K :=
  inclusion P ⋙ Under.forget P

instance (P : PresentedAffinoidAlgebra K) : (forget P).Faithful :=
  inferInstanceAs (inclusion P ⋙ Under.forget P).Faithful

section NontrivialValuation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] {P : PresentedAffinoidAlgebra K}

/-- All algebraic triangles have unique bounded lifts to the relative hom-set.
The finite Banach-module theorem constructs the bound. -/
def algebraicHomEquiv (X Y : AlgebraicallyFiniteEtaleUnder P) :
    {h : X.obj.right →ₐ[K] Y.obj.right //
      h.comp X.baseMap.toAlgHom = Y.baseMap.toAlgHom} ≃ (X ⟶ Y) :=
  (BoundedAlgHom.finiteTriangleEquiv X.baseMap X.property.1 Y.baseMap).trans
    { toFun := fun h => homMk h.1 h.2
      invFun := fun h => ⟨homMap h, homMap_comp_baseMap h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => hom_ext rfl }

@[simp]
theorem algebraicHomEquiv_apply_toAlgHom (X Y : AlgebraicallyFiniteEtaleUnder P)
    (h : {h : X.obj.right →ₐ[K] Y.obj.right //
      h.comp X.baseMap.toAlgHom = Y.baseMap.toAlgHom}) :
    (homMap (algebraicHomEquiv X Y h)).toAlgHom = h.1 :=
  rfl

end NontrivialValuation

/-- The actual spectra and bounded pullbacks in geometric direction. -/
def spectrumFunctor (P : PresentedAffinoidAlgebra K) :
    (AlgebraicallyFiniteEtaleUnder P)ᵒᵖ ⥤ TopCat.{u} :=
  (forget P).op ⋙ affinoidSpectrumFunctor K

@[simp]
theorem spectrumFunctor_map_apply
    {X Y : (AlgebraicallyFiniteEtaleUnder P)ᵒᵖ} (h : X ⟶ Y)
    (x : BanachSpectrum X.unop.obj.right) (a : Y.unop.obj.right) :
    BanachSpectrum.toMulRingSeminorm ((spectrumFunctor P).map h x) a =
      x ((homMap h.unop).toAlgHom a) :=
  rfl

/-- Actual continuous spectrum maps over the spectrum of the fixed base. -/
def spectrumOverFunctor (P : PresentedAffinoidAlgebra K) :
    (AlgebraicallyFiniteEtaleUnder P)ᵒᵖ ⥤ Over (TopCat.of (BanachSpectrum P)) :=
  (inclusion P).op ⋙ (Over.opEquivOpUnder P).inverse ⋙
    Over.post (affinoidSpectrumFunctor K)

@[simp]
theorem spectrumOverFunctor_obj_apply (Y : AlgebraicallyFiniteEtaleUnder P)
    (x : BanachSpectrum Y.obj.right) (a : P) :
    BanachSpectrum.toMulRingSeminorm
        (((spectrumOverFunctor P).obj (Opposite.op Y)).hom x) a =
      x (Y.baseMap a) :=
  rfl

@[simp]
theorem spectrumOverFunctor_map_apply
    {Y Z : (AlgebraicallyFiniteEtaleUnder P)ᵒᵖ} (h : Y ⟶ Z)
    (x : BanachSpectrum Y.unop.obj.right) (a : Z.unop.obj.right) :
    BanachSpectrum.toMulRingSeminorm
        (((spectrumOverFunctor P).map h).left x) a =
      x (homMap h.unop a) :=
  rfl

/-- Forgetting the geometric structural map recovers exactly the spectrum functor. -/
theorem spectrumOverFunctor_forget (P : PresentedAffinoidAlgebra K) :
    spectrumOverFunctor P ⋙ Over.forget (TopCat.of (BanachSpectrum P)) =
      spectrumFunctor P :=
  rfl

end AlgebraicallyFiniteEtaleUnder

end Langlands.Analytic.PresentedAffinoidAlgebra
