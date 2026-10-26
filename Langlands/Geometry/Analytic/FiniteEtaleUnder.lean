import Langlands.Geometry.Analytic.FiniteEtaleAlgebra
import Langlands.Geometry.Analytic.FiniteBoundedMaps
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Algebraically finite étale affinoid algebras under a fixed base -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

/-- Cancel the first arrow in an algebraically finite étale composite.
Only algebraic properties are used; no completeness or valuation hypothesis is needed. -/
theorem AlgebraicallyFiniteEtale.of_comp {f : BoundedAlgHom K A B}
    {g : BoundedAlgHom K B C} (hf : f.AlgebraicallyFiniteEtale)
    (hgf : (g.comp f).AlgebraicallyFiniteEtale) : g.AlgebraicallyFiniteEtale := by
  refine ⟨RingHom.Finite.of_comp_finite hgf.1, ?_⟩
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra B C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale A B := hf.2
  let : Algebra.Etale A C := hgf.2
  exact Algebra.Etale.of_restrictScalars A B C

end BoundedAlgHom

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Actual arrows out of `P` whose underlying ring maps are finite and étale. -/
def algebraicallyFiniteEtaleUnderProperty (P : PresentedStrictAffinoidAlgebra K) :
    ObjectProperty (Under P) :=
  fun X => X.hom.AlgebraicallyFiniteEtale

/-- The full subcategory of the actual bounded-map undercategory cut out by
finite étale structural maps. All compatible bounded arrows are retained. -/
abbrev AlgebraicallyFiniteEtaleAffinoidUnder (P : PresentedStrictAffinoidAlgebra K) :=
  (algebraicallyFiniteEtaleUnderProperty P).FullSubcategory

namespace AlgebraicallyFiniteEtaleAffinoidUnder

variable {P : PresentedStrictAffinoidAlgebra K}

/-- Construct an object from a specified actual finite étale bounded base map. -/
def mk {Q : PresentedStrictAffinoidAlgebra K} (f : BoundedAlgHom K P Q)
    (hf : f.AlgebraicallyFiniteEtale) : AlgebraicallyFiniteEtaleAffinoidUnder P :=
  ⟨Under.mk f, hf⟩

/-- The actual bounded structural map of an object. -/
abbrev baseMap (X : AlgebraicallyFiniteEtaleAffinoidUnder P) :
    BoundedAlgHom K P X.obj.right :=
  X.obj.hom

/-- The bounded algebra map in a morphism of the fixed-base category. -/
abbrev homMap {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P} (h : X ⟶ Y) :
    BoundedAlgHom K X.obj.right Y.obj.right :=
  h.hom.right

/-- Construct an arrow from its actual bounded commuting triangle. -/
def homMk {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P}
    (h : BoundedAlgHom K X.obj.right Y.obj.right)
    (comm : h.comp X.baseMap = Y.baseMap) : X ⟶ Y :=
  ObjectProperty.homMk (Under.homMk h comm)

@[simp]
theorem homMap_homMk {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P}
    (h : BoundedAlgHom K X.obj.right Y.obj.right)
    (comm : h.comp X.baseMap = Y.baseMap) : homMap (homMk h comm) = h :=
  rfl

/-- Every arrow is a map over the specified base. -/
theorem homMap_comp_baseMap {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P}
    (h : X ⟶ Y) : (homMap h).comp X.baseMap = Y.baseMap :=
  Under.w h.hom

@[ext]
theorem hom_ext {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P} {h k : X ⟶ Y}
    (heq : homMap h = homMap k) : h = k :=
  ObjectProperty.hom_ext (algebraicallyFiniteEtaleUnderProperty P)
    (Under.UnderMorphism.ext heq)

/-- A compatible arrow between two finite étale objects is itself finite étale. -/
theorem homMap_algebraicallyFiniteEtale
    {X Y : AlgebraicallyFiniteEtaleAffinoidUnder P} (h : X ⟶ Y) :
    (homMap h).AlgebraicallyFiniteEtale := by
  apply BoundedAlgHom.AlgebraicallyFiniteEtale.of_comp X.property
  rw [homMap_comp_baseMap]
  exact Y.property

/-- The identity structural arrow is an object over every base. -/
def base (P : PresentedStrictAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleAffinoidUnder P :=
  mk (BoundedAlgHom.id K P) BoundedAlgHom.algebraicallyFiniteEtale_id

/-- The inclusion retains exactly the commuting bounded-map triangles. -/
def inclusion (P : PresentedStrictAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleAffinoidUnder P ⥤ Under P :=
  (algebraicallyFiniteEtaleUnderProperty P).ι

instance (P : PresentedStrictAffinoidAlgebra K) : (inclusion P).Full :=
  inferInstanceAs (algebraicallyFiniteEtaleUnderProperty P).ι.Full

instance (P : PresentedStrictAffinoidAlgebra K) : (inclusion P).Faithful :=
  inferInstanceAs (algebraicallyFiniteEtaleUnderProperty P).ι.Faithful

/-- Forget the structural map while retaining its actual target algebra. -/
def forget (P : PresentedStrictAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleAffinoidUnder P ⥤ PresentedStrictAffinoidAlgebra K :=
  inclusion P ⋙ Under.forget P

instance (P : PresentedStrictAffinoidAlgebra K) : (forget P).Faithful :=
  inferInstanceAs (inclusion P ⋙ Under.forget P).Faithful

/-- Every arrow factors through the existing wide category of finite étale maps. -/
def toFiniteEtale (P : PresentedStrictAffinoidAlgebra K) :
    AlgebraicallyFiniteEtaleAffinoidUnder P ⥤ AlgebraicallyFiniteEtaleAffinoidAlgebra K where
  obj X := ⟨X.obj.right⟩
  map h := ⟨homMap h, homMap_algebraicallyFiniteEtale h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

section NontrivialValuation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] {P : PresentedStrictAffinoidAlgebra K}

/-- Every compatible algebraic map has one bounded lift to the actual hom-set.
The nontrivial valuation is used only for this automatic boundedness comparison. -/
def algebraicHomEquiv (X Y : AlgebraicallyFiniteEtaleAffinoidUnder P) :
    {h : X.obj.right →ₐ[K] Y.obj.right //
      h.comp X.baseMap.toAlgHom = Y.baseMap.toAlgHom} ≃ (X ⟶ Y) :=
  (BoundedAlgHom.finiteTriangleEquiv X.baseMap X.property.1 Y.baseMap).trans
    { toFun := fun h => homMk h.1 h.2
      invFun := fun h => ⟨homMap h, homMap_comp_baseMap h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => hom_ext rfl }

@[simp]
theorem algebraicHomEquiv_apply_toAlgHom (X Y : AlgebraicallyFiniteEtaleAffinoidUnder P)
    (h : {h : X.obj.right →ₐ[K] Y.obj.right //
      h.comp X.baseMap.toAlgHom = Y.baseMap.toAlgHom}) :
    (homMap (algebraicHomEquiv X Y h)).toAlgHom = h.1 :=
  rfl

end NontrivialValuation

/-- The actual spectrum functor on the fixed-base category in geometric direction. -/
def spectrumFunctor [CompleteSpace K] (P : PresentedStrictAffinoidAlgebra K) :
    (AlgebraicallyFiniteEtaleAffinoidUnder P)ᵒᵖ ⥤ TopCat :=
  (forget P).op ⋙ strictAffinoidSpectrumFunctor K

@[simp]
theorem spectrumFunctor_map_apply [CompleteSpace K]
    {X Y : (AlgebraicallyFiniteEtaleAffinoidUnder P)ᵒᵖ} (h : X ⟶ Y)
    (x : BanachSpectrum X.unop.obj.right) (a : Y.unop.obj.right) :
    BanachSpectrum.toMulRingSeminorm ((spectrumFunctor P).map h x) a =
      x.toMulRingSeminorm ((homMap h.unop).toAlgHom a) :=
  rfl

end AlgebraicallyFiniteEtaleAffinoidUnder

end Langlands.Analytic
