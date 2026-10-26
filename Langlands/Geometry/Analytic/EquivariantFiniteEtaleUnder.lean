import Langlands.Geometry.Analytic.FiniteEtaleUnder
import Langlands.Geometry.Analytic.NormContinuousAction

/-! # Algebraically finite étale affinoid objects under a continuous action -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G]

/-- Select actual equivariant bounded structural maps that are algebraically
finite étale on the underlying presented algebras. -/
def algebraicallyFiniteEtaleActionUnderProperty (X : NormContinuousAffinoidAction K G) :
    ObjectProperty (Under X) :=
  fun Y => (NormContinuousAffinoidAction.homMap Y.hom).AlgebraicallyFiniteEtale

/-- The full undercategory of a fixed norm-continuous affinoid action cut out by
algebraically finite étale structural maps. -/
abbrev AlgebraicallyFiniteEtaleAffinoidActionUnder (X : NormContinuousAffinoidAction K G) :=
  (algebraicallyFiniteEtaleActionUnderProperty X).FullSubcategory

namespace AlgebraicallyFiniteEtaleAffinoidActionUnder

variable {X : NormContinuousAffinoidAction K G}

/-- Bundle an actual equivariant bounded base map with its algebraic property. -/
def mk {Y : NormContinuousAffinoidAction K G} (f : X ⟶ Y)
    (hf : (NormContinuousAffinoidAction.homMap f).AlgebraicallyFiniteEtale) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X :=
  ⟨Under.mk f, hf⟩

/-- The displayed equivariant structural arrow. -/
abbrev baseHom (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X) :
    X ⟶ Y.obj.right :=
  Y.obj.hom

/-- The actual bounded algebra map underlying the structural arrow. -/
abbrev baseMap (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X) :
    BoundedAlgHom K X.obj.V Y.obj.right.obj.V :=
  NormContinuousAffinoidAction.homMap Y.baseHom

/-- The equivariant arrow retained by a map over the fixed base. -/
abbrev homAction {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X} (h : Y ⟶ Z) :
    Y.obj.right ⟶ Z.obj.right :=
  h.hom.right

/-- The actual bounded algebra map of an arrow over the fixed base. -/
abbrev homMap {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X} (h : Y ⟶ Z) :
    BoundedAlgHom K Y.obj.right.obj.V Z.obj.right.obj.V :=
  NormContinuousAffinoidAction.homMap (homAction h)

/-- Every compatible equivariant arrow is a morphism over the base. -/
def homMk {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y.obj.right ⟶ Z.obj.right) (comm : Y.baseHom ≫ h = Z.baseHom) : Y ⟶ Z :=
  ObjectProperty.homMk (Under.homMk h comm)

@[simp]
theorem homAction_homMk {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y.obj.right ⟶ Z.obj.right) (comm : Y.baseHom ≫ h = Z.baseHom) :
    homAction (homMk h comm) = h :=
  rfl

/-- Admit every equivariant bounded map whose algebra triangle commutes. -/
def boundedHomMk {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : BoundedAlgHom K Y.obj.right.obj.V Z.obj.right.obj.V)
    (equivariant : ∀ g : G, Y.obj.right.obj.ρ g ≫ h = h ≫ Z.obj.right.obj.ρ g)
    (comm : h.comp Y.baseMap = Z.baseMap) : Y ⟶ Z :=
  homMk (NormContinuousAffinoidAction.homMk h equivariant)
    (NormContinuousAffinoidAction.hom_ext comm)

@[simp]
theorem homMap_boundedHomMk {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : BoundedAlgHom K Y.obj.right.obj.V Z.obj.right.obj.V)
    (equivariant : ∀ g : G, Y.obj.right.obj.ρ g ≫ h = h ≫ Z.obj.right.obj.ρ g)
    (comm : h.comp Y.baseMap = Z.baseMap) :
    homMap (boundedHomMk h equivariant comm) = h :=
  rfl

theorem baseHom_comp_homAction {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y ⟶ Z) : Y.baseHom ≫ homAction h = Z.baseHom :=
  Under.w h.hom

theorem homMap_comp_baseMap {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y ⟶ Z) : (homMap h).comp Y.baseMap = Z.baseMap :=
  congrArg (fun f : X ⟶ Z.obj.right => NormContinuousAffinoidAction.homMap f)
    (baseHom_comp_homAction h)

@[ext]
theorem hom_ext {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X} {h k : Y ⟶ Z}
    (heq : homMap h = homMap k) : h = k :=
  ObjectProperty.hom_ext (algebraicallyFiniteEtaleActionUnderProperty X)
    (Under.UnderMorphism.ext (NormContinuousAffinoidAction.hom_ext heq))

/-- Finite étaleness of arrows follows from the structural maps and cancellation. -/
theorem homMap_algebraicallyFiniteEtale
    {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X} (h : Y ⟶ Z) :
    (homMap h).AlgebraicallyFiniteEtale := by
  apply BoundedAlgHom.AlgebraicallyFiniteEtale.of_comp Y.property
  rw [homMap_comp_baseMap]
  exact Z.property

/-- The identity structural map is available over every action. -/
def base (X : NormContinuousAffinoidAction K G) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X :=
  mk (𝟙 X) BoundedAlgHom.algebraicallyFiniteEtale_id

/-- Include all compatible equivariant triangles in the actual undercategory. -/
def inclusion (X : NormContinuousAffinoidAction K G) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X ⥤ Under X :=
  (algebraicallyFiniteEtaleActionUnderProperty X).ι

instance (X : NormContinuousAffinoidAction K G) : (inclusion X).Full :=
  inferInstanceAs (algebraicallyFiniteEtaleActionUnderProperty X).ι.Full

instance (X : NormContinuousAffinoidAction K G) : (inclusion X).Faithful :=
  inferInstanceAs (algebraicallyFiniteEtaleActionUnderProperty X).ι.Faithful

/-- Forget the structural arrow while retaining the actual action. -/
def forget (X : NormContinuousAffinoidAction K G) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X ⥤ NormContinuousAffinoidAction K G :=
  inclusion X ⋙ Under.forget X

instance (X : NormContinuousAffinoidAction K G) : (forget X).Faithful :=
  inferInstanceAs (inclusion X ⋙ Under.forget X).Faithful

/-- Forget only the action, retaining the actual finite étale base map. -/
def forgetAction (X : NormContinuousAffinoidAction K G) :
    AlgebraicallyFiniteEtaleAffinoidActionUnder X ⥤
      AlgebraicallyFiniteEtaleAffinoidUnder X.obj.V where
  obj Y := AlgebraicallyFiniteEtaleAffinoidUnder.mk Y.baseMap Y.property
  map h := AlgebraicallyFiniteEtaleAffinoidUnder.homMk (homMap h) (homMap_comp_baseMap h)
  map_id _ := rfl
  map_comp _ _ := rfl

instance (X : NormContinuousAffinoidAction K G) : (forgetAction X).Faithful where
  map_injective {Y} {Z} h k heq := by
    apply hom_ext
    exact congrArg (fun q : (forgetAction X).obj Y ⟶ (forgetAction X).obj Z =>
      AlgebraicallyFiniteEtaleAffinoidUnder.homMap q) heq

@[simp]
theorem forgetAction_obj_baseMap (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X) :
    ((forgetAction X).obj Y).baseMap = Y.baseMap :=
  rfl

@[simp]
theorem forgetAction_map_homMap {Y Z : AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y ⟶ Z) :
    AlgebraicallyFiniteEtaleAffinoidUnder.homMap ((forgetAction X).map h) = homMap h :=
  rfl

section Spectrum

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable [IsTopologicalGroup G]

/-- The actual continuous equivariant spectrum maps, in geometric direction. -/
def spectrumFunctor (X : NormContinuousAffinoidAction K G) :
    (AlgebraicallyFiniteEtaleAffinoidActionUnder X)ᵒᵖ ⥤ ContAction TopCat.{u} G :=
  (forget X).op ⋙ NormContinuousAffinoidAction.spectrumFunctor

/-- Actual continuous equivariant spectra over the fixed base spectrum. -/
def spectrumOverFunctor (X : NormContinuousAffinoidAction K G) :
    (AlgebraicallyFiniteEtaleAffinoidActionUnder X)ᵒᵖ ⥤
      Over (NormContinuousAffinoidAction.spectrum X) :=
  (inclusion X).op ⋙ (Over.opEquivOpUnder X).inverse ⋙
    Over.post NormContinuousAffinoidAction.spectrumFunctor

@[simp]
theorem spectrumOverFunctor_obj_apply (Y : AlgebraicallyFiniteEtaleAffinoidActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) (a : X.obj.V) :
    BanachSpectrum.toMulRingSeminorm
        (((spectrumOverFunctor X).obj (Opposite.op Y)).hom.hom.hom x) a =
      x (Y.baseMap a) :=
  rfl

@[simp]
theorem spectrumOverFunctor_map_apply
    {Y Z : (AlgebraicallyFiniteEtaleAffinoidActionUnder X)ᵒᵖ} (h : Y ⟶ Z)
    (x : BanachSpectrum Y.unop.obj.right.obj.V) (a : Z.unop.obj.right.obj.V) :
    BanachSpectrum.toMulRingSeminorm
        (((spectrumOverFunctor X).map h).left.hom.hom x) a =
      x (homMap h.unop a) :=
  rfl

/-- Forgetting the geometric base recovers exactly the continuous spectrum functor. -/
theorem spectrumOverFunctor_forget (X : NormContinuousAffinoidAction K G) :
    spectrumOverFunctor X ⋙ Over.forget (NormContinuousAffinoidAction.spectrum X) =
      spectrumFunctor X :=
  rfl

end Spectrum

end AlgebraicallyFiniteEtaleAffinoidActionUnder

end Langlands.Analytic
