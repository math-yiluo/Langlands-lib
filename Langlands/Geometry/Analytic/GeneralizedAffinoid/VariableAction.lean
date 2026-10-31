import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction
import Langlands.Topology.GroupAction.VariableContinuousAction

/-! # Actual affinoid quotient spectra with varying topological operator groups -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- An actual positive-polyradius quotient action with its topological group.
Morphisms below have the geometric direction. -/
structure VariableActionSpace where
  groupType : Type v
  [group : Group groupType]
  [topology : TopologicalSpace groupType]
  [topologicalGroup : IsTopologicalGroup groupType]
  algebraAction : NormContinuousAction K groupType

attribute [instance] VariableActionSpace.group VariableActionSpace.topology
  VariableActionSpace.topologicalGroup

namespace VariableActionSpace

variable {K}

/-- A source-to-target continuous group map and a contravariant bounded algebra
map, equivariant for that group map. -/
structure Hom (X Y : VariableActionSpace.{u, v} K) where
  groupHom : X.groupType →ₜ* Y.groupType
  algebraMap : BoundedAlgHom K Y.algebraAction.obj.V X.algebraAction.obj.V
  equivariant : ∀ (g : X.groupType) (a : Y.algebraAction.obj.V),
    algebraMap ((Y.algebraAction.obj.ρ (groupHom g)).toAlgHom a) =
      (X.algebraAction.obj.ρ g).toAlgHom (algebraMap a)

@[ext]
theorem Hom.ext {X Y : VariableActionSpace.{u, v} K} {f g : Hom X Y}
    (hgroup : f.groupHom = g.groupHom) (halgebra : f.algebraMap = g.algebraMap) :
    f = g := by
  cases f
  cases g
  cases hgroup
  cases halgebra
  rfl

def Hom.id (X : VariableActionSpace.{u, v} K) : Hom X X where
  groupHom := ContinuousMonoidHom.id X.groupType
  algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
  equivariant _ _ := rfl

def Hom.comp {X Y Z : VariableActionSpace.{u, v} K} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  groupHom := g.groupHom.comp f.groupHom
  algebraMap := f.algebraMap.comp g.algebraMap
  equivariant h a := by
    change f.algebraMap (g.algebraMap
      ((Z.algebraAction.obj.ρ (g.groupHom (f.groupHom h))).toAlgHom a)) =
      (X.algebraAction.obj.ρ h).toAlgHom (f.algebraMap (g.algebraMap a))
    rw [g.equivariant, f.equivariant]

instance : Category (VariableActionSpace.{u, v} K) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · ext h; rfl
    · rfl
  comp_id f := by
    apply Hom.ext
    · ext h; rfl
    · rfl
  assoc f g h := by
    apply Hom.ext
    · ext a; rfl
    · rfl

@[simp]
theorem comp_groupHom {X Y Z : VariableActionSpace.{u, v} K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).groupHom = g.groupHom.comp f.groupHom := rfl

@[simp]
theorem comp_algebraMap {X Y Z : VariableActionSpace.{u, v} K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).algebraMap = f.algebraMap.comp g.algebraMap := rfl

/-- Forget the group, retaining the actual quotient and opposite bounded map. -/
def forget : VariableActionSpace.{u, v} K ⥤ (PresentedAffinoidAlgebra K)ᵒᵖ where
  obj X := Opposite.op X.algebraAction.obj.V
  map {X Y} f :=
    Quiver.Hom.op (show Y.algebraAction.obj.V ⟶ X.algebraAction.obj.V from f.algebraMap)

/-- Every varying-group arrow is a bounded equivariant algebra arrow after
restricting the target action to the source group. -/
def restrictedAlgebraHom {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) :
    (NormContinuousAction.restrict f.groupHom).obj Y.algebraAction ⟶ X.algebraAction :=
  NormContinuousAction.homMk f.algebraMap (fun g => by
    apply BoundedAlgHom.ext
    intro a
    exact f.equivariant g a)

@[simp]
theorem restrictedAlgebraHom_map {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) :
    NormContinuousAction.homMap (restrictedAlgebraHom f) = f.algebraMap := rfl

section FixedGroup

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The existing opposite category of fixed-group actions embeds faithfully. -/
def ofFixed : NormContinuousSpace K G ⥤ VariableActionSpace.{u, v} K where
  obj X := ⟨G, X.unop⟩
  map f :=
    { groupHom := ContinuousMonoidHom.id G
      algebraMap := NormContinuousAction.homMap f.unop
      equivariant := NormContinuousAction.homMap_apply_action f.unop }
  map_id _ := by apply Hom.ext <;> rfl
  map_comp _ _ := by apply Hom.ext <;> rfl

instance : (ofFixed (K := K) G).Faithful where
  map_injective {X} {Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply NormContinuousAction.hom_ext
    exact congrArg (fun k => k.algebraMap) h

@[simp]
theorem ofFixed_map_groupHom {X Y : NormContinuousSpace K G} (f : X ⟶ Y) :
    ((ofFixed G).map f).groupHom = ContinuousMonoidHom.id G := rfl

end FixedGroup

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Construct actual jointly continuous quotient spectra and equivariant
seminorm pullback, retaining each source-to-target group map. -/
def spectrumFunctor :
    VariableActionSpace.{u, v} K ⥤ Langlands.Topology.VariableContinuousAction.{u, v} where
  obj X := ⟨X.groupType, NormContinuousAction.spectrum X.algebraAction⟩
  map {X Y} f :=
    { groupHom := f.groupHom
      spaceMap := TopCat.ofHom (BanachSpectrum.comapContinuous f.algebraMap.toBoundedRingHom)
      equivariant := fun g => by
        apply TopCat.ext
        intro x
        change BanachSpectrum X.algebraAction.obj.V at x
        apply BanachSpectrum.ext
        intro a
        change x ((X.algebraAction.obj.ρ (g⁻¹)).toAlgHom (f.algebraMap a)) =
          x (f.algebraMap ((Y.algebraAction.obj.ρ ((f.groupHom g)⁻¹)).toAlgHom a))
        rw [← map_inv]
        exact congrArg (fun b : X.algebraAction.obj.V => x b) (f.equivariant (g⁻¹) a).symm }
  map_id _ := by
    apply Langlands.Topology.VariableContinuousAction.Hom.ext
    · rfl
    · apply TopCat.ext
      intro x
      exact BanachSpectrum.ext fun _ => rfl
  map_comp _ _ := by
    apply Langlands.Topology.VariableContinuousAction.Hom.ext
    · rfl
    · apply TopCat.ext
      intro x
      exact BanachSpectrum.ext fun _ => rfl

@[simp]
theorem spectrumFunctor_map_groupHom {X Y : VariableActionSpace.{u, v} K}
    (f : X ⟶ Y) : (spectrumFunctor.map f).groupHom = f.groupHom := rfl

@[simp]
theorem spectrumFunctor_map_apply {X Y : VariableActionSpace.{u, v} K}
    (f : X ⟶ Y) (x : BanachSpectrum X.algebraAction.obj.V)
    (a : Y.algebraAction.obj.V) :
    BanachSpectrum.toMulRingSeminorm ((spectrumFunctor.map f).spaceMap x) a =
      x (f.algebraMap a) := rfl

/-- Forgetting operators commutes exactly with the actual spectrum functor. -/
theorem spectrumFunctor_comp_forget :
    spectrumFunctor (K := K) ⋙ Langlands.Topology.VariableContinuousAction.forget =
      forget ⋙ affinoidSpectrumFunctor K := rfl

end Spectrum

end VariableActionSpace

end Langlands.Analytic.PresentedAffinoidAlgebra
