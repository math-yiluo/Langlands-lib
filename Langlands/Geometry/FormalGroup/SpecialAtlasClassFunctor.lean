import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChangeAlongComposition

/-! # Varying-base functors of unframed special-atlas classes -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- Unframed actual special-atlas classes, with their supplied coefficient-algebra structures. -/
def classFunctor : CommAlgCat.{v} 𝒪[K] ⥤ Type (max u (v + 1)) where
  obj R := IsoClass (K := K) (D := D) (ι := ι) (R := R)
  map f := ↾(fun q => q.baseChangeAlong f.hom)
  map_id R := by
    ext q
    exact q.baseChangeAlong_id
  map_comp f g := by
    ext q
    exact (q.baseChangeAlong_comp f.hom g.hom).symm

/-- Restrict varying-base special-atlas classes to coefficient algebras in Nilp. -/
def nilpClassFunctor (π : 𝒪[K]) :
    Nilp.{u, v} 𝒪[K] π ⥤ Type (max u (v + 1)) :=
  Nilp.forget 𝒪[K] π ⋙ classFunctor ι

namespace HeightSquaredAtlas

/-- Varying-base classes whose representatives already carry actual height-d² certificates. -/
def classFunctor (π : 𝒪[K]) :
    CommAlgCat.{v} 𝒪[K] ⥤ Type (max u (v + 1)) where
  obj R := IsoClass (K := K) (D := D) (ι := ι) (R := R) π
  map f := ↾(fun q => q.baseChangeAlong f.hom)
  map_id R := by
    ext q
    exact q.baseChangeAlong_id
  map_comp f g := by
    ext q
    exact (q.baseChangeAlong_comp f.hom g.hom).symm

/-- The height-certified functor on the actual pi-nilpotent coefficient category. -/
def nilpClassFunctor (π : 𝒪[K]) :
    Nilp.{u, v} 𝒪[K] π ⥤ Type (max u (v + 1)) :=
  Nilp.forget 𝒪[K] π ⋙ classFunctor ι π

/-- Forgetting height is natural for actual extension along the supplied scalar maps. -/
def forgetHeightNatTrans (π : 𝒪[K]) :
    classFunctor ι π ⟶ SpecialAtlas.classFunctor ι where
  app R := ↾IsoClass.forgetHeight
  naturality R S f := by
    ext q
    exact q.forgetHeight_baseChangeAlong f.hom

/-- Every component retains the injection defined by the restricted comparison relation. -/
theorem forgetHeightNatTrans_injective (π : 𝒪[K]) (R : CommAlgCat.{v} 𝒪[K]) :
    Function.Injective ((forgetHeightNatTrans ι π).app R) :=
  IsoClass.forgetHeight_injective

/-- Restrict the same natural injection to Nilp. -/
def nilpForgetHeightNatTrans (π : 𝒪[K]) :
    nilpClassFunctor ι π ⟶ SpecialAtlas.nilpClassFunctor ι π :=
  Functor.whiskerLeft (Nilp.forget 𝒪[K] π) (forgetHeightNatTrans ι π)

/-- Restriction keeps the injection at every nilpotent coefficient algebra. -/
theorem nilpForgetHeightNatTrans_injective (π : 𝒪[K]) (R : Nilp.{u, v} 𝒪[K] π) :
    Function.Injective ((nilpForgetHeightNatTrans ι π).app R) :=
  forgetHeightNatTrans_injective ι π R.obj

/-- A height-certified class forces nilpotence of the actual coefficient image of pi. -/
theorem classFunctor_base_nilpotent (π : 𝒪[K]) (R : CommAlgCat.{v} 𝒪[K])
    (q : (classFunctor ι π).obj R) : IsNilpotent (algebraMap 𝒪[K] R π) :=
  q.base_nilpotent

/-- There are no height-certified classes over a base with nonnilpotent image of pi. -/
theorem classFunctor_isEmpty (π : 𝒪[K]) (R : CommAlgCat.{v} 𝒪[K])
    (h : ¬ IsNilpotent (algebraMap 𝒪[K] R π)) :
    IsEmpty ((classFunctor ι π).obj R) :=
  ⟨fun q => h (classFunctor_base_nilpotent ι π R q)⟩

end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
