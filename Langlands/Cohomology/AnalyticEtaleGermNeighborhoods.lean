import Langlands.Geometry.Analytic.DistinguishedOpenNeighborhoods
import Langlands.Sheaf.Equivariant.AnalyticEtaleOpenRestriction
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleGermSystem
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Maps.Proper.Basic

/-! # Pointed étale neighbourhoods for analytic Galois germs -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Set Topology TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- A pointed étale object whose inverse images of base neighbourhoods
are cofinal among the neighbourhoods of its point. -/
structure EtaleGermNeighborhood (y : localizedSpaceFunctor.obj X) where
  obj : EtaleSite X
  point : localizedSpaceFunctor.obj obj.left
  map_point : localizedSpaceFunctor.map obj.hom point = y
  shrink (B : Opens (localizedSpaceFunctor.obj obj.left)) (hB : point ∈ B) :
    ∃ O : Opens (localizedSpaceFunctor.obj X), y ∈ O ∧
      localizedSpaceFunctor.map obj.hom ⁻¹' (O : Set (localizedSpaceFunctor.obj X)) ⊆
        (B : Set (localizedSpaceFunctor.obj obj.left))

/-- Restrict a fixed étale object to the ordinary neighbourhoods of `y`. -/
def etaleNeighborhoodDiagram (y : localizedSpaceFunctor.obj X) (A : EtaleSite X) :
    nbhdIndex.{u, v, uL} X y ⥤ EtaleSite X :=
  nbhdOpen.{u, v, uL} X y ⋙ etaleOpenRestrictionFunctor X ⋙
    (CategoryTheory.evaluation (EtaleSite X) (EtaleSite X)).obj A

theorem restrictEtale_hom_apply (O : Opens (localizedSpaceFunctor.obj X)) (A : EtaleSite X)
    (x : localizedSpaceFunctor.obj (((etaleOpenRestrictionFunctor X).obj O).obj A).left) :
    localizedSpaceFunctor.map (((etaleOpenRestrictionFunctor X).obj O).obj A).hom x =
      localizedSpaceFunctor.map A.hom x.val := by
  have h := MorphismProperty.Over.w ((etaleOpenRestrictionInclusion X O).app A)
  rw [← h, localizedSpaceFunctor.map_comp_apply]
  rfl

namespace EtaleGermNeighborhood

variable {X} {y : localizedSpaceFunctor.obj X} (W : EtaleGermNeighborhood X y)

/-- The base space itself represents a pointed étale neighbourhood. -/
def base (y : localizedSpaceFunctor.obj X) : EtaleGermNeighborhood X y where
  obj := MorphismProperty.Over.mk ⊤ (𝟙 X) (etale_of_isIso _)
  point := y
  map_point := by change localizedSpaceFunctor.map (𝟙 X) y = y; simp
  shrink B hB := by
    change Opens (localizedSpaceFunctor.obj X) at B
    refine ⟨B, hB, ?_⟩
    change localizedSpaceFunctor.map (𝟙 X) ⁻¹' (B : Set (localizedSpaceFunctor.obj X)) ⊆
      (B : Set (localizedSpaceFunctor.obj X))
    simp

/-- A base-open restriction keeps the cofinality of the pointed neighbourhood. -/
def restrict (U : Opens (localizedSpaceFunctor.obj X)) (hy : y ∈ U) :
    EtaleGermNeighborhood X y := by
  let A := ((etaleOpenRestrictionFunctor X).obj U).obj W.obj
  have hp : localizedSpaceFunctor.map W.obj.hom W.point ∈ U := by
    rwa [W.map_point]
  let x : localizedSpaceFunctor.obj A.left := ⟨W.point, hp⟩
  refine ⟨A, x, (restrictEtale_hom_apply X U W.obj x).trans W.map_point, ?_⟩
  intro B hx
  let j := restrictEtaleInclusion X U W.obj
  have hj : IsOpenEmbedding (localizedSpaceFunctor.map j) :=
    isOpenEmbedding_domainι _ _
  let V : Opens (localizedSpaceFunctor.obj W.obj.left) :=
    ⟨localizedSpaceFunctor.map j '' (B : Set (localizedSpaceFunctor.obj A.left)),
      hj.isOpenMap (B : Set (localizedSpaceFunctor.obj A.left)) B.isOpen⟩
  obtain ⟨T, ht, hsub⟩ := W.shrink V ⟨x, hx, rfl⟩
  refine ⟨T, ht, ?_⟩
  intro t ht'
  obtain ⟨s, hs, he⟩ := hsub (by
    change localizedSpaceFunctor.map W.obj.hom t.val ∈ T
    rwa [← restrictEtale_hom_apply X U W.obj t])
  exact hj.injective he ▸ hs

/-- A proper étale cover with a singleton fibre over the chosen point
represents a pointed étale neighbourhood over the same base point. -/
def ofProper {A : EtaleSite X} (p : A ⟶ W.obj)
    (hp : IsProperMap (localizedSpaceFunctor.map p.left))
    (x : localizedSpaceFunctor.obj A.left) (hx : localizedSpaceFunctor.map p.left x = W.point)
    (hunique : ∀ z, localizedSpaceFunctor.map p.left z = W.point → z = x) :
    EtaleGermNeighborhood X y := by
  have hcomp (z : localizedSpaceFunctor.obj A.left) :
      localizedSpaceFunctor.map A.hom z =
        localizedSpaceFunctor.map W.obj.hom (localizedSpaceFunctor.map p.left z) := by
    rw [← localizedSpaceFunctor.map_comp_apply, MorphismProperty.Over.w p]
  refine ⟨A, x, (hcomp x).trans (hx ▸ W.map_point), ?_⟩
  intro B hB
  let Z := localizedSpaceFunctor.map p.left '' (B : Set _)ᶜ
  have hz : IsClosed Z := hp.isClosedMap _ B.isOpen.isClosed_compl
  have hw : W.point ∈ Zᶜ := by
    rintro ⟨z, hz, hzp⟩
    exact hz ((hunique z hzp).symm ▸ hB)
  obtain ⟨O, hy, hO⟩ := W.shrink ⟨Zᶜ, hz.isOpen_compl⟩ hw
  refine ⟨O, hy, fun z hzo => ?_⟩
  by_contra hz
  have hh : localizedSpaceFunctor.map p.left z ∈ Zᶜ := hO (by
    change localizedSpaceFunctor.map W.obj.hom (localizedSpaceFunctor.map p.left z) ∈ O
    rwa [← hcomp])
  exact hh ⟨z, hz, rfl⟩

end EtaleGermNeighborhood

variable {X} {y : localizedSpaceFunctor.obj X}

/-- An inclusion of two neighbourhood opens gives the arrow of indices. -/
def nbhdIndex.homOfLE {i j : nbhdIndex.{u, v, uL} X y}
    (h : (nbhdOpen X y).obj i ≤ (nbhdOpen X y).obj j) : i ⟶ j := by
  refine AsSmall.up.map (Functor.Elements.homMk (CategoryTheory.homOfLE h) ?_)
  apply ULift.ext
  rfl

variable (X) (y)

/-- The neighbourhood indices that are distinguished and contained in `U`. -/
def distinguishedNbhdProperty (U : Opens (localizedSpaceFunctor.obj X)) :
    ObjectProperty (nbhdIndex.{u, v, uL} X y) := fun i =>
  (nbhdOpen.{u, v, uL} X y).obj i ≤ U ∧
    IsDistinguishedOpen X ((nbhdOpen.{u, v, uL} X y).obj i : Set _)

abbrev distinguishedNbhdIndex (U : Opens (localizedSpaceFunctor.obj X)) :=
  (distinguishedNbhdProperty.{u, v, uL} X y U).FullSubcategory

section Basis

variable {X y}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : G →* Aut X}
variable [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ)

include hρ

/-- Below every ordinary neighbourhood index there is a distinguished
neighbourhood inside a prescribed open containing `y`. -/
theorem exists_distinguishedNbhdIndex {U : Opens (localizedSpaceFunctor.obj X)} (hU : y ∈ U)
    (i : nbhdIndex.{u, v, uL} X y) :
    ∃ j : distinguishedNbhdIndex.{u, v, uL} X y U, Nonempty (j.obj ⟶ i) := by
  let T := (nbhdOpen.{u, v, uL} X y).obj i
  have hTU : y ∈ (T ⊓ U : Opens _) := ⟨mem_nbhdOpen X y i, hU⟩
  obtain ⟨O, _, hO, hy, hsub, _, _⟩ := hasStableDistinguishedOpenNeighborhoods hρ y
    ((T ⊓ U : Opens _) : Set _) (T ⊓ U).isOpen hTU
  let V : Opens (localizedSpaceFunctor.obj X) := ⟨O, hO.1⟩
  have hV : V ≤ T ⊓ U := subset_closure.trans hsub
  let j : nbhdIndex.{u, v, uL} X y := nbhdIndex.mk V hy
  exact ⟨⟨j, hV.trans inf_le_right, hO⟩, ⟨nbhdIndex.homOfLE (hV.trans inf_le_left)⟩⟩

theorem distinguishedNbhdIndex_isCofiltered {U : Opens (localizedSpaceFunctor.obj X)} (hU : y ∈ U) :
    IsCofiltered (distinguishedNbhdIndex.{u, v, uL} X y U) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (distinguishedNbhdProperty X y U).ι (exists_distinguishedNbhdIndex hρ hU)

theorem distinguishedNbhdInclusion_initial {U : Opens (localizedSpaceFunctor.obj X)} (hU : y ∈ U) :
    ((distinguishedNbhdProperty.{u, v, uL} X y U).ι).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_distinguishedNbhdIndex hρ hU)

end Basis

end Langlands.Sheaf.Equivariant.Analytic
