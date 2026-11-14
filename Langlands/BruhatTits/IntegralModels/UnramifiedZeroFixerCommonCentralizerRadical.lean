import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerRadical

/-! # One common centralizer radical subgroup for all zero-fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

/-- One subgroup, chosen before all facets, models and represented radicals,
is the centralizer part of every upstairs radical preimage. -/
theorem exists_unramifiedZeroFixerCommonCentralizerRadical
    (hinter : TorusCentralizerUnipotentRadicalStatement.{u}) :
    ∃ H : Subgroup (rationalPoints G),
      H ≤ (rationalPoints.map C.centralizer.j).range ∧
      H ≤ E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap) ∧
      ∀ (Ω : Set C.Apartment), Ω.Nonempty →
        (∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) →
      ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
        N.IsSmooth →
        N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      ∀ (U : GroupScheme
          (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ N.specialFibre), IsUnipotentRadical i →
        (((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap) ⊓
          (rationalPoints.map C.centralizer.j).range = H := by
  classical
  rcases Classical.em (∃ (Ω : Set C.Apartment)
      (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
      Ω.Nonempty ∧
      (∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) ∧
      N.IsSmooth ∧
      N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) with hex | hex
  · obtain ⟨Ω₀, N₀, hne₀, hfacet₀, hSmooth₀, hN₀⟩ := hex
    let : Smooth N₀.group.X.hom := hSmooth₀
    obtain ⟨V₀, v₀, hv₀⟩ :=
      unramifiedZeroFixerCentralizer_exists_radical C E N₀ Ω₀ hN₀ hne₀ hfacet₀
    let P₀ := unramifiedZeroFixerCentralizerModel C E N₀ Ω₀ hN₀
    let K₀ := ((rationalPoints.map v₀).range.comap P₀.reduction).map P₀.integralPointMap
    let f := rationalPoints.map C.centralizer.j
    refine ⟨K₀.map f, ?_, ?_, ?_⟩
    · exact K₀.map_le_range f
    · rintro g ⟨z, hz, rfl⟩
      have hzint : z ∈ P₀.integralPoints := by
        obtain ⟨s, _, rfl⟩ := hz
        exact ⟨s, rfl⟩
      have hg := (unramifiedZeroFixerCentralizerModelMap C E N₀ Ω₀ hN₀).map_mem_integralPoints
        hzint
      rw [hN₀] at hg
      refine ⟨hg.1, ?_⟩
      obtain ⟨x, hx⟩ := hne₀
      have hfix := C.map_centralizer_mem_pointwiseFixer_of_smul_eq z x
        (C.apartment.mem_pointwiseFixer.mp hg.2 _ ⟨x, hx, rfl⟩) Set.univ
      change rationalPoints.map C.centralizer.j z ∈
        C.pointwiseFixer (Set.range C.apartmentMap)
      simpa only [Set.image_univ] using hfix
    · intro Ω hne hfacet N hSmooth hN U i hi
      let : Smooth N.group.X.hom := hSmooth
      obtain ⟨V, v, hv⟩ :=
        unramifiedZeroFixerCentralizer_exists_radical C E N Ω hN hne hfacet
      have hind := unramifiedZeroFixerCentralizer_radicalPreimage_eq C E N₀ N Ω₀ Ω
        hN₀ hN hne₀ hne v₀ v hv₀ hv
      have hcomp := unramifiedZeroFixerCentralizer_radicalPreimage_comap C E N Ω hN
        hinter hne hfacet i v hi hv
      let B := ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap
      change B ⊓ f.range = K₀.map f
      calc
        B ⊓ f.range = f.range ⊓ B := inf_comm _ _
        _ = (B.comap f).map f := (Subgroup.map_comap_eq f B).symm
        _ = K₀.map f := congrArg (fun J => J.map f) (hind.trans hcomp).symm
  · refine ⟨⊥, bot_le, bot_le, ?_⟩
    intro Ω hne hfacet N hSmooth hN U i hi
    exact (hex ⟨Ω, N, hne, hfacet, hSmooth, hN⟩).elim

/-- Conditional common-subgroup reduction: the exact torus-centralizer radical
intersection theorem supplies one centralizer subgroup for every model and radical. -/
def UnramifiedZeroFixerCommonCentralizerRadicalStatement : Prop :=
  TorusCentralizerUnipotentRadicalStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G),
    ∃ H : Subgroup (rationalPoints G),
      H ≤ (rationalPoints.map C.centralizer.j).range ∧
      H ≤ E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap) ∧
      ∀ (Ω : Set C.Apartment), Ω.Nonempty →
        (∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) →
      ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
        N.IsSmooth →
        N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      ∀ (U : GroupScheme
          (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ N.specialFibre), IsUnipotentRadical i →
        (((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap) ⊓
          (rationalPoints.map C.centralizer.j).range = H

/-- The conditional common-centralizer-subgroup reduction is proved. -/
theorem unramifiedZeroFixerCommonCentralizerRadical :
    UnramifiedZeroFixerCommonCentralizerRadicalStatement.{u} := by
  intro hinter F _ _ _ _ G _ C E
  exact exists_unramifiedZeroFixerCommonCentralizerRadical C E hinter

end Langlands.BruhatTits.IntegralModels
