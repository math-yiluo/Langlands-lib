import Langlands.GroupScheme.RelativeIdentityComponent.ProductImage
import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover
import Langlands.GroupScheme.RelativeIdentityComponent.SectionComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Fiber

/-! # Quasi-compactness of group schemes from their residue fibres -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- If an open subscheme contains the unit at `s` and the residue fibre at `s` is smooth,
every point of the identity component of that fibre is a product of two points of the
open subscheme. -/
theorem fiberι_mem_range_product {P : Over S} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (s : S) [Smooth (residueFiber G s).X.hom] (he : unitSection G s ∈ Set.range i.left)
    {y : (residueFiber G s).X.left}
    (hy : y ∈ IdentityComponent.identitySet (residueFiber G s)) :
    G.X.hom.fiberι s y ∈ Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) := by
  let j := (Over.pullback (S.fromSpecResidueField s)).map i
  have : IsOpenImmersion j.left :=
    MorphismProperty.of_isPullback
      (overPullback_isPullback (S.fromSpecResidueField s) i).flip
      (inferInstance : IsOpenImmersion i.left)
  have hj : IdentityComponent.identityPoint (residueFiber G s) ∈ Set.range j.left := by
    rw [range_of_isPullback (overPullback_isPullback (S.fromSpecResidueField s) i)]
    change G.X.hom.fiberι s (IdentityComponent.identityPoint (residueFiber G s)) ∈
      Set.range i.left
    rw [← fiberPoint_unit G s, SectionComponent.fiberι_fiberPoint]
    exact he
  have hmem := identitySet_subset_range_fieldOpenProduct (residueFiber G s) j hj hy
  change y ∈ Set.range (baseChangedProduct G (S.fromSpecResidueField s) i).left at hmem
  rw [range_baseChangedProduct] at hmem
  exact hmem

/-- Over a quasi-separated base, a group scheme whose residue fibres are smooth, connected
and quasi-compact has quasi-compact structure morphism. -/
theorem quasiCompact_of_residueFibers [QuasiSeparatedSpace S]
    (hsmooth : ∀ s : S, Smooth (residueFiber G s).X.hom)
    (hconn : ∀ s : S, ConnectedSpace (G.X.hom.fiber s))
    (hcpt : ∀ s : S, CompactSpace (G.X.hom.fiber s)) :
    QuasiCompact G.X.hom := by
  let f := G.X.hom
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun s => ?_
  -- The topological fibre over `s` is compact.
  have hK : IsCompact (f ⁻¹' {s}) := by
    rw [← Scheme.Hom.range_fiberι]
    have := hcpt s
    exact isCompact_range (f.fiberι s).continuous
  -- A compact open neighbourhood `W` of that fibre.
  obtain ⟨W, hWc, hWo, hKW, -⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    hK isOpen_univ (Set.subset_univ _)
  let W' : G.X.left.Opens := ⟨W, hWo⟩
  have hes : unitSection G s ∈ W := hKW (by
    change f (unitSection G s) = s
    rw [← Scheme.Hom.comp_apply, unitSection_comp]
    rfl)
  -- An affine neighbourhood `V` of `s` whose unit section lies in `W`.
  obtain ⟨V, hV, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (U := (unitSection G) ⁻¹ᵁ W') hes
  -- The open subscheme `W ∩ f⁻¹ V`, as a quasi-compact scheme over `S`.
  let g : W'.toScheme ⟶ S := W'.ι ≫ f
  have : CompactSpace W'.toScheme := isCompact_iff_compactSpace.mp hWc
  let Q : W'.toScheme.Opens := g ⁻¹ᵁ V
  have : CompactSpace Q.toScheme :=
    isCompact_iff_compactSpace.mp (g.isCompact_preimage hV.isCompact)
  let P : Over S := Over.mk (Q.ι ≫ g)
  let i : P ⟶ G.X := Over.homMk (Q.ι ≫ W'.ι)
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (Q.ι ≫ W'.ι))
  have hPV : ∀ z : P.left, P.hom z ∈ V := fun z => z.2
  -- The unit section over `V` lands in `P`.
  have hunit : ∀ t ∈ V, unitSection G t ∈ Set.range i.left := by
    intro t ht
    have htW : unitSection G t ∈ W := hVW ht
    let w : W'.toScheme := ⟨unitSection G t, htW⟩
    have hw : g w ∈ V := by
      change f (unitSection G t) ∈ V
      rw [← Scheme.Hom.comp_apply, unitSection_comp]
      exact ht
    exact ⟨⟨w, hw⟩, rfl⟩
  -- The product of two copies of `P` is quasi-compact.
  have : CompactSpace P.left := inferInstanceAs (CompactSpace Q.toScheme)
  have : QuasiCompact P.hom := quasiCompact_of_compactSpace _
  have : CompactSpace (P ⊗ P).left :=
    inferInstanceAs (CompactSpace (pullback P.hom P.hom : Scheme.{u}))
  let m := ((i ⊗ₘ i) ≫ μ[G.X]).left
  have hrange : f ⁻¹' (V : Set S) = Set.range m := by
    ext y
    constructor
    · intro hy
      let t : S := f y
      obtain ⟨y', hy'⟩ : y ∈ Set.range (f.fiberι t) := by
        rw [Scheme.Hom.range_fiberι]
        rfl
      have := hsmooth t
      have : ConnectedSpace (residueFiber G t).X.left := hconn t
      have hid : y' ∈ IdentityComponent.identitySet (residueFiber G t) := by
        rw [IdentityComponent.identitySet, PreconnectedSpace.connectedComponent_eq_univ]
        trivial
      rw [← hy']
      exact fiberι_mem_range_product G i t (hunit t hy) hid
    · rintro ⟨z, rfl⟩
      have hw : m ≫ f = (P ⊗ P).hom := Over.w ((i ⊗ₘ i) ≫ μ[G.X])
      have hfst : (fst P P).left ≫ P.hom = (P ⊗ P).hom := Over.w (fst P P)
      change (m ≫ f) z ∈ V
      rw [hw, ← hfst, Scheme.Hom.comp_apply]
      exact hPV _
  have hcomp : IsCompact (f ⁻¹' (V : Set S)) := by
    rw [hrange]
    exact isCompact_range m.continuous
  refine ⟨V, hsV, ?_⟩
  have : IsAffine V.toScheme := hV
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
  exact isCompact_iff_compactSpace.mp hcomp

end Langlands.GroupScheme.RelativeIdentityComponent
