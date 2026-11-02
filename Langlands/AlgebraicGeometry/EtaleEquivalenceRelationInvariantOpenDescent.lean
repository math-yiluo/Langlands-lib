import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpen
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianDiagram
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Invariant affine covers at a finite level of a cartesian diagram -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.CartesianDiagram

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D)

attribute [local instance] IsCofiltered.isConnected

/-- An object limit of cartesian relation morphisms is also a relation limit. -/
noncomputable def isLimitRelation [IsCofiltered I]
    (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (relationFunctor.mapCone c) :=
  isLimitOfIsPullbackOfIsConnected (Functor.whiskerLeft D sourceTransformation)
    (relationFunctor.mapCone c) (objectFunctor.mapCone c)
    { hom := c.pt.s
      w := fun i => (c.π.app i).isCartesian.2.w.symm }
    (fun i => (c.π.app i).isCartesian.2) hc

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
  (hc : IsLimit (objectFunctor.mapCone c))

include hc in
/-- An affine open at a given level whose inverse image is invariant
becomes invariant after a transition. -/
lemma exists_isInvariantOpen_preimage {i : I} (V : (D.obj i).U.Opens)
    (hV : IsAffineOpen V)
    (h : c.pt.IsInvariantOpen ((c.π.app i).objMap ⁻¹ᵁ V)) :
    ∃ (j : I) (a : j ⟶ i),
      (D.obj j).IsInvariantOpen ((D.map a).objMap ⁻¹ᵁ V) := by
  have (i : I) : IsAffine ((D ⋙ relationFunctor).obj i) :=
    inferInstanceAs (IsAffine (D.obj i).R)
  have hsource : IsCompact (((D.obj i).s ⁻¹ᵁ V) : Set (D.obj i).R) :=
    QuasiCompact.isCompact_preimage _ V.2 hV.isCompact
  have htarget : IsCompact (((D.obj i).t ⁻¹ᵁ V) : Set (D.obj i).R) :=
    QuasiCompact.isCompact_preimage _ V.2 hV.isCompact
  have heq : (c.π.app i).relMap ⁻¹ᵁ ((D.obj i).s ⁻¹ᵁ V) =
      (c.π.app i).relMap ⁻¹ᵁ ((D.obj i).t ⁻¹ᵁ V) := by
    change c.pt.s ⁻¹ᵁ ((c.π.app i).objMap ⁻¹ᵁ V) =
      c.pt.t ⁻¹ᵁ ((c.π.app i).objMap ⁻¹ᵁ V) at h
    rw [← Scheme.Hom.comp_preimage, (c.π.app i).isCartesian.2.w,
      Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage (c.π.app i).relMap,
      (c.π.app i).isCartesian.1, Scheme.Hom.comp_preimage]
    simpa only [Functor.const_obj_obj] using h
  obtain ⟨j, a, ha⟩ := exists_map_preimage_eq_map_preimage
    (D ⋙ relationFunctor) (relationFunctor.mapCone c) (isLimitRelation D c hc)
    hsource htarget heq
  refine ⟨j, a, ?_⟩
  change (D.map a).relMap ⁻¹ᵁ ((D.obj i).s ⁻¹ᵁ V) =
    (D.map a).relMap ⁻¹ᵁ ((D.obj i).t ⁻¹ᵁ V) at ha
  change (D.obj j).s ⁻¹ᵁ ((D.map a).objMap ⁻¹ᵁ V) =
    (D.obj j).t ⁻¹ᵁ ((D.map a).objMap ⁻¹ᵁ V)
  simpa only [← Scheme.Hom.comp_preimage, (D.map a).isCartesian.2.w,
    (D.map a).isCartesian.1] using ha

include hc in
/-- An invariant affine open of the limit descends as an invariant affine open. -/
lemma exists_isAffineOpen_isInvariantOpen_preimage_eq
    (U : c.pt.U.Opens) (hU : IsAffineOpen U) (h : c.pt.IsInvariantOpen U) :
    ∃ (i : I) (V : (D.obj i).U.Opens),
      IsAffineOpen V ∧ (D.obj i).IsInvariantOpen V ∧
        (c.π.app i).objMap ⁻¹ᵁ V = U := by
  have (i : I) : IsAffine ((D ⋙ objectFunctor).obj i) :=
    inferInstanceAs (IsAffine (D.obj i).U)
  obtain ⟨i, V, hV, hVU⟩ := exists_isAffineOpen_preimage_eq
    (D ⋙ objectFunctor) (objectFunctor.mapCone c) hc U hU
  change (D.obj i).U.Opens at V
  change (c.π.app i).objMap ⁻¹ᵁ V = U at hVU
  obtain ⟨j, a, ha⟩ := exists_isInvariantOpen_preimage D c hc V hV (by
    rwa [hVU])
  refine ⟨j, (D.map a).objMap ⁻¹ᵁ V, hV.preimage _, ha, ?_⟩
  rw [← Scheme.Hom.comp_preimage, ← comp_objMap, c.w a]
  exact hVU

include hc in
/-- A finite invariant affine cover of the limit descends to a single level,
retaining its members, affineness, invariance, and covering property. -/
lemma exists_invariantAffineCover {K : Type u} [Finite K]
    (U : K → c.pt.U.Opens) (hcover : IsOpenCover U)
    (hU : ∀ k, IsAffineOpen (U k)) (hinv : ∀ k, c.pt.IsInvariantOpen (U k)) :
    ∃ (i : I) (V : K → (D.obj i).U.Opens),
      IsOpenCover V ∧ ∀ k, IsAffineOpen (V k) ∧
        (D.obj i).IsInvariantOpen (V k) ∧ U k = (c.π.app i).objMap ⁻¹ᵁ V k := by
  classical
  have (i : I) : IsAffine ((D ⋙ objectFunctor).obj i) :=
    inferInstanceAs (IsAffine (D.obj i).U)
  obtain ⟨i, V, hVcover, hV⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite
    (D ⋙ objectFunctor) (objectFunctor.mapCone c) hc U hcover hU
  change K → (D.obj i).U.Opens at V
  change ∀ k, IsAffineOpen (V k) ∧ U k = (c.π.app i).objMap ⁻¹ᵁ V k at hV
  have hi (k : K) : c.pt.IsInvariantOpen ((c.π.app i).objMap ⁻¹ᵁ V k) := by
    rw [← (hV k).2]
    exact hinv k
  choose j a hj using fun k =>
    exists_isInvariantOpen_preimage D c hc (V k) (hV k).1 (hi k)
  obtain ⟨l, fli, g, hg⟩ := IsCofiltered.wideCospan a
  refine ⟨l, fun k => (D.map fli).objMap ⁻¹ᵁ V k, ?_, fun k => ?_⟩
  · change (⨆ k, (D.map fli).objMap ⁻¹ᵁ V k) = ⊤
    rw [← Scheme.Hom.preimage_iSup, hVcover, Scheme.Hom.preimage_top]
  · refine ⟨(hV k).1.preimage _, ?_, ?_⟩
    · have hw : (D.map fli).objMap ⁻¹ᵁ V k =
          (D.map (g k)).objMap ⁻¹ᵁ ((D.map (a k)).objMap ⁻¹ᵁ V k) := by
        rw [← Scheme.Hom.comp_preimage, ← comp_objMap, ← D.map_comp, hg k]
      change (D.obj l).IsInvariantOpen ((D.map fli).objMap ⁻¹ᵁ V k)
      rw [hw]
      exact (D.map (g k)).isCartesian.isInvariantOpen_preimage (hj k)
    · rw [← Scheme.Hom.comp_preimage, ← comp_objMap, c.w fli]
      exact (hV k).2

/-- The actual finite-level data of an invariant affine cover. -/
structure InvariantAffineCoverModel {K : Type u} (U : K → c.pt.U.Opens) where
  index : I
  opens : K → (D.obj index).U.Opens
  isCover : IsOpenCover opens
  isAffine : ∀ k, IsAffineOpen (opens k)
  isInvariant : ∀ k, (D.obj index).IsInvariantOpen (opens k)
  preimage_eq : ∀ k, U k = (c.π.app index).objMap ⁻¹ᵁ opens k

/-- Choose one level and its finite invariant affine cover. -/
noncomputable def invariantAffineCoverModel {K : Type u} [Finite K]
    (U : K → c.pt.U.Opens) (hcover : IsOpenCover U)
    (hU : ∀ k, IsAffineOpen (U k)) (hinv : ∀ k, c.pt.IsInvariantOpen (U k)) :
    InvariantAffineCoverModel D c U :=
  Classical.choice (by
    obtain ⟨i, V, hVcover, hV⟩ := exists_invariantAffineCover D c hc U hcover hU hinv
    exact ⟨⟨i, V, hVcover, fun k => (hV k).1,
      fun k => (hV k).2.1, fun k => (hV k).2.2⟩⟩)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.CartesianDiagram
