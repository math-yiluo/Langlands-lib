import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Shrinking finite-set affine neighborhoods inside open subschemes -/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Every finite set in a specified open of an AF scheme has an affine
neighborhood contained in that open. -/
def FiniteAffineNeighborhoodsOpenShrinkingStatement : Prop :=
  ∀ (X : Scheme.{u}), HasFiniteAffineNeighborhoods X →
    ∀ (E : Set X) (W : X.Opens), E.Finite → E ⊆ W →
      ∃ V : X.affineOpens, E ⊆ V.val ∧ V.val ≤ W

/-- Shrink the affine neighborhood of a finite set within a specified open. -/
theorem exists_affineOpen_subset_of_finite
    {X : Scheme.{u}} (hX : HasFiniteAffineNeighborhoods X)
    (E : Set X) (W : X.Opens) (hE : E.Finite) (hEW : E ⊆ W) :
    ∃ V : X.affineOpens, E ⊆ V.val ∧ V.val ≤ W := by
  obtain ⟨U, hEU⟩ := hX E hE
  let T : X.Opens := U.val
  let : IsAffine T.toScheme := U.property
  have hE' : (T.ι ⁻¹' E).Finite :=
    hE.preimage T.ι.isOpenEmbedding.injective.injOn
  obtain ⟨r, hEr, hrW⟩ := GenericPointAvoidance.exists_basicOpen_of_finite
    (X := T.toScheme) hE' (W := T.ι ⁻¹ᵁ W) (fun _ hx => hEW hx)
  let V : X.Opens := T.ι ''ᵁ T.toScheme.basicOpen r
  refine ⟨⟨V, ((isAffineOpen_top T.toScheme).basicOpen r).image_of_isOpenImmersion
    T.ι⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hEU hx⟩, hEr hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hrW hx

/-- The finite-set shrinking proposition holds in every universe. -/
theorem finiteAffineNeighborhoodsOpenShrinking :
    FiniteAffineNeighborhoodsOpenShrinkingStatement.{u} := by
  intro X hX E W hE hEW
  exact exists_affineOpen_subset_of_finite hX E W hE hEW

/-- The AF condition passes to an arbitrary open subscheme. -/
theorem hasFiniteAffineNeighborhoods_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (hY : HasFiniteAffineNeighborhoods Y) :
    HasFiniteAffineNeighborhoods X := by
  intro E hE
  obtain ⟨V, hEV, hV⟩ := exists_affineOpen_subset_of_finite hY
    (f '' E) f.opensRange (hE.image f) (Set.image_subset_range _ _)
  refine ⟨⟨f ⁻¹ᵁ V.val, V.property.preimage_of_isOpenImmersion f hV⟩, ?_⟩
  intro x hx
  exact hEV ⟨x, hx, rfl⟩

/-- Every open of an AF scheme is AF, with no compactness assumption. -/
theorem hasFiniteAffineNeighborhoods_open
    {X : Scheme.{u}} (hX : HasFiniteAffineNeighborhoods X) (W : X.Opens) :
    HasFiniteAffineNeighborhoods W.toScheme :=
  hasFiniteAffineNeighborhoods_of_isOpenImmersion W.ι hX

/-- A compact open contained in an affine chart is quasi-affine. -/
theorem isQuasiAffine_of_le_affineOpen
    {X : Scheme.{u}} (U : X.affineOpens) (V : X.Opens)
    (hVU : V ≤ U.val) (hV : IsCompact (V : Set X)) :
    V.toScheme.IsQuasiAffine := by
  let : IsAffine U.val.toScheme := U.property
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  exact Scheme.IsQuasiAffine.of_isImmersion (X.homOfLE hVU)

end Langlands.AlgebraicGeometry.PointTopology
