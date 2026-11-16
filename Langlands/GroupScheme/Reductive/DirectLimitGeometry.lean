import Langlands.AlgebraicGeometry.DirectLimitLocus
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityProof
import Langlands.GroupScheme.Reductive.IdentityComponentLocusProof
import Langlands.GroupScheme.Reductive.IdentityComponentLocusBaseChange

/-! # Reductive and connected fibre loci over a direct limit of rings -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.GroupScheme

local instance directLimit_smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom b))

local instance directLimit_affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- The actual base changes of a group over one term of a directed ring system. -/
abbrev directedSystemBaseChange {ι : Type u} [Preorder ι]
    (A : ι ⥤ CommRingCat.{u}) (i₀ : ι) (G₀ : GroupScheme (Spec (A.obj i₀))) :
    ∀ i : ι, i₀ ≤ i → GroupScheme (Spec (A.obj i)) :=
  fun _ h => (baseChange (Spec.map (A.map (homOfLE h)))).obj G₀

/-- The reductive identity-component locus is full at the colimit exactly
when it is full at every sufficiently large stage. -/
theorem identityComponentReductiveLocus_eq_univ_iff_eventually
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A : ι ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : ι) (G₀ : GroupScheme (Spec (A.obj i₀)))
    [Smooth G₀.X.hom] [IsAffineHom G₀.X.hom] :
    identityComponentReductiveLocus ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) = Set.univ ↔
      ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i →
        identityComponentReductiveLocus (directedSystemBaseChange A i₀ G₀ i h) = Set.univ := by
  simpa only [directedSystemBaseChange, identityComponentReductiveLocus_baseChange] using
    Langlands.AlgebraicGeometry.spec_preimage_eq_univ_iff_eventually_of_isOpen A c hc i₀
      (identityComponentReductiveLocus G₀) (identityComponentReductiveLocusOpen _ G₀)

/-- Geometric connectedness of all fibres descends along the directed ring colimit. -/
theorem geometricallyConnected_baseChange_iff_eventually
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A : ι ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : ι) (G₀ : GroupScheme (Spec (A.obj i₀)))
    [Smooth G₀.X.hom] [IsAffineHom G₀.X.hom] :
    GeometricallyConnected ((baseChange (Spec.map (c.ι.app i₀))).obj G₀).X.hom ↔
      ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i →
        GeometricallyConnected (directedSystemBaseChange A i₀ G₀ i h).X.hom := by
  have hs := isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility
      geometricallyConnectedFiberLocalConstructibility
      G₀.X.hom
  have H := Langlands.AlgebraicGeometry.spec_preimage_eq_univ_iff_eventually_of_isConstructible
    A c hc i₀ _ hs
  have he {T : Scheme.{u}} (b : T ⟶ Spec (A.obj i₀)) :
      geometricallyConnectedFiberLocus ((baseChange b).obj G₀).X.hom =
        b ⁻¹' geometricallyConnectedFiberLocus G₀.X.hom :=
    geometricallyConnectedFiberLocus_baseChange (IsPullback.of_hasPullback _ _)
  simpa only [directedSystemBaseChange,
    ← geometricallyConnectedFiberLocus_eq_univ_iff, he] using H

end Langlands.GroupScheme
