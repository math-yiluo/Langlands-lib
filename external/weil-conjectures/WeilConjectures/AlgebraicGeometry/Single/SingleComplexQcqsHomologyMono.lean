/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenAffine
import WeilConjectures.AlgebraicGeometry.Single.SingleComplexOpenAffineUnion
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTop
import WeilConjectures.AlgebraicGeometry.SingleComplexTargetLocality

/-! # Degreewise monomorphism in qcqs single-complex base change

## References

* Stacks Project, Tag 0DJ9
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The monomorphism part in one degree of the qcqs single-complex stalk criterion. -/
theorem singleComplexBaseChange_homology_mono
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) n).map
        (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ)) := by
  have hIso : IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map φ) := by
    apply singleComplexBaseChange_targetLocal (f := f) (f' := f') (g := g) (g' := g')
      (sq := sq) (K := K) (hK := hK) (K' := K') (hK' := hK') (φ := φ) (h_stalk := h_stalk)
    intro X₀ X₀' S₀ S₀' f₀ f₀' g₀ g₀' sq₀ _ _ _ _ K₀ hK₀ K₀' hK₀' φ₀ hstalk₀
    let : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
    let : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated f₀
    let P : X₀.Opens → Prop := fun U ↦
      IsIso (singleComplexOpenComparison f₀ f₀' g₀ g₀' sq₀.w K₀ K₀' φ₀ U)
    have h_affine : ∀ U : X₀.Opens, IsAffineOpen U → P U := by
      intro U hU
      exact singleComplexOpenComparison_affine f₀ f₀' g₀ g₀' sq₀
        K₀ hK₀ K₀' hK₀' φ₀ hstalk₀ U hU
    have h_union : ∀ U V : X₀.Opens, IsCompact (U : Set X₀) → IsAffineOpen V →
        P U → P V → P (U ⊓ V) → P (U ⊔ V) := by
      intro U V hUqc hV hU hPV hUV
      exact singleComplexOpenComparison_affine_union f₀ f₀' g₀ g₀' sq₀
        K₀ hK₀ K₀' hK₀' φ₀ U V hUqc hV hU hPV hUV
    have htop : P ⊤ := quasiCompactOpen_induction X₀ P h_affine h_union ⊤
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X₀)))
    exact singleComplexOpenComparison_top f₀ f₀' g₀ g₀' sq₀.w K₀ K₀' φ₀ htop
  exact inferInstance

end AlgebraicGeometry
