/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Single.SingleComplexOpenUnionTriangles

/-! # The affine-adjoining step of single-complex source-open induction

## References

* Stacks Project, Tag 0DJ9, induction step
* Stacks Project, Tag 0DJ9, induction step, applied inside `U ⊔ V`
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Gluing the comparison after adjoining one affine open. -/
theorem singleComplexOpenComparison_affine_union
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVaff : IsAffineOpen V)
    (hU : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U))
    (hV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ V))
    (hUV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊓ V))) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊔ V)) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hVqc : IsCompact (V : Set X) := hVaff.isCompact
  have hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
      U.isOpen hUqc V.isOpen hVqc
  obtain ⟨d₁, d₂, d₃, d₁', d₂', d₃', hT, hT', t, ht₁, ht₂, ht₃⟩ :=
    singleComplexOpenComparison_union_triangles f f' g g' sq K hK K' hK' φ
      U V hUqc hVqc hUVqc
  have hb : IsIso (biprod.map
      (singleComplexOpenComparison f f' g g' sq.w K K' φ U)
      (singleComplexOpenComparison f f' g g' sq.w K K' φ V)) := by
    let := hU
    let := hV
    change IsIso (biprod.mapIso
      (asIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U))
      (asIso (singleComplexOpenComparison f f' g g' sq.w K K' φ V))).hom
    infer_instance
  have h₂ : IsIso t.hom₂ := ht₂.symm ▸ hb
  have h₃ : IsIso t.hom₃ := ht₃.symm ▸ hUV
  have h₁ := Pretriangulated.isIso₁_of_isIso₂₃ t hT hT' h₂ h₃
  rw [ht₁] at h₁
  exact h₁

end AlgebraicGeometry
