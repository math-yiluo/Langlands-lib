/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Single.SingleComplexOpenUnionCompatibleChainData
import WeilConjectures.AlgebraicGeometry.Single.SingleComplexOpenUnionSESCompatibility

/-! # Chain-level comparison on a compact source-open union

## References

* Stacks Project, Cohomology, Tags 08HZ and 08HY
* Stacks Project, Tags 08HZ (relative Mayer--Vietoris), 08HY (the counit base-change construction),
  0DJ9 (the source-open induction diagram), and 013N--013O (the cylinder replacement and its
  homotopy equivalence)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A short-exact-complex presentation of the comparison diagram on a union.
This is a construction before forming connecting maps or distinguished triangles. -/
theorem singleComplexOpenComparison_union_ses_presentation
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
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ (a (U ⊔ V)).left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ (a (U ⊔ V)).right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (a (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ (a (U ⊔ V)).hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (a U).hom (a V).hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (a (U ⊓ V)).hom := by
  classical
  dsimp only
  let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
    Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
  obtain ⟨A, B, A', B', t, t', α, β, hc, e₁, e₂, e₃, e₁', e₂', e₃',
    hα, hβ, hγ⟩ :=
    singleComplexOpenComparison_union_compatible_chain_data f f' g g' sq K hK K' hK' φ
      U V hUqc hVqc hUVqc
  exact singleComplexOpenComparison_union_ses_compatibility A B A' B' t t' α β hc
    (a (U ⊔ V)).hom (biprod.map (a U).hom (a V).hom) (a (U ⊓ V)).hom
    e₁ e₂ e₃ e₁' e₂' e₃' hα hβ hγ

end AlgebraicGeometry
