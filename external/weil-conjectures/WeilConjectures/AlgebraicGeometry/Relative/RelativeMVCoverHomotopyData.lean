/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVCoverRows
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # Resolved relative comparison on a two-open cover

## References

* Stacks Project, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A relative comparison on a covering pair, before identifying any coefficients
with modules in degree zero. -/
theorem relativeMV_cover_homotopy_data
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ (b U).left ⊞ (b V).left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ (b (U ⊓ V)).left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ (b U).right ⊞ (b V).right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ (b (U ⊓ V)).right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom =
          e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ (b (U ⊓ V)).hom := by
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', hα, hU, hV, hγ⟩ :=
    relativeMV_cover_rows f f' g g' hpull K K' φ U V hcover
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP'
  let d := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P))
  let d' := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P'))
  refine ⟨P.X₁, P.X₂, P'.X₁, P'.X₂, P.f, P'.f, m.τ₁, m.τ₂,
    Homotopy.ofEq m.comm₁₂.symm, e₁, e₂, d ≪≫ e₃, e₁', e₂', d' ≪≫ e₃',
    hα, ?_, ?_⟩
  · apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.map_fst] using hU
    · simpa only [Category.assoc, biprod.map_snd] using hV
  · dsimp only [Iso.trans_hom, d, d', asIso_hom]
    have h := congrArg (fun k ↦ DerivedCategory.Q.map k ≫ e₃'.hom)
      (CochainComplex.mappingCone.map_descShortComplex P P' m)
    simpa only [CochainComplex.mappingCone.map_eq_mapOfHomotopy,
      Functor.map_comp, Category.assoc, hγ] using h

end AlgebraicGeometry
