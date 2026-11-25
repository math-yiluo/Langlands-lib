/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.RelativeMVSESPresentation

/-! # Compatible relative Mayer--Vietoris boundaries

Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Complete the fixed relative restriction sequences by compatible boundaries.
This asserts distinguishedness and only the connecting square; it does not assert
commutativity of either restriction square.
Source: Stacks Project, Cohomology, Tags 08BV and 08HZ; Tag 0DJ9, induction diagram
(blueprint: lem-pc-relative-mv-boundary-completion).
Proof: The qcqs morphisms f and its base change over the affine bases have qcqs
sources. The base change g' of the affine morphism g is affine. Its inverse images
of U, V and their overlap are quasi-compact. Use the functorial K-injective
Mayer--Vietoris construction for these two covers. Identify exact open restriction
with derived pullback by its derived universal property and the canonical
underived open-pullback comparison. Identify composite direct images by the
right-adjoint mates of the same pinned pullback composition comparisons. Thus the
first two maps become exactly relativeMVSourceFirst/Second and
relativeMVTargetFirst/Second. Apply the triangulated functors Lg* Rf* and Rf'* and
transport the boundaries as well as the first two arrows along these comparisons
and the additive biproduct comparisons. This proves the two distinguishedness
claims. Transpose the object map under Lg'* adjoint to Rg'*. Functoriality of the
K-injective short-exact-sequence boundary, and compatibility of this construction
with direct image, give its boundary square. Transpose back using the
shift-compatible derived adjunction. The mates calculation of Tag 08HY and
associativity of pullback composition identify the overlap component with the
specified local arrow, including the equality transport of the pullback
projections; the global component is the specified base-change composite.
The zero terms for empty opens and zero complexes satisfy the same construction.
No invertibility of the object map or of any base-change map is used. -/
theorem relativeMV_boundary_completion
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
    ∃ (δ : (a (U ⊓ V)).left ⟶ aX.left⟦(1 : ℤ)⟧)
      (δ' : (a (U ⊓ V)).right ⟶ aX.right⟦(1 : ℤ)⟧),
      Triangle.mk (relativeMVSourceFirst f g U V K)
        (relativeMVSourceSecond f g U V K) δ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk (relativeMVTargetFirst g' f' U V K')
        (relativeMVTargetSecond g' f' U V K') δ' ∈ distTriang (schemeDerivedCategory S') ∧
      δ ≫ aX.hom⟦(1 : ℤ)⟧' = (a (U ⊓ V)).hom ≫ δ' := by
  classical
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', hf, hg, hf', hg', h₁, h₃⟩ :=
    relativeMV_ses_presentation f f' g g' hpull K K' φ
      U V hcover
  let δ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧'
  let δ' := e₃'.inv ≫ DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧'
  refine ⟨δ, δ', ?_, ?_, ?_⟩
  · apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP)
    refine (Triangle.isoMk _ _ e₁ e₂ e₃ hf hg ?_).symm
    change DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ
    simp only [δ, Iso.hom_inv_id_assoc]
  · apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP')
    refine (Triangle.isoMk _ _ e₁' e₂' e₃' hf' hg' ?_).symm
    change DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧' = e₃'.hom ≫ δ'
    simp only [δ', Iso.hom_inv_id_assoc]
  · have hn := DerivedCategory.triangleOfSESδ_naturality hP hP' m
    have hshift := congrArg (fun t ↦ t⟦(1 : ℤ)⟧') h₁
    simp only [Functor.map_comp] at hshift
    have h₃inv : e₃.inv ≫ DerivedCategory.Q.map m.τ₃ =
        (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom ≫ e₃'.inv := by
      apply (cancel_mono e₃'.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h₃]
      simp only [Iso.inv_hom_id_assoc]
    dsimp only [δ, δ']
    simp only [Category.assoc]
    rw [← hshift, ← Category.assoc (DerivedCategory.triangleOfSESδ hP), hn]
    simp only [← Category.assoc]
    rw [h₃inv]

end AlgebraicGeometry
