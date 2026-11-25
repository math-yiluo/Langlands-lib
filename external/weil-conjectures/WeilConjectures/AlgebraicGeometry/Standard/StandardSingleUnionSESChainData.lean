/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleUnionHomotopyChainData
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopySquareRectification

/-! # Chain representatives of the single-module union comparison

Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private lemma transport_comparison
    {E : Type*} [Category E] {X Y Z X' Z' : E}
    (e : X ≅ Y) (e₂ : Y ≅ Z) (e₂' : X' ≅ Z')
    {b : X ⟶ X'} {β : Y ⟶ X'} {f : Z ⟶ Z'}
    (hb : b = e.hom ≫ β) (hβ : β ≫ e₂'.hom = e₂.hom ≫ f) :
    b ≫ e₂'.hom = (e ≪≫ e₂).hom ≫ f := by
  calc
    b ≫ e₂'.hom = (e.hom ≫ β) ≫ e₂'.hom := congrArg (· ≫ e₂'.hom) hb
    _ = e.hom ≫ (β ≫ e₂'.hom) := Category.assoc _ _ _
    _ = e.hom ≫ (e₂.hom ≫ f) := congrArg (e.hom ≫ ·) hβ
    _ = (e ≪≫ e₂).hom ≫ f := (Category.assoc _ _ _).symm

-- Rectify abstract chain representatives without unfolding the geometric vertices.
private theorem unionHomotopyChainData_rectify
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    {a aU aV aUV : Arrow (DerivedCategory E)}
    (h : ∃ (C D C' D' : CochainComplex E ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom) :
    ∃ (C D C' D' : CochainComplex E ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (hc : t ≫ β = α ≫ t')
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by
  obtain ⟨C, D, C', D', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hcone⟩ := h
  obtain ⟨T, i, b, hc, d₂, d₃, hb, hq⟩ :=
    CochainComplex.homotopy_square_cone_rectification t t' α β H
  refine ⟨C, T, C', D', i, t', α, b, hc, e₁, d₂ ≪≫ e₂, d₃ ≪≫ e₃,
    e₁', e₂', e₃', hα, ?_, ?_⟩
  · exact transport_comparison d₂ e₂ e₂' hb hβ
  · exact transport_comparison d₃ e₃ e₃' hq hcone

set_option backward.isDefEq.respectTransparency false in
/-- A strict first-map square whose cones represent the overlap comparisons.
Unlike a short exact presentation, this asserts no monomorphism, epimorphism,
short complex or exactness of complexes on A.

Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY, 0DJ9, 013N--013O.
(blueprint: new-pc-standard-single-union-ses-chain-data).

Proof:
Set W = U union V and form its cartesian base change W_A. The opens induced
by U and V cover W, and their inverse images cover W_A. Choose K-injective
resolutions with injective terms of N[0] and of its ordinary pullback in degree
zero. For each cover form the restriction-pair and restriction-difference row.
Sheaf gluing proves exactness at the first two terms, and flasqueness of injective
module sheaves makes the difference map surjective. Thus the cone of the first
map represents the overlap term, with the usual difference sign.
Relative Mayer--Vietoris (Tag 08HZ) computes the two direct-image
cover diagrams functorially. Apply derived pullback to the source diagram.
These functors are triangulated and additive. Represent the finite diagrams by
complexes using diagram resolutions (K-flat for the source
pullback and K-injective for direct images). The counit from derived to ordinary
pullback of N[0], transposed under the derived adjunction, gives the comparison
of these two diagrams. Restriction-unit naturality and the underived open
counit square give its compatibility with the restriction maps, including the
specified homotopies. Rectify the first square by replacing its representatives
by functorial cylinders; carry the specified homotopies into the induced cone
map. Use the comparison of resolved cover diagrams, including its homotopies,
rather than an arbitrary completion of a square in the triangulated category:
that completion alone would not identify the prescribed overlap map. This gives
t, t', alpha and beta with a strict commuting square and ensures
that its functorial cone map represents the original overlap comparison.
Exact open restriction identifies the coefficients with the literal tensor
pullbacks displayed below. Direct-image composition and the additive biproduct
comparison give the six vertex isomorphisms. Expand each base-change map as the
mate of the pulled-back direct-image counit followed by the single-complex
pullback counit. The composite-counit identity and adjunction triangle identities
identify the first component with the union comparison, the middle component
with the biproduct of the two member comparisons, and the cone component with
the overlap comparison. This gives the three conjugacy equations.
Empty opens give zero terms. Repeated or contained opens give split restriction
rows. Zero coefficients give zero rows. All choices are existential witnesses,
not definitions of data from an unproved existence theorem. -/
theorem standardSingle_union_ses_chain_data
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (hc : t ≫ β = α ≫ t')
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact unionHomotopyChainData_rectify (standardSingle_union_homotopy_chain_data p g U V N)

end AlgebraicGeometry
