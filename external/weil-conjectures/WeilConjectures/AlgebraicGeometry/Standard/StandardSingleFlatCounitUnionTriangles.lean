/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleUnionSESPresentation

/-! # The union comparison as a morphism of distinguished triangles

Source: Stacks Project, Tags 0DJ9, 08BV and 08FE.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionTriangles_flatOver_of_iso
    {X S : Scheme.{u}} (f : X ⟶ S) {G H : X.Modules} (eGH : G ≅ H)
    (hflat : H.IsFlatOver f) : G.IsFlatOver f := by
  intro V U e
  let φ := (f.appLE V.1 U.1 e).hom
  let : Module Γ(S, V.1) Γ(G, U.1) := Module.compHom _ φ
  let : Module Γ(S, V.1) Γ(H, U.1) := Module.compHom _ φ
  let E := (ModuleCat.restrictScalars φ).mapIso
    ((SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op U.1)).mapIso eGH)
  exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr (hflat V U e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionTriangles_flatOver_restrict
    {X Y S : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a] (f : Y ⟶ S)
    (F : Y.Modules) (hflat : F.IsFlatOver f) : (F.restrict a).IsFlatOver (a ≫ f) := by
  intro V U e
  let U' : Y.affineOpens := ⟨a ''ᵁ U.1, U.2.image_of_isOpenImmersion a⟩
  have e' : U'.1 ≤ f ⁻¹ᵁ V.1 := by
    apply (a.image_mono e).trans
    exact (a.image_preimage_le (f ⁻¹ᵁ V.1))
  have hh := hflat V U' e'
  have heq : (a ≫ f).appLE V.1 U.1 e ≫ (a.appIso U.1).inv =
      f.appLE V.1 U'.1 e' := by
    rw [Scheme.Hom.comp_appLE, Category.assoc, Scheme.Hom.appLE_appIso_inv]
    rfl
  convert hh using 1 <;> try rfl
  ext r m
  change (F.smul (((a.appIso U.1).inv.hom)
    (((a ≫ f).appLE V.1 U.1 e).hom r))).asHom.hom m =
      (F.smul ((f.appLE V.1 U'.1 e').hom r)).asHom.hom m
  exact congrArg (fun t ↦ (F.smul t).asHom.hom m) (congrArg (fun t ↦ t.hom r) heq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionTriangles_isIso_of_presentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B)
    (h : StandardSingleFlatCounitPresentation p M g) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    IsIso (standardSingleBaseChangeMap p M g) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  obtain ⟨K, hb, hf, e, t, he⟩ := h
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    B.toRingedSpace K hb hf
  have := SingleComplexBaseChange.counit_isIso_kFlat g K hK
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionTriangles_isIso_on_subopen
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (W T : Y.Opens)
    (hTW : T ≤ W) (N : W.toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver (W.ι ≫ p)) (hT : StandardSingleFlatCounitOnOpen p g T) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    IsIso (standardSingleBaseChangeMap (T.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE hTW) N) g) := by
  let a := Y.homOfLE hTW
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  let e := (adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction a)).app N
  have : (Scheme.Modules.tensorPullbackObj a N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.toScheme.ringCatSheaf).prop_of_iso e.symm
      (inferInstance : (N.restrict a).IsQuasicoherent)
  have hn : (Scheme.Modules.tensorPullbackObj a N).IsFlatOver (T.ι ≫ p) := by
    apply unionTriangles_flatOver_of_iso _ e
    simpa only [a, ← Category.assoc, Scheme.homOfLE_ι] using
      unionTriangles_flatOver_restrict a (W.ι ≫ p) N hN
  exact unionTriangles_isIso_of_presentation _ _ _ (hT _ hn)

-- Attach R while transporting the diagram, so the large vertices are elaborated only once.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionTriangles_transport
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : DerivedCategory C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    {P P' : ShortComplex (CochainComplex C ℤ)} (m : P ⟶ P')
    (e₁ : DerivedCategory.Q.obj P.X₁ ≅ X₁)
    (e₂ : DerivedCategory.Q.obj P.X₂ ≅ X₂)
    (e₃ : DerivedCategory.Q.obj P.X₃ ≅ X₃)
    (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ Y₁)
    (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ Y₂)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ Y₃)
    (hP : P.ShortExact) (hP' : P'.ShortExact)
    (h₁ : DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ f₁)
    (h₂ : DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = e₂.hom ≫ f₂)
    (h₃ : DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ f₃)
    (R : Prop) (hR : R) :
    ∃ (d₁ : X₁ ⟶ X₂) (d₂ : X₂ ⟶ X₃) (d₃ : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
      (d₁' : Y₁ ⟶ Y₂) (d₂' : Y₂ ⟶ Y₃) (d₃' : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (DerivedCategory C) ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (DerivedCategory C) ∧
      ∃ φ : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        φ.hom₁ = f₁ ∧ φ.hom₂ = f₂ ∧ φ.hom₃ = f₃ ∧ R := by
  let d₁ := e₁.inv ≫ DerivedCategory.Q.map P.f ≫ e₂.hom
  let d₂ := e₂.inv ≫ DerivedCategory.Q.map P.g ≫ e₃.hom
  let d₃ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧'
  let d₁' := e₁'.inv ≫ DerivedCategory.Q.map P'.f ≫ e₂'.hom
  let d₂' := e₂'.inv ≫ DerivedCategory.Q.map P'.g ≫ e₃'.hom
  let d₃' := e₃'.inv ≫ DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧'
  let e : DerivedCategory.triangleOfSES hP ≅ Triangle.mk d₁ d₂ d₃ :=
    Triangle.isoMk _ _ e₁ e₂ e₃
      (by exact (Iso.hom_inv_id_assoc e₁ (DerivedCategory.Q.map P.f ≫ e₂.hom)).symm)
      (by exact (Iso.hom_inv_id_assoc e₂ (DerivedCategory.Q.map P.g ≫ e₃.hom)).symm)
      (by exact (Iso.hom_inv_id_assoc e₃
        (DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧')).symm)
  let e' : DerivedCategory.triangleOfSES hP' ≅ Triangle.mk d₁' d₂' d₃' :=
    Triangle.isoMk _ _ e₁' e₂' e₃'
      (by exact (Iso.hom_inv_id_assoc e₁' (DerivedCategory.Q.map P'.f ≫ e₂'.hom)).symm)
      (by exact (Iso.hom_inv_id_assoc e₂' (DerivedCategory.Q.map P'.g ≫ e₃'.hom)).symm)
      (by exact (Iso.hom_inv_id_assoc e₃'
        (DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧')).symm)
  let φ : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃' :=
    e.inv ≫ DerivedCategory.triangleOfSES.map hP hP' m ≫ e'.hom
  refine ⟨d₁, d₂, d₃, d₁', d₂', d₃',
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP) _ e.symm,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP') _ e'.symm,
    φ, ?_, ?_, ?_, hR⟩
  · change e₁.inv ≫ DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = _
    rw [h₁]
    simp only [Iso.inv_hom_id_assoc]
  · change e₂.inv ≫ DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = _
    rw [h₂]
    simp only [Iso.inv_hom_id_assoc]
  · change e₃.inv ≫ DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = _
    rw [h₃]
    simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The relative Mayer--Vietoris diagram for a relatively flat module has invertible
middle and overlap components. This supplies only the triangle diagram; it does
not assert invertibility of the union comparison or a factorization at a chosen
flat complex.

Source: Stacks Project, Tag 0DJ9, induction diagram; Tags 08BV and 08FE.
(blueprint: new-pc-standard-single-flat-counit-union-triangles).

Proof:
1. Work on X = U union V and restrict N to the opens induced by U, V and
   U intersection V. Exact open restriction preserves quasi-coherence and
   relative flatness. The three presentation hypotheses give bounded-above flat
   representatives of the respective direct images. Their pinned pullback
   counits are invertible by bounded-flat K-flatness and uniqueness of the
   left-derived functor. The presentation equations therefore make the three
   canonical single-module comparisons invertible.
2. On X and on its base change choose K-injective resolutions with injective
   terms of N[0] and its ordinary pullback in degree zero. Apply
   schemeKInjective_mayerVietoris_presentation to the induced two-open covers.
   Its short exact complexes give distinguished triangles via triangleOfSES.
   Apply derived direct image, and also derived pullback on the source side,
   and transport the open terms using the canonical composition isomorphisms.
   These functors are triangulated and additive, so the middle terms are the
   biproducts of the direct images on U and V. No compactness of the opens or
   quasi-coherence of their direct images is required.
3. Transpose the ordinary single-module pullback map under the derived
   pullback/direct-image adjunction. Naturality of the sectionwise restriction
   units gives the first square, and the difference of the two restriction
   squares gives the second. For the connecting square use the degreewise
   identity schemeMVUnderivedOpenCounit_square and naturality of the boundary
   of the short exact cover complexes. Transposition back commutes with shift.
   Pasting the adjunction counits identifies the first component with
   standardSingleBaseChangeMap and the open components with the three maps
   in step 1. The biproduct of the U and V isomorphisms is invertible, as is
   the overlap component. Package the two distinguished triangles, their
   explicit differentials and this triangle morphism.
Empty opens, identical opens and the zero module obey the same construction:
the empty-open terms vanish, while the restriction-difference sequence remains
short exact. No witness here defines a new object of the library. -/
theorem standardSingleFlatCounitUnionTriangles
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (d₁ : a.left ⟶ aU.left ⊞ aV.left)
      (d₂ : aU.left ⊞ aV.left ⟶ aUV.left)
      (d₃ : aUV.left ⟶ a.left⟦(1 : ℤ)⟧)
      (d₁' : a.right ⟶ aU.right ⊞ aV.right)
      (d₂' : aU.right ⊞ aV.right ⟶ aUV.right)
      (d₃' : aUV.right ⟶ a.right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory A) ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory A) ∧
      ∃ φ : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        φ.hom₁ = a.hom ∧ φ.hom₂ = biprod.map aU.hom aV.hom ∧ φ.hom₃ = aUV.hom ∧
        IsIso aU.hom ∧ IsIso aV.hom ∧ IsIso aUV.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
  let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
    (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
  let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
    (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
  let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
    (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
  dsimp only
  have hses := @standardSingle_union_ses_presentation.{u} Y B A p g U V N
  dsimp only at hses
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, h₃⟩ := hses
  have hU := unionTriangles_isIso_on_subopen p g (U ⊔ V) U le_sup_left N hN hPU
  have hV := unionTriangles_isIso_on_subopen p g (U ⊔ V) V le_sup_right N hN hPV
  have hUV := unionTriangles_isIso_on_subopen p g (U ⊔ V) (U ⊓ V)
    (inf_le_left.trans le_sup_left) N hN hPUV
  exact @unionTriangles_transport.{u + 1, u, u + 1}
    (SheafOfModules.{u} (moduleRings A.toRingedSpace)) inferInstance inferInstance
    (HasDerivedCategory.standard _) a.left (aU.left ⊞ aV.left) aUV.left
    a.right (aU.right ⊞ aV.right) aUV.right
    a.hom (biprod.map aU.hom aV.hom) aUV.hom P P' m
    e₁ e₂ e₃ e₁' e₂' e₃' hP hP' h₁ h₂ h₃
    (IsIso aU.hom ∧ IsIso aV.hom ∧ IsIso aUV.hom) ⟨hU, hV, hUV⟩

end AlgebraicGeometry
