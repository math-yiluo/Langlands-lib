/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVCoverHomotopyData
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleOpenRelativeArrow

/-! # Homotopy representatives of the resolved cover comparison -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem transport_comparison
    {T : Type*} [Category T] {X Y : T} {a b : Arrow T}
    (q : X ⟶ Y) (e : X ≅ a.left) (e' : Y ≅ a.right) (i : a ≅ b)
    (h : q ≫ e'.hom = e.hom ≫ a.hom) :
    q ≫ (e' ≪≫ Arrow.rightFunc.mapIso i).hom =
      (e ≪≫ Arrow.leftFunc.mapIso i).hom ≫ b.hom := by
  change q ≫ (e'.hom ≫ i.hom.right) = (e.hom ≫ i.hom.left) ≫ b.hom
  rw [← Category.assoc, h, Category.assoc, ← Arrow.w, ← Category.assoc]

private theorem transport_biprod_comparison
    {T : Type*} [Category T] [HasZeroMorphisms T] [HasBinaryBiproducts T]
    {X Y : T} {a₁ a₂ b₁ b₂ : Arrow T}
    (q : X ⟶ Y) (e : X ≅ a₁.left ⊞ a₂.left)
    (e' : Y ≅ a₁.right ⊞ a₂.right) (i₁ : a₁ ≅ b₁) (i₂ : a₂ ≅ b₂)
    (h : q ≫ e'.hom = e.hom ≫ biprod.map a₁.hom a₂.hom) :
    q ≫ (e' ≪≫ biprod.mapIso
        (Arrow.rightFunc.mapIso i₁) (Arrow.rightFunc.mapIso i₂)).hom =
      (e ≪≫ biprod.mapIso
        (Arrow.leftFunc.mapIso i₁) (Arrow.leftFunc.mapIso i₂)).hom ≫
          biprod.map b₁.hom b₂.hom := by
  simp only [Iso.trans_hom, biprod.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  congr 1
  change biprod.map a₁.hom a₂.hom ≫ biprod.map i₁.hom.right i₂.hom.right =
    biprod.map i₁.hom.left i₂.hom.left ≫ biprod.map b₁.hom b₂.hom
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc] using
      congrArg (fun k ↦ biprod.fst ≫ k) i₁.hom.w.symm
  · simpa only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc] using
      congrArg (fun k ↦ biprod.snd ≫ k) i₂.hom.w.symm

-- Transport the finite diagram before specializing its vertices to scheme functors.
private theorem unionHomotopyChainData_transport
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    {a b₁ b₂ b₃ c₁ c₂ c₃ : Arrow (DerivedCategory E)}
    (h : ∃ (C D C' D' : CochainComplex E ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ b₁.left ⊞ b₂.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ b₃.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ b₁.right ⊞ b₂.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ b₃.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map b₁.hom b₂.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ b₃.hom)
    (hi₁ : Nonempty (b₁ ≅ c₁)) (hi₂ : Nonempty (b₂ ≅ c₂))
    (hi₃ : Nonempty (b₃ ≅ c₃)) :
    ∃ (C D C' D' : CochainComplex E ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ c₁.left ⊞ c₂.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ c₃.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ c₁.right ⊞ c₂.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ c₃.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map c₁.hom c₂.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ c₃.hom := by
  obtain ⟨C, D, C', D', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ := h
  obtain ⟨i₁⟩ := hi₁
  obtain ⟨i₂⟩ := hi₂
  obtain ⟨i₃⟩ := hi₃
  refine ⟨C, D, C', D', t, t', α, β, H, e₁,
    e₂ ≪≫ biprod.mapIso (Arrow.leftFunc.mapIso i₁) (Arrow.leftFunc.mapIso i₂),
    e₃ ≪≫ Arrow.leftFunc.mapIso i₃, e₁',
    e₂' ≪≫ biprod.mapIso (Arrow.rightFunc.mapIso i₁) (Arrow.rightFunc.mapIso i₂),
    e₃' ≪≫ Arrow.rightFunc.mapIso i₃, hα, ?_, ?_⟩
  · exact transport_biprod_comparison _ e₂ e₂' i₁ i₂ hβ
  · exact transport_comparison _ e₃ e₃' i₃ hγ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolved cover comparison before cylinder rectification.
Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9.
(blueprint: lem-pc-standard-single-union-homotopy-chain-data).

Proof: Put W = U union V and pull its cover back to W_A. Resolve N[0] and
its ordinary pullback by functorial injective-term K-injective complexes. The
restriction-pair and restriction-difference rows are exact: sheaf gluing gives
the kernel, and injectivity gives the surjection onto the overlap. Apply the
relative direct-image computation to these rows. Resolve the source diagram
K-flatly before applying derived pullback, keeping the restriction maps and
the homotopies of the finite diagram. The derived-to-ordinary pullback counit,
transposed under the pullback/direct-image adjunction, induces the comparison
of the two resolved diagrams. Naturality of the restriction units and the
underived open counit square supply a specified homotopy H of its first square.
The induced cone map is mapOfHomotopy H: the homotopy term must be retained,
rather than choosing an arbitrary third map between distinguished triangles.
Identify the six objects using the short exact rows, direct-image composition,
exact open restriction and the additive biproduct comparison. Expand the
single-module comparison as the base-change mate followed by the single
pullback counit. Pasting counits and the adjunction triangle identities gives
the three displayed equations, including the equation for mapOfHomotopy H.
No cylinder rectification is done here. Empty opens and zero coefficients
produce zero rows; repeated or contained opens produce split rows. These
constructions therefore require neither flatness nor quasi-coherence. -/
theorem standardSingle_union_homotopy_chain_data
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
          e₃.hom ≫ aUV.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let W := U ⊔ V
  let f := W.ι ≫ p
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
  let φ := Scheme.picardTermwiseSingleMap (pullback.fst f g) N
  have hcover : (W.ι ⁻¹ᵁ U) ⊔ (W.ι ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact W.ι_preimage_self
  exact unionHomotopyChainData_transport
    (relativeMV_cover_homotopy_data f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) K K' φ (W.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ V) hcover)
    (standardSingle_open_relative_arrow p g W U le_sup_left N)
    (standardSingle_open_relative_arrow p g W V le_sup_right N)
    (standardSingle_open_relative_arrow p g W (U ⊓ V) (inf_le_left.trans le_sup_left) N)

end AlgebraicGeometry
