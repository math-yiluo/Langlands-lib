/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionCoherentTriangle

/-! # Canonical completion of the derived tensor row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

private theorem tensorLinearLift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (M N : ModuleCat.{u} (A ⊗[R] B))
    (f : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ⟶
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = f := by
  refine ⟨ofHom { toFun := f, map_add' := f.hom.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.inductionOn with
    | tmul a b =>
      have hb (y : M) :
          f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • y) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f y :=
        f.hom.map_smul b y
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.hom.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl


set_option backward.isDefEq.respectTransparency false in
private theorem map_to_common_derived
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
    (m : BaseDerivedTensorCohomologyModel R A B Q C)
    (n : BaseDerivedTensorCohomologyModel R A B Q' C) (i : ℤ)
    (δ : m.derived ⟶ n.derived) (g : m.cohomology i ⟶ n.cohomology i)
    (hδ : Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
      n.counit = m.counit)
    (hg : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
          (n.cohomologyIso i).hom =
      (m.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q'))))) :
    let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
    let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let cm := Functor.leftDerivedNatTrans m.derived L m.counit ε W (𝟙 _)
    let cn := Functor.leftDerivedNatTrans n.derived L n.counit ε W (𝟙 _)
    (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map g ≫
        (n.cohomologyIso i).hom ≫ H.map (cn.app (F.obj Q')) =
      (m.cohomologyIso i).hom ≫ H.map (cm.app (F.obj Q)) ≫ H.map (L.map (F.map f)) := by
  intro W F H cm cn
  have hc : δ ≫ cn = cm := by
    apply Functor.leftDerived_ext L ε W m.derived
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [Functor.leftDerivedNatTrans_fac, Category.comp_id, hδ,
      Functor.leftDerivedNatTrans_fac, Category.comp_id]
  rw [← Category.assoc, hg]
  simp only [Category.assoc]
  change (m.cohomologyIso i).hom ≫ H.map (m.derived.map (F.map f)) ≫
    H.map (δ.app (F.obj Q')) ≫ H.map (cn.app (F.obj Q')) = _
  rw [← H.map_comp (δ.app _) (cn.app _), ← NatTrans.comp_app, hc]
  rw [← H.map_comp, cm.naturality, H.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_exact_pair
    {E B : Type u} [CommRing E] [CommRing B] (r : B →+* E)
    {X Y Z : ModuleCat.{u} E} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : (ComposableArrows.mk₂ ((restrictScalars r).map f)
      ((restrictScalars r).map g)).Exact) :
    (ComposableArrows.mk₂ f g).Exact := by
  have w : f ≫ g = 0 := by
    apply (restrictScalars r).map_injective
    have hw := h.toIsComplex.zero 0
    change (restrictScalars r).map f ≫ (restrictScalars r).map g = 0 at hw
    simpa only [Functor.map_comp, Functor.map_zero] using hw
  apply ComposableArrows.exact₂_mk _ w
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  have hh := h.exact 0
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_exact_row
    {E B : Type u} [CommRing E] [CommRing B] (r : B →+* E)
    {X₀ X₁ X₂ X₃ X₄ : ModuleCat.{u} E}
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄)
    (h : (ComposableArrows.mk₄ ((restrictScalars r).map f₀)
      ((restrictScalars r).map f₁) ((restrictScalars r).map f₂)
      ((restrictScalars r).map f₃)).Exact) :
    (ComposableArrows.mk₄ f₀ f₁ f₂ f₃).Exact := by
  apply ComposableArrows.exact_of_δ₀
  · apply restrict_exact_pair r
    exact ComposableArrows.exact₂_mk _ _ (h.exact 0)
  · apply ComposableArrows.exact_of_δ₀
    · apply restrict_exact_pair r
      exact ComposableArrows.exact₂_mk _ _ (h.exact 1)
    · apply restrict_exact_pair r
      exact ComposableArrows.exact₂_mk _ _ (h.exact 2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Complete the canonical same-degree model maps by the derived connecting map.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, exactness and independence of
choices; step 1 of lem-pc-base-derived-tensor-ordinary-triangle-rows.

Proof: choose the triangulated universal derived extension supplied by
exists_baseDerivedExtension_resolution. Universal uniqueness identifies it with
m₁.derived. The coherent shift compatible with the counit is unique by the right
Kan universal property, so this identification respects the given shift structure.
Exact restriction A to R sends the localized distinguished triangle to D(R).
Apply derived extension and its long exact cohomology sequence. Identify all
three vertices with the prescribed model cohomology via universal counit
uniqueness. The hypotheses hg0, hg1 and hg3 identify its three same-degree maps
with the prescribed s₀, s₁ and s₃: the counit identities force each δk to be the
unique universal transformation. Define the B-linear boundary by the displayed
formula. Multiplication by a in A defines an endomorphism of the input triangle;
naturality of the cohomology connecting map, the cohomologyIso_smul identities
and naturality of the unique universal comparison show that this B-linear map
commutes with a tensor 1. It already commutes with 1 tensor b by B-linearity.
Tensor induction gives E-linearity, E = A tensor_R B, and thus a morphism s₂.
Its restriction is exactly the stated formula by construction. The B-linear
row is conjugate to the long exact row; exact faithful restriction E to B
reflects exactness, proving the first conclusion. No ordinary counit comparison
square is claimed here. Zero rings, zero complexes and arbitrary degrees use
the same universal-property and tensor-induction arguments.
(blueprint: lem-pc-base-derived-tensor-canonical-row-completion). -/
theorem exists_baseDerivedTensor_canonical_row_completion
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C)
    [m₁.derived.CommShift ℤ] [NatTrans.CommShift m₁.counit ℤ]
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C) (i : ℤ)
    (δ0 : m₁.derived ⟶ m₂.derived) (δ1 : m₂.derived ⟶ m₃.derived)
    (δ3 : m₁.derived ⟶ m₂.derived)
    (s0 : m₁.cohomology i ⟶ m₂.cohomology i)
    (s1 : m₂.cohomology i ⟶ m₃.cohomology i)
    (s3 : m₁.cohomology (i + 1) ⟶ m₂.cohomology (i + 1))
    (hδ0 : Functor.whiskerLeft DerivedCategory.Qh δ0 ≫ m₂.counit = m₁.counit)
    (hδ1 : Functor.whiskerLeft DerivedCategory.Qh δ1 ≫ m₃.counit = m₂.counit)
    (hδ3 : Functor.whiskerLeft DerivedCategory.Qh δ3 ≫ m₂.counit = m₁.counit)
    (hg0 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s0 ≫
          (m₂.cohomologyIso i).hom =
      (m₁.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m₁.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₁)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ0.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₂)))))
    (hg1 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s1 ≫
          (m₃.cohomologyIso i).hom =
      (m₂.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m₂.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₂)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ1.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₃)))))
    (hg3 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s3 ≫
          (m₂.cohomologyIso (i + 1)).hom =
      (m₁.cohomologyIso (i + 1)).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (i + 1)).map
          (m₁.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₁)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (i + 1)).map
          (δ3.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₂))))) :
    letI := m₁.universal
    let δ := Functor.leftDerivedNatTrans m₃.derived m₁.derived m₃.counit m₁.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (𝟙 _)
    let D := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ m₁.derived
    let X := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₃))
    ∃ s₂ : m₃.cohomology i ⟶ m₁.cohomology (i + 1),
      (ComposableArrows.mk₄ s0 s1 s₂ s3).Exact ∧
      (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map s₂ ≫
        (m₁.cohomologyIso (i + 1)).hom =
      (m₃.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map (δ.app X) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
          (ShiftedHom.map T.mor₃ D) i (i + 1) (by omega) := by
  have := m₁.universal
  have := m₂.universal
  have := m₃.universal
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
    HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let D := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
    HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ m₁.derived
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
  let U := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let c₂ := Functor.leftDerivedNatIso m₂.derived m₁.derived m₂.counit m₁.counit W
    (Iso.refl _)
  let c₃ := Functor.leftDerivedNatIso m₃.derived m₁.derived m₃.counit m₁.counit W
    (Iso.refl _)
  let e₁ := m₁.cohomologyIso i
  let e₂ := m₂.cohomologyIso i ≪≫ (H i).mapIso (c₂.app (F.obj T.obj₂))
  let e₃ := m₃.cohomologyIso i ≪≫ (H i).mapIso (c₃.app (F.obj T.obj₃))
  let e₄ := m₁.cohomologyIso (i + 1)
  let e₅ := m₂.cohomologyIso (i + 1) ≪≫
    (H (i + 1)).mapIso (c₂.app (F.obj T.obj₂))
  let b : (H i).obj (D.obj T.obj₃) ⟶ (H (i + 1)).obj (D.obj T.obj₁) :=
    (H 0).shiftMap (ShiftedHom.map T.mor₃ D) i (i + 1) (by omega)
  let t : U.obj (m₃.cohomology i) ⟶ U.obj (m₁.cohomology (i + 1)) :=
    e₃.hom ≫ b ≫ e₄.inv
  have ht : ∀ (a : A) (x : m₃.cohomology i),
      t ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • t x := by
    intro a x
    let k : A ⊗[R] B := Algebra.TensorProduct.includeLeft (S := R) a
    have ha₃ : U.map (k • 𝟙 (m₃.cohomology i)) ≫ e₃.hom =
        e₃.hom ≫ (H i).map (D.map (a • 𝟙 T.obj₃)) := by
      dsimp only [e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [← Category.assoc, m₃.cohomologyIso_smul, Category.assoc]
      change (m₃.cohomologyIso i).hom ≫
        (H i).map (m₃.derived.map (F.map (a • 𝟙 T.obj₃))) ≫
        (H i).map (c₃.hom.app (F.obj T.obj₃)) = _
      erw [← (H i).map_comp, c₃.hom.naturality, (H i).map_comp]
      rfl
    have ha₁ : U.map (k • 𝟙 (m₁.cohomology (i + 1))) ≫ e₄.hom =
        e₄.hom ≫ (H (i + 1)).map (D.map (a • 𝟙 T.obj₁)) :=
      m₁.cohomologyIso_smul (i + 1) a
    have w : (a • 𝟙 T.obj₃) ≫ T.mor₃ =
        T.mor₃ ≫ (a • 𝟙 T.obj₁)⟦(1 : ℤ)⟧' := by
      ext j y
      exact (T.mor₃.f j).hom.map_smul a y
    have wn : D.map (a • 𝟙 T.obj₃) ≫ ShiftedHom.map T.mor₃ D =
        ShiftedHom.map T.mor₃ D ≫ (D.map (a • 𝟙 T.obj₁))⟦(1 : ℤ)⟧' := by
      simp only [ShiftedHom.map, ← Functor.map_comp_assoc, w, Functor.map_comp,
        Category.assoc, Functor.commShiftIso_hom_naturality]
    have hb : (H i).map (D.map (a • 𝟙 T.obj₃)) ≫ b =
        b ≫ (H (i + 1)).map (D.map (a • 𝟙 T.obj₁)) := by
      calc
        (H i).map (D.map (a • 𝟙 T.obj₃)) ≫ b =
            (H 0).shiftMap (D.map (a • 𝟙 T.obj₃) ≫ ShiftedHom.map T.mor₃ D)
              i (i + 1) (by omega) :=
          ((H 0).shiftMap_comp' _ _ i (i + 1) (by omega)).symm
        _ = (H 0).shiftMap (ShiftedHom.map T.mor₃ D ≫
            (D.map (a • 𝟙 T.obj₁))⟦(1 : ℤ)⟧') i (i + 1) (by omega) := by rw [wn]
        _ = b ≫ (H (i + 1)).map (D.map (a • 𝟙 T.obj₁)) :=
          (H 0).shiftMap_comp _ _ i (i + 1) (by omega)
    have hi : (H (i + 1)).map (D.map (a • 𝟙 T.obj₁)) ≫ e₄.inv =
        e₄.inv ≫ U.map (k • 𝟙 (m₁.cohomology (i + 1))) := by
      apply (cancel_epi e₄.hom).1
      rw [← Category.assoc, ← ha₁]
      simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
        Category.comp_id]
    have hc : U.map (k • 𝟙 (m₃.cohomology i)) ≫ t =
        t ≫ U.map (k • 𝟙 (m₁.cohomology (i + 1))) := by
      dsimp only [t]
      rw [← Category.assoc, ha₃]
      simp only [Category.assoc]
      rw [← Category.assoc ((H i).map (D.map (a • 𝟙 T.obj₃))) b e₄.inv,
        hb, Category.assoc, hi]
    exact congrArg (fun f ↦ f x) hc
  obtain ⟨s₂, hs₂⟩ := tensorLinearLift R A B _ _ t ht
  refine ⟨s₂, ?_, ?_⟩
  · have h0 : U.map s0 ≫ e₂.hom = e₁.hom ≫ (H i).map (D.map T.mor₁) := by
      have hh := map_to_common_derived R A B C m₁.derived m₁.counit
        T.obj₁ T.obj₂ T.mor₁ m₁ m₂ i δ0 s0 hδ0 hg0
      dsimp only at hh
      rw [Functor.leftDerivedNatTrans_id] at hh
      change U.map s0 ≫ e₂.hom =
        e₁.hom ≫ (H i).map (𝟙 _) ≫ (H i).map (D.map T.mor₁) at hh
      dsimp only [H, F, D, Functor.comp_obj, Functor.comp_map] at hh ⊢
      rw [CategoryTheory.Functor.map_id] at hh
      simpa only [Category.id_comp] using hh
    have h1 : U.map s1 ≫ e₃.hom = e₂.hom ≫ (H i).map (D.map T.mor₂) := by
      exact map_to_common_derived R A B C m₁.derived m₁.counit T.obj₂ T.obj₃ T.mor₂
        m₂ m₃ i δ1 s1 hδ1 hg1
    have h3 : U.map s3 ≫ e₅.hom = e₄.hom ≫ (H (i + 1)).map (D.map T.mor₁) := by
      have hh := map_to_common_derived R A B C m₁.derived m₁.counit
        T.obj₁ T.obj₂ T.mor₁ m₁ m₂ (i + 1) δ3 s3 hδ3 hg3
      dsimp only at hh
      rw [Functor.leftDerivedNatTrans_id] at hh
      change U.map s3 ≫ e₅.hom =
        e₄.hom ≫ (H (i + 1)).map (𝟙 _) ≫ (H (i + 1)).map (D.map T.mor₁) at hh
      dsimp only [H, F, D, Functor.comp_obj, Functor.comp_map] at hh ⊢
      rw [CategoryTheory.Functor.map_id] at hh
      simpa only [Category.id_comp] using hh
    have h2 : U.map s₂ ≫ e₄.hom = e₃.hom ≫ b := by
      rw [hs₂]
      simp only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hd := baseDerivedExtension_coherent_triangle_distinguished R A B
      m₁.derived m₁.counit T hT
    have he : (ComposableArrows.mk₄ ((H i).map (D.map T.mor₁))
        ((H i).map (D.map T.mor₂)) b ((H (i + 1)).map (D.map T.mor₁))).Exact := by
      apply ComposableArrows.exact_of_δ₀
      · exact (DerivedCategory.HomologySequence.exact₂
          (D.mapTriangle.obj T) hd i).exact_toComposableArrows
      · apply ComposableArrows.exact_of_δ₀
        · exact (DerivedCategory.HomologySequence.exact₃ (D.mapTriangle.obj T) hd
            i (i + 1)).exact_toComposableArrows
        · exact (DerivedCategory.HomologySequence.exact₁ (D.mapTriangle.obj T) hd
            i (i + 1)).exact_toComposableArrows
    apply restrict_exact_row Algebra.TensorProduct.includeRight.toRingHom
    exact ComposableArrows.exact_of_iso
      (ComposableArrows.isoMk₄ e₁ e₂ e₃ e₄ e₅ h0 h1 h2 h3).symm he
  · have h2 : U.map s₂ ≫ e₄.hom = e₃.hom ≫ b := by
      rw [hs₂]
      simp only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [U, e₄, e₃, c₃, W, F, D, H, b, Functor.leftDerivedNatIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
      Functor.comp_obj, Functor.comp_map] at h2 ⊢
    simpa only [Category.assoc] using h2
end ModuleCat
