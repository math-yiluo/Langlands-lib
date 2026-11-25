/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Independence of localized tensor cohomology from its universal derived model

Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-base-derived-tensor-cohomology-model-localized-independence). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
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


/-- Two universal base-derived tensor models have isomorphic localized source
modules, compatibly with their specified localized comparison maps.
Source: Stacks Project, more-algebra.tex, Tag 06Y6 (independence of choices).
(blueprint: lem-pc-base-derived-tensor-cohomology-model-localized-independence).

Proof: uniqueness of total left derived functors gives a natural isomorphism
between m.derived and n.derived, commuting with their counits. Apply homology to
its component at the restricted complex M and compose with m.cohomologyIso and
the inverse of n.cohomologyIso. Naturality at multiplication by a in A and the
cohomologyIso_smul equations show compatibility with a tensor 1. B-linearity
shows compatibility with 1 tensor b, hence tensor induction makes this an
A-tensor-B-linear isomorphism. The comparison_eq equations and counit
compatibility show it commutes with the ordinary comparison; the ordinaryIso
maps coincide because their prescribed values on pure tensors agree. Likewise
the ordinaryToLocalized maps coincide by their values on pure tensors.
Extend the isomorphism to D. Transpose the desired localized equation through
the extension/restriction adjunction. Its naturality and the two localized_eq
identities reduce it to the ordinary comparison equation just proved. There is
no flatness or K-flatness assumption on M or the ring maps. This argument also
covers zero rings, zero complexes and every cohomological degree. -/
theorem baseDerivedTensorCohomologyModel_localized_independence
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m n : BaseDerivedTensorCohomologyModel R A B M D) (i : ℤ) :
    ∃ s : (extendScalars (algebraMap (A ⊗[R] B) D)).obj (m.cohomology i) ≅
        (extendScalars (algebraMap (A ⊗[R] B) D)).obj (n.cohomology i),
      s.hom ≫ n.localizedComparison i = m.localizedComparison i := by
  classical
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let : m.derived.IsLeftDerivedFunctor m.counit W := m.universal
  let : n.derived.IsLeftDerivedFunctor n.counit W := n.universal
  let δ := Functor.leftDerivedNatIso m.derived n.derived m.counit n.counit W (Iso.refl _)
  let K := ((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let X := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let U := restrictScalars (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let eB : U.obj (m.cohomology i) ≅ U.obj (n.cohomology i) :=
    m.cohomologyIso i ≪≫ H.mapIso (δ.app X) ≪≫ (n.cohomologyIso i).symm
  have heB (a : A) : U.map ((Algebra.TensorProduct.includeLeft (S := R) a :
      A ⊗[R] B) • 𝟙 (m.cohomology i)) ≫ eB.hom =
      eB.hom ≫ U.map ((Algebra.TensorProduct.includeLeft (S := R) a :
        A ⊗[R] B) • 𝟙 (n.cohomology i)) := by
    let v := DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map (a • 𝟙 M)))
    have hδ := congrArg H.map (δ.hom.naturality v)
    simp only [Functor.map_comp] at hδ
    apply (cancel_mono (n.cohomologyIso i).hom).1
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, m.cohomologyIso_smul, Category.assoc]
    rw [hδ]
    rw [n.cohomologyIso_smul]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  obtain ⟨f, hf⟩ := tensorLinearLift R A B (m.cohomology i) (n.cohomology i) eB.hom
    (fun a x ↦ by
      have h := ConcreteCategory.congr_hom (heB a) x
      exact h)
  have hfinv (a : A) : U.map ((Algebra.TensorProduct.includeLeft (S := R) a :
      A ⊗[R] B) • 𝟙 (n.cohomology i)) ≫ eB.inv =
      eB.inv ≫ U.map ((Algebra.TensorProduct.includeLeft (S := R) a :
        A ⊗[R] B) • 𝟙 (m.cohomology i)) := by
    apply (cancel_epi eB.hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun z ↦ z ≫ eB.inv) (heB a).symm
  obtain ⟨g, hg⟩ := tensorLinearLift R A B (n.cohomology i) (m.cohomology i) eB.inv
    (fun a x ↦ by
      have h := ConcreteCategory.congr_hom (hfinv a) x
      exact h)
  change U.map f = eB.hom at hf
  change U.map g = eB.inv at hg
  let e : m.cohomology i ≅ n.cohomology i :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply U.map_injective
        simp only [Functor.map_comp, hf, hg, Iso.hom_inv_id]
        exact (U.map_id _).symm
      inv_hom_id := by
        apply U.map_injective
        simp only [Functor.map_comp, hf, hg, Iso.inv_hom_id]
        exact (U.map_id _).symm }
  have hordinary : m.ordinaryIso.hom = n.ordinaryIso.hom := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ExtendScalars.hom_ext
    intro x
    exact (m.ordinaryIso_tmul j 1 x).trans (n.ordinaryIso_tmul j 1 x).symm
  have hlocal : m.ordinaryToLocalized = n.ordinaryToLocalized := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ExtendScalars.hom_ext
    intro x
    exact (m.ordinaryToLocalized_tmul j 1 x).trans
      (n.ordinaryToLocalized_tmul j 1 x).symm
  have hc : e.hom ≫ n.comparison i = m.comparison i := by
    apply U.map_injective
    let T := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).obj M
    apply (cancel_mono ((T.sc i).mapHomologyIso U).inv).1
    rw [Functor.map_comp, Category.assoc, n.comparison_eq, m.comparison_eq]
    change U.map f ≫ _ = _
    rw [hf]
    have hδ := Functor.leftDerivedNatTrans_app m.derived n.derived m.counit n.counit
      W (𝟙 _) ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
    have hδ' := congrArg H.map hδ
    simp only [NatTrans.id_app, Category.comp_id, Functor.map_comp] at hδ'
    change H.map (δ.hom.app X) ≫ H.map (n.counit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) =
        H.map (m.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) at hδ'
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [reassoc_of% hδ']
    rw [hordinary]
  let J := extendScalars (algebraMap (A ⊗[R] B) D)
  let adj := extendRestrictScalarsAdj (algebraMap (A ⊗[R] B) D)
  refine ⟨J.mapIso e, ?_⟩
  apply (adj.homEquiv _ _).injective
  dsimp only [Functor.mapIso_hom]
  rw [adj.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit]
  rw [n.localized_eq, m.localized_eq]
  rw [← Category.assoc, ← Category.assoc, hc, hlocal]
  simp only [Category.assoc]


end ModuleCat
