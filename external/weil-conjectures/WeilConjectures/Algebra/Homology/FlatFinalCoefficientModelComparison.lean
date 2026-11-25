/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent

import WeilConjectures.Algebra.Homology.FlatIteratedScalarExtensionHomologySquare

/-! # Flat change of the final coefficient ring of a tensor cohomology model

Source: Stacks Project, Tags 06Y6 and 00HD.
(blueprint: lem-pc-flat-final-coefficient-model-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace ModuleCat


private theorem tensorAdditiveLift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (M N : ModuleCat.{v} (A ⊗[R] B))
    (f : M →+ N)
    (hb : ∀ (b : B) (x : M),
      f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f x)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = ofHom
      (show ((restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M) →ₗ[B]
        ((restrictScalars
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N) from
          { toFun := f, map_add' := f.map_add, map_smul' := hb }) := by
  refine ⟨ofHom { toFun := f, map_add' := f.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.inductionOn with
    | tmul a b =>
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl

private theorem ordinaryModelComparisonIso
    (R A B E D : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing E] [CommRing D]
    [Algebra R A] [Algebra R B]
    [Algebra (A ⊗[R] B) E] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : BaseDerivedTensorCohomologyModel R A B M E)
    (n : BaseDerivedTensorCohomologyModel R A B M D) (i : ℤ) :
    ∃ e : m.cohomology i ≅ n.cohomology i,
      e.hom ≫ n.comparison i = m.comparison i := by
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
  obtain ⟨f, hf⟩ := tensorAdditiveLift R A B (m.cohomology i) (n.cohomology i)
    eB.hom.hom.toAddMonoidHom
    (fun b x ↦ eB.hom.hom.map_smul b x)
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
  obtain ⟨g, hg⟩ := tensorAdditiveLift R A B (n.cohomology i) (m.cohomology i)
    eB.inv.hom.toAddMonoidHom
    (fun b x ↦ eB.inv.hom.map_smul b x)
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
  exact ⟨e, hc⟩

private def equalScalarModuleIso
    (T D : Type u) [CommRing T] [CommRing D] (f g : T →+* D) (h : f = g)
    (V : ModuleCat.{u} T) : (extendScalars f).obj V ≅ (extendScalars g).obj V :=
  eqToIso (congrArg (fun k : T →+* D ↦ (extendScalars k).obj V) h)

private theorem equalScalarModuleIso_one
    (T D : Type u) [CommRing T] [CommRing D] (f g : T →+* D) (h : f = g)
    (V : ModuleCat.{u} T) (x : V) :
    (equalScalarModuleIso T D f g h V).hom ((1 : D) ⊗ₜ[T, f] x) =
      (1 : D) ⊗ₜ[T, g] x := by
  subst g
  rfl

private def equalScalarComplexIso
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : A →+* D ↦ ((extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

private theorem equalScalarComplexIso_inv_one
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (x : Q.X j) :
    (equalScalarComplexIso A D f g h Q).inv.f j ((1 : D) ⊗ₜ[A, g] x) =
      (1 : D) ⊗ₜ[A, f] x := by
  subst g
  rfl

/-- Flat change of the final coefficient ring commutes with a model's comparison.
Source: Stacks Project, Tag 06Y6 (uniqueness of derived tensor) and Tag 00HD
(exact tensor by a flat module).
(blueprint: lem-pc-flat-final-coefficient-model-comparison).

Proof: the universal counits identify the two models' derived functors. Apply
cohomology at the restricted complex, and conjugate by their cohomologyIso maps.
Naturality at multiplication by a in A and cohomologyIso_smul make the resulting
B-linear isomorphism A-tensor-B-linear. The comparison_eq equations identify the
ordinary comparison maps under this isomorphism. Extend it along A tensor_R B
to E and then to D; tensor associativity identifies this with extension directly
to D. This constructs e. Flatness of k makes its extension exact. The natural
homology isomorphism for that exact extension, and the termwise coefficient unit,
identify extension of the E-localized comparison with the D-localized comparison:
transpose by extension/restriction adjunction and substitute both localized_eq
identities. On 1 tensor (1 tensor x) the coefficient chain map is precisely tau.
Two successive applications of ExtendScalars.hom_ext show that its given formula
fixes it uniquely. Taking homology proves the equation. No flatness of E or D
over A tensor_R B is used. Identity maps, zero complexes, and zero final rings
satisfy the same tensor and adjunction equations. -/
theorem exists_flatFinalCoefficientModelComparison
    (R A B E D : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing E] [CommRing D]
    [Algebra R A] [Algebra R B]
    [Algebra (A ⊗[R] B) E] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (k : E →+* D) (hk : k.Flat)
    (hcoeff : k.comp (algebraMap (A ⊗[R] B) E) = algebraMap (A ⊗[R] B) D)
    (phi : A →+* E)
    (hphi : (algebraMap (A ⊗[R] B) E).comp
      (algebraMap A (A ⊗[R] B)) = phi)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : BaseDerivedTensorCohomologyModel R A B M E)
    (n : BaseDerivedTensorCohomologyModel R A B M D) (i : ℤ) :
    let C := ((extendScalars phi).mapHomologicalComplex (.up ℤ)).obj M
    let CD := ((extendScalars (k.comp phi)).mapHomologicalComplex (.up ℤ)).obj M
    let F := extendScalars k
    letI := preservesFiniteLimits_extendScalars_of_flat hk
    let aE := AlgebraicGeometry.affineBaseChangeTildeModuleMap R A B E M m phi hphi i
      (C.homology i) (Iso.refl _)
    let hphiD : (algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)) = k.comp phi := by rw [← hcoeff, RingHom.comp_assoc, hphi]
    let aD := AlgebraicGeometry.affineBaseChangeTildeModuleMap R A B D M n
      (k.comp phi) hphiD i (CD.homology i) (Iso.refl _)
    ∃ e : F.obj (AlgebraicGeometry.affineBaseChangeTildeModule R A B E M m i) ≅
        AlgebraicGeometry.affineBaseChangeTildeModule R A B D M n i,
      ∀ tau : (F.mapHomologicalComplex (.up ℤ)).obj C ≅ CD,
        (∀ (j : ℤ) (x : M.X j),
          tau.hom.f j ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A, phi] x)) =
            (1 : D) ⊗ₜ[A, k.comp phi] x) →
        F.map aE ≫ ((C.sc i).mapHomologyIso F).inv ≫
            HomologicalComplex.homologyMap tau.hom i = e.hom ≫ aD := by
  subst phi
  dsimp only
  let c := algebraMap (A ⊗[R] B) E
  let d := algebraMap (A ⊗[R] B) D
  let f := algebraMap A (A ⊗[R] B)
  let F := extendScalars k
  let CE := ((extendScalars (c.comp f)).mapHomologicalComplex (.up ℤ)).obj M
  let CN := ((extendScalars (d.comp f)).mapHomologicalComplex (.up ℤ)).obj M
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_of_flat hk
  obtain ⟨s, hs⟩ := ordinaryModelComparisonIso R A B E D M m n i
  let e₀ := (extendScalarsComp c k).symm.app (n.cohomology i) ≪≫
    equalScalarModuleIso (A ⊗[R] B) D (k.comp c) d hcoeff (n.cohomology i)
  let e := F.mapIso ((extendScalars c).mapIso s) ≪≫ e₀
  have he (x : m.cohomology i) :
      e.hom ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A ⊗[R] B, c] x)) =
        (1 : D) ⊗ₜ[A ⊗[R] B, d] (s.hom x) := by
    change e₀.hom (F.map ((extendScalars c).map s.hom)
      ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A ⊗[R] B, c] x))) = _
    rw [ExtendScalars.map_tmul, ExtendScalars.map_tmul]
    change (equalScalarModuleIso (A ⊗[R] B) D (k.comp c) d hcoeff _).hom
      ((extendScalarsComp c k).inv.app _ _) = _
    have ht := extendScalarsComp_hom_app_one_tmul c k (n.cohomology i) (s.hom x)
    have hi := ConcreteCategory.congr_hom
      ((extendScalarsComp c k).app (n.cohomology i)).hom_inv_id
      ((1 : D) ⊗ₜ[A ⊗[R] B, k.comp c] (s.hom x))
    have hi' := (congrArg (fun z ↦ (extendScalarsComp c k).inv.app _ z) ht).symm.trans hi
    rw [hi']
    exact equalScalarModuleIso_one (A ⊗[R] B) D (k.comp c) d hcoeff _ _
  refine ⟨e, ?_⟩
  intro tau htau
  let h : d.comp f = k.comp (c.comp f) := by
    change (algebraMap (A ⊗[R] B) D).comp _ = _
    rw [← hcoeff, RingHom.comp_assoc]
  let q := equalScalarComplexIso A D (d.comp f) (k.comp (c.comp f)) h M
  let tauN := tau ≪≫ q.symm
  have htauN (j : ℤ) (x : M.X j) :
      tauN.hom.f j ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A, c.comp f] x)) =
        (1 : D) ⊗ₜ[A, d.comp f] x := by
    change q.inv.f j (tau.hom.f j _) = _
    rw [htau]
    exact equalScalarComplexIso_inv_one A D (d.comp f) (k.comp (c.comp f)) h M j x
  have hsq := flatIteratedScalarExtension_homology_square A (A ⊗[R] B) E D
    f c d k hk hcoeff M i (m.cohomology i) (n.cohomology i) s
    (m.comparison i) (n.comparison i) hs m.ordinaryToLocalized n.ordinaryToLocalized
    m.ordinaryToLocalized_tmul n.ordinaryToLocalized_tmul
    (m.localizedComparison i) (n.localizedComparison i) (m.localized_eq i) (n.localized_eq i)
    e he tauN htauN
  have ht : tauN.hom ≫ q.hom = tau.hom := by simp [tauN]
  have hfinal := congrArg (fun a ↦ a ≫ HomologicalComplex.homologyMap q.hom i) hsq
  simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp, ht] at hfinal
  simpa only [AlgebraicGeometry.affineBaseChangeTildeModuleMap, Category.assoc,
    Iso.refl_hom, eqToHom_refl, Functor.map_id, Category.comp_id,
    q, equalScalarComplexIso, eqToIso.hom, HomologicalComplex.homologyFunctor,
    HomologicalComplex.homologyMap_id] using hfinal

end ModuleCat
