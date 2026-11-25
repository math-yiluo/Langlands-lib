/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Right derived functors after an exact functor

Source: Weil conjectures blueprint, `theorem-riemann-roch-coherent-serre-duality--2`, standard
homological algebra parenthetical; Stacks Project, Tag 015M (blueprint:
lem-sc-ext-derived-composite).
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Lifts from a resolution into an injective resolution that agree on the augmentation
are homotopic. The coinductive proof extends the construction of Mathlib's
`InjectiveResolution.descHomotopyZero` to a source with arbitrary terms: exactness of the
source and injectivity of the target suffice. -/
private theorem homotopy_of_resolution
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {X : B}
    {K : CochainComplex B ℕ} (ι : (CochainComplex.single₀ B).obj X ⟶ K)
    [QuasiIso ι] (J : InjectiveResolution X)
    (f g : K ⟶ J.cocomplex) (hf : ι ≫ f = J.ι) (hg : ι ≫ g = J.ι) :
    Nonempty (Homotopy f g) := by
  let z := f - g
  have hz : ι ≫ z = 0 := by simp [z, Preadditive.comp_sub, hf, hg]
  let h₀ : K.X 1 ⟶ J.cocomplex.X 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ ι).descToInjective (z.f 0)
      (by simpa using HomologicalComplex.congr_hom hz 0)
  have wh₀ : K.d 0 1 ≫ h₀ = z.f 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ ι).comp_descToInjective _ _
  let h₁ : K.X 2 ⟶ J.cocomplex.X 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ ι 0).descToInjective
      (z.f 1 - h₀ ≫ J.cocomplex.d 0 1) (by
        rw [Preadditive.comp_sub, ← Category.assoc, wh₀,
          HomologicalComplex.Hom.comm, sub_self])
  have wh₁ : K.d 1 2 ≫ h₁ = z.f 1 - h₀ ≫ J.cocomplex.d 0 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ ι 0).comp_descToInjective _ _
  have hz0 : Homotopy z 0 := by
    refine Homotopy.mkCoinductive z h₀ (by simp [wh₀]) h₁ (by simp [wh₁]) ?_
    rintro n ⟨a, b, w⟩
    have ww : z.f (n + 1) = K.d (n + 1) (n + 2) ≫ b +
        a ≫ J.cocomplex.d n (n + 1) := by simpa [add_comm] using w
    refine ⟨(CochainComplex.exact_succ_of_quasiIso_single₀ ι (n + 1)).descToInjective
      (z.f (n + 2) - b ≫ J.cocomplex.d (n + 1) (n + 2)) ?_, ?_⟩
    · rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, ww,
        Preadditive.add_comp, Category.assoc, Category.assoc,
        HomologicalComplex.d_comp_d, comp_zero, add_zero, sub_self]
    · simp [(CochainComplex.exact_succ_of_quasiIso_single₀ ι (n + 1)).comp_descToInjective]
  exact ⟨Homotopy.equivSubZero.invFun hz0⟩

/-- (blueprint: lem-sc-ext-derived-composite) An exact functor `T` whose injective images
are `U`-acyclic can be pulled inside every right derived functor of the left exact functor `U`.
The isomorphism is canonical: for any injective resolutions `I` of `M` and `J` of `T(M)`,
its forward map is the cohomology map of any lift `φ : T(I) ⟶ J` of the identity, transported
through the injective-resolution identifications and the complex-composition isomorphism.

Source: blueprint `theorem-riemann-roch-coherent-serre-duality--2`, standard homological algebra
parenthetical; Stacks Project, Tag 015M, proof (using Tag 015E).

Proof: choose an injective resolution `M ⟶ I` (def-sp-injective-resolutions). Exactness of
`T` makes `T(M) ⟶ T(I)` a resolution, although its terms need not be injective. The hypothesis
makes every term `T(Iⁿ)` acyclic (def-sp-acyclic). Apply the acyclic-resolution comparison of
lemma-weil-pbc-leray-acyclicity, item 2: any lift to an injective resolution `J` identifies
`RⁱU(T(M))` with `Hⁱ(U(T(I)))`. The composite `T ⋙ U` is left exact and its right derived
functor, computed with `I`, is the same cohomology object (def-sp-left-exact-additive).
Transporting the comparison gives the claimed isomorphism, with the displayed formula for
all choices of resolutions and lifts; homotopy uniqueness makes the formula independent
of those choices. -/
theorem exists_rightDerived_exact_comp_iso
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (U : B ⥤ C) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] [U.Additive] [PreservesFiniteLimits U]
    (hTU : ∀ (I : A), Injective I → U.rightAcyclic (T.obj I)) (M : A) (i : ℕ) :
    ∃ e : ((T ⋙ U).rightDerived i).obj M ≅ (U.rightDerived i).obj (T.obj M),
      ∀ (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
        (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex),
        T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 →
        e.hom = (I.isoRightDerivedObj (T ⋙ U) i).hom ≫
          HomologicalComplex.homologyMap
            ((mapHomologicalComplexCompIso (Iso.refl (T ⋙ U))
              (ComplexShape.up ℕ)).inv.app I.cocomplex) i ≫
          HomologicalComplex.homologyMap
            ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i ≫
          (J.isoRightDerivedObj U i).inv := by
  classical
  let TI := T.mapHomologicalComplex (ComplexShape.up ℕ)
  let UI := U.mapHomologicalComplex (ComplexShape.up ℕ)
  let c := mapHomologicalComplexCompIso (Iso.refl (T ⋙ U)) (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) i
  let ι (I : InjectiveResolution M) :=
    (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app M ≫
      TI.map I.ι
  have hι (I : InjectiveResolution M) : QuasiIso (ι I) := by
    dsimp [ι, TI]
    infer_instance
  have hι₀ (I : InjectiveResolution M) : (ι I).f 0 = T.map (I.ι.f 0) := by
    simp [ι, TI, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  let I₀ := injectiveResolution M
  let J₀ := injectiveResolution (T.obj M)
  let φ₀ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj M)) J₀ (ι I₀)
  have hφ₀ : ι I₀ ≫ φ₀ = J₀.ι := by simp [φ₀]
  have : QuasiIso φ₀ := by dsimp [φ₀]; infer_instance
  have : QuasiIso (UI.map φ₀) :=
    U.quasiIso_map_of_rightAcyclic_nat φ₀
      (fun n ↦ hTU (I₀.cocomplex.X n) inferInstance)
      (fun n ↦ Functor.rightAcyclic_of_injective _)
  have : IsIso (H.map (UI.map φ₀)) :=
    (quasiIsoAt_iff_isIso_homologyMap (UI.map φ₀) i).1 inferInstance
  let e := I₀.isoRightDerivedObj (T ⋙ U) i ≪≫
    H.mapIso (c.symm.app I₀.cocomplex) ≪≫
    asIso (H.map (UI.map φ₀)) ≪≫ (J₀.isoRightDerivedObj U i).symm
  refine ⟨e, ?_⟩
  intro I J φ hφ
  have hφ' : ι I ≫ φ = J.ι := by
    ext n
    cases n with
    | zero => simpa [hι₀] using hφ
    | succ n => simp [ι, TI]
  let α := InjectiveResolution.desc (𝟙 M) I I₀
  let β := InjectiveResolution.desc (𝟙 (T.obj M)) J J₀
  have hα : I₀.ι ≫ α = I.ι := by simp [α]
  have hβ : J₀.ι ≫ β = J.ι := by simp [β]
  have hTα : ι I₀ ≫ TI.map α = ι I := by
    simp only [ι, Category.assoc, ← TI.map_comp, hα]
  obtain ⟨ht⟩ := homotopy_of_resolution (ι I₀) J
    (φ₀ ≫ β) (TI.map α ≫ φ)
    (by rw [← Category.assoc, hφ₀, hβ])
    (by rw [← Category.assoc, hTα, hφ'])
  have hh := (U.mapHomotopy ht).homologyMap_eq i
  have hI := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 M) I₀ I α (by simp [α]) (T ⋙ U) i
  have hJ := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 (T.obj M)) J₀ J β (by simp [β]) U i
  have hc := c.inv.naturality α
  have hh' : H.map (UI.map φ₀) ≫ H.map (UI.map β) =
      H.map (UI.map (TI.map α)) ≫ H.map (UI.map φ) := by
    simpa only [H, UI, HomologicalComplex.homologyFunctor_map,
      Functor.map_comp, HomologicalComplex.homologyMap_comp] using hh
  have hI' : (I.isoRightDerivedObj (T ⋙ U) i).hom =
      (I₀.isoRightDerivedObj (T ⋙ U) i).hom ≫
        H.map (((T ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).map α) := by
    simpa only [H, Functor.comp_map, Functor.map_id, Category.id_comp] using hI
  have hJ' : (J₀.isoRightDerivedObj U i).inv =
      H.map (UI.map β) ≫ (J.isoRightDerivedObj U i).inv := by
    simpa only [H, UI, Functor.comp_map, Functor.map_id, Category.comp_id] using hJ
  have hc' : H.map (c.inv.app I₀.cocomplex) ≫ H.map (UI.map (TI.map α)) =
      H.map (((T ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).map α) ≫
        H.map (c.inv.app I.cocomplex) := by
    simpa only [Functor.map_comp, Functor.comp_map] using (congrArg H.map hc).symm
  change (I₀.isoRightDerivedObj (T ⋙ U) i).hom ≫
      H.map (c.inv.app I₀.cocomplex) ≫ H.map (UI.map φ₀) ≫
        (J₀.isoRightDerivedObj U i).inv =
    (I.isoRightDerivedObj (T ⋙ U) i).hom ≫
      H.map (c.inv.app I.cocomplex) ≫ H.map (UI.map φ) ≫
        (J.isoRightDerivedObj U i).inv
  rw [hJ', hI']
  simp only [Category.assoc]
  rw [reassoc_of% hh', reassoc_of% hc']

end CategoryTheory.Functor
