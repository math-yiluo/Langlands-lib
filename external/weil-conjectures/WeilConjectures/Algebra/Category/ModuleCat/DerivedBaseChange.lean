/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Derived base change of modules

Let `f : A →+* A'` be a morphism of commutative rings. A morphism `η : K ⟶ Res K'` in `D(A)`
from an object `K` to the restriction of scalars of `K' ∈ D(A')` *exhibits `K'` as the derived
base change `K ⊗ᴸ_A A'`* (`ModuleCat.IsDerivedBaseChange`) if it is a universal arrow from `K`
to the restriction of scalars: derived base change is left adjoint to restriction of scalars.

When `f` is surjective with principal kernel `(a)`, extension of scalars `M ↦ A' ⊗_A M`
together with the unit `M ⟶ A' ⊗_A M` of the extension-restriction adjunction is a reduction
datum for restriction of scalars along `f` and the multiplication by `a`
(`ModuleCat.reductionDatum`). Hence for a K-flat complex `P` the reduction
`P ⟶ Res (A' ⊗_A P)` exhibits `A' ⊗_A P` as the derived base change of `P`
(`ModuleCat.isDerivedBaseChange_Q_map_complexMap`).

## Main definitions

- `ModuleCat.derivedRestrictScalars`: restriction of scalars `D(A') ⥤ D(A)`.
- `ModuleCat.IsDerivedBaseChange`: universal arrows to restrictions of scalars.
- `ModuleCat.smulIdNatTrans`: the multiplication by a scalar on `A`-modules.
- `ModuleCat.reductionDatum`: extension of scalars along a surjective ring morphism with
  principal kernel is a reduction datum.

## Main results

- `ModuleCat.IsDerivedBaseChange.comp`: derived base changes compose.
- `ModuleCat.IsDerivedBaseChange.isIso`: two derived base changes of the same object are
  isomorphic through any compatible comparison map.
- `ModuleCat.isDerivedBaseChange_Q_map_complexMap`: the reduction of a K-flat complex is its
  derived base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

section

variable {A A' : Type u} [CommRing A] [CommRing A'] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')] (f : A →+* A')

/-- Restriction of scalars `D(A') ⥤ D(A)` along a ring morphism `f : A →+* A'`, induced by the
exact restriction of scalars of modules. -/
noncomputable abbrev derivedRestrictScalars :
    DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (restrictScalars.{u} f).mapDerivedCategory

variable {f}

/-- A morphism `η : K ⟶ Res K'` from `K ∈ D(A)` to the restriction of scalars of `K' ∈ D(A')`
*exhibits `K'` as the derived base change `K ⊗ᴸ_A A'`* if it is universal among morphisms from
`K` to restrictions of scalars: every `K ⟶ Res N` factors uniquely as `η` followed by the
restriction of a morphism `K' ⟶ N`. -/
def IsDerivedBaseChange {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')} (η : K ⟶ (derivedRestrictScalars f).obj K') :
    Prop :=
  ∀ N : DerivedCategory (ModuleCat.{u} A'),
    Function.Bijective fun g : K' ⟶ N ↦ η ≫ (derivedRestrictScalars f).map g

/-- Restricting scalars along `g` and then along `f` is restricting scalars along `g ∘ f`. -/
noncomputable def derivedRestrictScalarsCompIso {A'' : Type u} [CommRing A'']
    [HasDerivedCategory.{u} (ModuleCat.{u} A'')] {g : A' →+* A''} {gf : A →+* A''}
    (hgf : gf = g.comp f) :
    derivedRestrictScalars g ⋙ derivedRestrictScalars f ≅ derivedRestrictScalars gf :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (restrictScalarsComp' f g gf hgf).symm

namespace IsDerivedBaseChange

variable {K : DerivedCategory (ModuleCat.{u} A)} {K' K'' : DerivedCategory (ModuleCat.{u} A')}

/-- Two derived base changes of the same object are isomorphic through every comparison map
compatible with them. -/
lemma isIso {η : K ⟶ (derivedRestrictScalars f).obj K'}
    {η' : K ⟶ (derivedRestrictScalars f).obj K''} (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') (φ : K' ⟶ K'')
    (hφ : η ≫ (derivedRestrictScalars f).map φ = η') : IsIso φ := by
  obtain ⟨ψ, hψ : η' ≫ _ = η⟩ := (hη' K').2 η
  refine ⟨⟨ψ, (hη K').1 ?_, (hη' K'').1 ?_⟩⟩
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hφ, hψ, CategoryTheory.Functor.map_id, Category.comp_id]
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hψ, hφ, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Derived base change is invariant under isomorphisms of the source. -/
lemma of_iso {K₀ : DerivedCategory (ModuleCat.{u} A)} (e : K₀ ≅ K)
    {η : K ⟶ (derivedRestrictScalars f).obj K'} (hη : IsDerivedBaseChange η) :
    IsDerivedBaseChange (e.hom ≫ η) := by
  intro N
  convert (e.symm.homFromEquiv (Z := (derivedRestrictScalars f).obj N)).bijective.comp
    (hη N) using 1
  ext g
  simp

/-- Derived base change is invariant under isomorphisms of the target. -/
lemma comp_map_iso {η : K ⟶ (derivedRestrictScalars f).obj K'} (hη : IsDerivedBaseChange η)
    (e : K' ≅ K'') : IsDerivedBaseChange (η ≫ (derivedRestrictScalars f).map e.hom) := by
  intro N
  convert (hη N).comp (e.symm.homFromEquiv (Z := N)).bijective using 1
  ext g
  simp

/-- Derived base changes compose. -/
lemma comp {A'' : Type u} [CommRing A''] [HasDerivedCategory.{u} (ModuleCat.{u} A'')]
    {g : A' →+* A''} {gf : A →+* A''} (hgf : gf = g.comp f)
    {K'' : DerivedCategory (ModuleCat.{u} A'')}
    {η : K ⟶ (derivedRestrictScalars f).obj K'} (hη : IsDerivedBaseChange η)
    {η' : K' ⟶ (derivedRestrictScalars g).obj K''} (hη' : IsDerivedBaseChange η') :
    IsDerivedBaseChange (f := gf)
      (η ≫ (derivedRestrictScalars f).map η' ≫
        (derivedRestrictScalarsCompIso hgf).hom.app K'') := by
  intro N
  convert ((((derivedRestrictScalarsCompIso hgf).app N).homToEquiv
    (Z := K)).bijective.comp (hη _)).comp (hη' N) using 1
  ext g
  have := (derivedRestrictScalarsCompIso hgf).hom.naturality g
  dsimp at this ⊢
  simp [this]

end IsDerivedBaseChange

end

section Reduction

variable {A A' : Type u} [CommRing A] [CommRing A']

/-- The multiplication by a scalar `a` on `A`-modules, as an endomorphism of the identity
functor. -/
@[simps]
def smulIdNatTrans (a : A) : 𝟭 (ModuleCat.{u} A) ⟶ 𝟭 _ where
  app M := a • 𝟙 M

variable (f : A →+* A')

/-- With scalars restricted back to `A`, the extension of scalars `A' ⊗_A M` of an `A`-module
`M` is the tensor product `A' ⊗ M` of `A`-modules. -/
noncomputable def restrictScalarsObjExtendScalarsObjIso (M : ModuleCat.{u} A) :
    (restrictScalars.{u} f).obj ((extendScalars.{u} f).obj M) ≅
      (restrictScalars.{u} f).obj (of A' A') ⊗ M :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars.{u} f).obj ((extendScalars.{u} f).obj M)))
    (M₂ := ↑((restrictScalars.{u} f).obj (of A' A') ⊗ M))
    (AddEquiv.refl _)
    (fun r x ↦ by
      induction x using TensorProduct.inductionOn with
      | tmul q m => rfl
      | add x y hx hy => simp_all)).toModuleIso

/-- With scalars restricted back to `A`, extension of scalars along `f` is the tensor product
`M ↦ M ⊗ A'` of `A`-modules. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u} f ⋙ restrictScalars.{u} f ≅
      tensorRight ((restrictScalars.{u} f).obj (of A' A')) :=
  NatIso.ofComponents (fun M ↦ restrictScalarsObjExtendScalarsObjIso f M ≪≫ β_ _ M)
    (fun {M N} φ ↦ by
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul q m => rfl
      | add x y hx hy => simp_all)

/-- The `A`-linear map `A ⟶ A'` induced by `f`, from the monoidal unit. -/
noncomputable def unitToRestrictScalars :
    𝟙_ (ModuleCat.{u} A) ⟶ (restrictScalars.{u} f).obj (of A' A') :=
  ofHom (Y := ↑((restrictScalars.{u} f).obj (of A' A'))) (LinearMap.toSpanSingleton A _ (1 : A'))

/-- The map `A ⟶ A'` is `f`. -/
@[simp]
lemma unitToRestrictScalars_apply (x : A) : (unitToRestrictScalars f).hom x = f x :=
  mul_one (f x)

/-- The unit `M ⟶ A' ⊗_A M` of the extension-restriction adjunction is
`M ≅ M ⊗ A ⟶ M ⊗ A'`. -/
lemma extendRestrictScalarsAdj_unit_app (M : ModuleCat.{u} A) :
    (extendRestrictScalarsAdj.{u} f).unit.app M =
      (ρ_ M).inv ≫ M ◁ unitToRestrictScalars f ≫
        (extendScalarsCompRestrictScalarsIso f).inv.app M := by
  ext m
  erw [extendRestrictScalarsAdj_unit_app_apply]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    unitToRestrictScalars, extendScalarsCompRestrictScalarsIso,
    restrictScalarsObjExtendScalarsObjIso, NatIso.ofComponents_inv_app, Iso.trans_inv,
    LinearEquiv.toModuleIso_inv, BraidedCategory.braiding_inv_naturality_right_assoc,
    braiding_inv_tensorUnit_left, Category.assoc, Iso.inv_hom_id_assoc, hom_comp,
    ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    AddEquiv.coe_toLinearEquiv_symm, AddEquiv.refl_symm, Function.comp_apply,
    MonoidalCategory.leftUnitor_inv_apply, MonoidalCategory.whiskerRight_apply]
  erw [AddEquiv.refl_apply, LinearMap.toSpanSingleton_apply, one_smul]

variable {f}

/-- The map `A ⟶ A'` is an epimorphism when `f` is surjective. -/
lemma epi_unitToRestrictScalars (hf : Function.Surjective f) : Epi (unitToRestrictScalars f) :=
  (epi_iff_surjective _).2 fun y ↦ by
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, unitToRestrictScalars_apply f x⟩

/-- The unit `M ⟶ A' ⊗_A M` of the extension-restriction adjunction is an epimorphism when `f`
is surjective. -/
lemma epi_extendRestrictScalarsAdj_unit_app (hf : Function.Surjective f) (M : ModuleCat.{u} A) :
    Epi ((extendRestrictScalarsAdj.{u} f).unit.app M) := by
  have := epi_unitToRestrictScalars hf
  have : Epi (M ◁ unitToRestrictScalars f) := (tensorLeft M).map_epi _
  rw [extendRestrictScalarsAdj_unit_app]
  infer_instance

variable {a : A}

/-- The multiplication by a generator `a` of `ker f` vanishes on restrictions of scalars of
`A'`-modules. -/
lemma smulIdNatTrans_app_restrictScalars_obj (ha : RingHom.ker f = Ideal.span {a})
    (X : ModuleCat.{u} A') : (smulIdNatTrans a).app ((restrictScalars.{u} f).obj X) = 0 := by
  have hfa : f a = 0 := by
    rw [← RingHom.mem_ker, ha]
    exact Ideal.mem_span_singleton_self a
  ext x
  exact (restrictScalars.smul_def f a x).trans (by simp [hfa])

/-- The multiplication by a generator `a` of `ker f` kills the map `A ⟶ A'`. -/
lemma smul_unitToRestrictScalars (ha : RingHom.ker f = Ideal.span {a}) :
    a • unitToRestrictScalars f = 0 := by
  have hfa : f a = 0 := by
    rw [← RingHom.mem_ker, ha]
    exact Ideal.mem_span_singleton_self a
  refine hom_ext (LinearMap.ext fun x ↦ ?_)
  rw [hom_smul, LinearMap.smul_apply, unitToRestrictScalars_apply]
  exact (restrictScalars.smul_def (M := of A' A') f a (f x)).trans (by simp [hfa])

/-- The multiplication by a generator `a` of `ker f`, followed by the map `A ⟶ A'`,
vanishes. -/
lemma smul_comp_unitToRestrictScalars (ha : RingHom.ker f = Ideal.span {a}) :
    (a • 𝟙 (𝟙_ (ModuleCat.{u} A))) ≫ unitToRestrictScalars f = 0 := by
  rw [Linear.smul_comp, Category.id_comp, smul_unitToRestrictScalars ha]

/-- The short complex of `A`-modules `A --a--> A ⟶ A'` is exact when `ker f = (a)`. -/
lemma exact_smul_unitToRestrictScalars (ha : RingHom.ker f = Ideal.span {a}) :
    (ShortComplex.mk _ _ (smul_comp_unitToRestrictScalars ha)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : x ∈ RingHom.ker f := (unitToRestrictScalars_apply f x).symm.trans hx
  rw [ha] at hx'
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  exact ⟨b, by simp [mul_comm]⟩

/-- The unit `M ⟶ A' ⊗_A M` is killed by the multiplication by a generator `a` of `ker f`. -/
lemma smulIdNatTrans_app_comp_extendRestrictScalarsAdj_unit_app
    (ha : RingHom.ker f = Ideal.span {a}) (M : ModuleCat.{u} A) :
    (smulIdNatTrans a).app M ≫ (extendRestrictScalarsAdj.{u} f).unit.app M = 0 := by
  have h : (a • 𝟙 M) ≫ (ρ_ M).inv ≫ M ◁ unitToRestrictScalars f = 0 :=
    calc _ = (ρ_ M).inv ≫ M ◁ (a • unitToRestrictScalars f) := by simp
      _ = 0 := by
        rw [smul_unitToRestrictScalars ha, MonoidalPreadditive.whiskerLeft_zero, comp_zero]
  rw [smulIdNatTrans_app, extendRestrictScalarsAdj_unit_app, reassoc_of% h, zero_comp]

/-- The kernel of the unit `M ⟶ A' ⊗_A M` is the image of the multiplication by a generator
`a` of `ker f`: tensoring with `M` preserves the exactness of `A --a--> A ⟶ A' ⟶ 0`. -/
lemma exact_extendRestrictScalarsAdj_unit_app (hf : Function.Surjective f)
    (ha : RingHom.ker f = Ideal.span {a}) (M : ModuleCat.{u} A) :
    (ShortComplex.mk _ _ (smulIdNatTrans_app_comp_extendRestrictScalarsAdj_unit_app ha M)).Exact :=
  MonoidalCategory.exact_smul_of_exact_map_tensorLeft _
    ((exact_smul_unitToRestrictScalars ha).map_of_epi_of_preservesCokernel
      (tensorLeft M) (epi_unitToRestrictScalars hf) inferInstance)
    ((extendScalarsCompRestrictScalarsIso f).app M).symm
    (by simp [extendRestrictScalarsAdj_unit_app]) _

/-- Extension of scalars is additive, as a left adjoint. -/
instance extendScalars_additive : (extendScalars.{u, u, u} f).Additive :=
  (extendRestrictScalarsAdj.{u} f).left_adjoint_additive

/-- **Extension of scalars along a surjective ring morphism with principal kernel is a
reduction datum.** For `f : A →+* A'` surjective with kernel `(a)`, the extension of scalars
`M ↦ A' ⊗_A M` together with the unit `M ⟶ A' ⊗_A M` is a reduction datum for restriction of
scalars along `f` and the multiplication by `a`. -/
noncomputable def reductionDatum (f : A →+* A') (hf : Function.Surjective f) (a : A)
    (ha : RingHom.ker f = Ideal.span {a}) :
    Functor.ReductionDatum (restrictScalars.{u} f) (smulIdNatTrans a) where
  Φ := extendScalars.{u} f
  r := (extendRestrictScalarsAdj.{u} f).unit
  σ_app_obj := smulIdNatTrans_app_restrictScalars_obj ha
  σ_comp_r := smulIdNatTrans_app_comp_extendRestrictScalarsAdj_unit_app ha
  epi_r := epi_extendRestrictScalarsAdj_unit_app hf
  exact := exact_extendRestrictScalarsAdj_unit_app hf ha
  quasiIso_map φ _ h₁ h₂ := by
    have := restrictScalars_full_of_surjective.{u} f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (extendScalarsCompRestrictScalarsIso f) φ h₁ h₂

/-- **The reduction of a K-flat complex is its derived base change.** For `f : A →+* A'`
surjective with kernel `(a)` and a K-flat complex `P` of `A`-modules, the reduction
`P ⟶ Res (A' ⊗_A P)` exhibits `A' ⊗_A P` as the derived base change of `P`. -/
theorem isDerivedBaseChange_Q_map_complexMap [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A')] (hf : Function.Surjective f)
    (ha : RingHom.ker f = Ideal.span {a}) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    IsDerivedBaseChange (f := f)
      (DerivedCategory.Q.map ((reductionDatum f hf a ha).complexMap P) ≫
        (restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app _) := by
  have := restrictScalars_full_of_surjective.{u} f hf
  exact (reductionDatum f hf a ha).bijective_comp_map P hP

end Reduction

section Comp

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A'')] {f : A →+* A'} {g : A' →+* A''} {gf : A →+* A''}

/-- On complexes, restricting scalars along `g` and then along `f` is restricting scalars along
`g ∘ f`: the identity maps, as a chain map. -/
noncomputable def restrictScalarsCompComplexMap (hgf : gf = g.comp f)
    (L : CochainComplex (ModuleCat.{u} A'') ℤ) :
    ((restrictScalars.{u} f).mapHomologicalComplex _).obj
        (((restrictScalars.{u} g).mapHomologicalComplex _).obj L) ⟶
      ((restrictScalars.{u} gf).mapHomologicalComplex _).obj L :=
  (NatTrans.mapHomologicalComplex (restrictScalarsComp' f g gf hgf).inv (.up ℤ)).app L

omit [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A'')] in
/-- The chain map `restrictScalarsCompComplexMap` is the identity on elements. -/
@[simp]
lemma restrictScalarsCompComplexMap_f_apply (hgf : gf = g.comp f)
    (L : CochainComplex (ModuleCat.{u} A'') ℤ) (i : ℤ) (x : L.X i) :
    ((restrictScalarsCompComplexMap hgf L).f i).hom x = x :=
  rfl

/-- The image in the derived category of a chain map `K ⟶ Res_g L`, restricted along `f`, is
the restriction along `f` of its image, up to the composition isomorphism
`derivedRestrictScalarsCompIso`. -/
lemma Q_map_restrictScalars_comp (hgf : gf = g.comp f) {K : CochainComplex (ModuleCat.{u} A') ℤ}
    {L : CochainComplex (ModuleCat.{u} A'') ℤ}
    (χ : K ⟶ ((restrictScalars.{u} g).mapHomologicalComplex _).obj L) :
    DerivedCategory.Q.map (((restrictScalars.{u} f).mapHomologicalComplex _).map χ ≫
        restrictScalarsCompComplexMap hgf L) ≫
        (restrictScalars.{u} gf).mapDerivedCategoryFactors.inv.app L =
      (restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app K ≫
        (derivedRestrictScalars f).map (DerivedCategory.Q.map χ ≫
          (restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app L) ≫
        (derivedRestrictScalarsCompIso hgf).hom.app (DerivedCategory.Q.obj L) := by
  rw [← cancel_mono ((restrictScalars.{u} gf).mapDerivedCategoryFactors.hom.app L),
    Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id, Category.assoc]
  have h₁ : (derivedRestrictScalarsCompIso hgf).hom.app (DerivedCategory.Q.obj L) ≫
      (restrictScalars.{u} gf).mapDerivedCategoryFactors.hom.app L =
        (derivedRestrictScalars f).map
          ((restrictScalars.{u} g).mapDerivedCategoryFactors.hom.app L) ≫
        (restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app
          (((restrictScalars.{u} g).mapHomologicalComplex _).obj L) ≫
        DerivedCategory.Q.map (restrictScalarsCompComplexMap hgf L) := by
    simp only [derivedRestrictScalarsCompIso, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac,
      ← Functor.mapDerivedCategoryCompIso_fac (restrictScalars g) (restrictScalars f) L]
    simp only [Functor.comp_obj, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
    have h₂ : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (restrictScalars.{u} g ⋙ restrictScalars.{u} f)) (.up ℤ)).hom.app L ≫
          (NatTrans.mapHomologicalComplex (restrictScalarsComp' f g gf hgf).inv (.up ℤ)).app L =
        restrictScalarsCompComplexMap hgf L := by
      ext i x
      rfl
    rw [← Functor.map_comp, h₂]
  rw [h₁, Functor.map_comp_assoc, ← Functor.map_comp_assoc (derivedRestrictScalars f)
    ((restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app L), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]

end Comp

end ModuleCat
