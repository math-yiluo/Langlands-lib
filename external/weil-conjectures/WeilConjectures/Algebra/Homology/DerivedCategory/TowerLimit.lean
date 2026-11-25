/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Limits of towers of complexes with surjective transitions are homotopy limits

Let `T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ` be a tower of complexes of modules whose transitions are
degreewise surjective, and let `c` be a limit cone of `T` (computed degreewise). In each degree
the sequence `0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact, so that it is a short exact
sequence of complexes. Its image in the derived category is the Milnor triangle, hence the
image of `c` in the derived category is a homotopy limit cone.

This uses that the localization functor `Q` to the derived category preserves products when
products are exact (`AB4*`) and there are K-injective resolutions: products of K-injective
complexes are K-injective, and a product of quasi-isomorphisms is a quasi-isomorphism.

## Main statements

- `HomologicalComplex.quasiIso_limMap`: if limits of shape `J` are exact, then a limit of
  quasi-isomorphisms is a quasi-isomorphism.
- `DerivedCategory.isLimitFanQ`: `Q` sends products of complexes to products.
- `DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`: the image in the derived category of a
  limit cone of a tower of complexes of modules with degreewise surjective transitions is a
  homotopy limit cone.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace HomologicalComplex

variable (C : Type*) [Category* C] [Abelian C] {ι : Type*} (c : ComplexShape ι)
  (J : Type*) [Category* J] [HasLimitsOfShape J C]

variable {C c J} in
/-- The degree `i` term of the limit of a diagram of complexes is the limit of the degree `i`
terms. -/
noncomputable def limitXIso (F : J ⥤ HomologicalComplex C c) (i : ι) :
    limit (F ⋙ eval C c i) ≅ (limit F).X i :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (isLimitOfPreserves (eval C c i) (limit.isLimit F))

variable {C c J} in
@[reassoc (attr := simp)]
lemma limitXIso_hom_π_f (F : J ⥤ HomologicalComplex C c) (i : ι) (k : J) :
    (limitXIso F i).hom ≫ (limit.π F k).f i = limit.π (F ⋙ eval C c i) k :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The limit of a diagram of complexes is computed degreewise. -/
noncomputable def functorEquivalenceInverseCompMapHomologicalComplexLim :
    (functorEquivalence C c J).inverse ⋙ lim.mapHomologicalComplex c ≅ lim :=
  NatIso.ofComponents (fun F ↦ Hom.isoOfComponents (limitXIso F) fun i j _ ↦
    (isLimitOfPreserves (eval C c j) (limit.isLimit F)).hom_ext fun k ↦ by
      dsimp
      rw [assoc, ← Hom.comm, limitXIso_hom_π_f_assoc, assoc, limitXIso_hom_π_f, limMap_π]
      rfl) fun {F G} f ↦ by
    ext i
    refine (isLimitOfPreserves (eval C c i) (limit.isLimit G)).hom_ext fun k ↦ ?_
    dsimp
    simp only [assoc, limitXIso_hom_π_f, ← comp_f, limMap_π]
    rw [comp_f, limitXIso_hom_π_f_assoc]
    simp

variable {C c J}

set_option backward.defeqAttrib.useBackward true in
/-- If limits of shape `J` are exact, a limit of quasi-isomorphisms of complexes is a
quasi-isomorphism. -/
lemma quasiIso_limMap [HasExactLimitsOfShape J C] {F₁ F₂ : J ⥤ HomologicalComplex C c}
    (f : F₁ ⟶ F₂) [∀ j, QuasiIso (f.app j)] : QuasiIso (limMap f) := by
  have : QuasiIso ((functorEquivalence.inverse C c J).map f) := by
    rw [quasiIso_functorCategory_iff]
    intro j
    exact inferInstanceAs (QuasiIso (f.app j))
  refine ((quasiIso C c).arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso
    (functorEquivalenceInverseCompMapHomologicalComplexLim C c J)).app (Arrow.mk f))).1 ?_
  have : (lim : (J ⥤ C) ⥤ C).PreservesHomology := inferInstance
  dsimp
  simp only [mem_quasiIso_iff]
  infer_instance

end HomologicalComplex

namespace DerivedCategory

open Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] {J : Type*}

set_option backward.defeqAttrib.useBackward true in
/-- The image in the derived category of a product of K-injective complexes is a product. -/
noncomputable def isLimitFanQOfIsKInjective [HasLimitsOfShape (Discrete J) C]
    (I : J → CochainComplex C ℤ) [∀ j, (I j).IsKInjective] :
    IsLimit (Fan.mk (Q.obj (∏ᶜ I)) fun j ↦ Q.map (Pi.π I j)) := by
  let hK := HomotopyCategory.isLimitFanQuotient C (.up ℤ) (productIsProduct I)
  have hprop : (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
      ((HomotopyCategory.quotient _ _).obj (∏ᶜ I)) :=
    ObjectProperty.prop_of_isLimit _ hK fun j ↦
      (CochainComplex.isKInjective_iff_rightOrthogonal _).1 inferInstance
  let X : HomotopyCategory.KInjectives C := ⟨_, hprop⟩
  let F' : Fan fun j ↦ HomotopyCategory.KInjectives.mk (I j) :=
    Fan.mk X fun j ↦ ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (Pi.π I j))
  have hF' : IsLimit F' := isLimitOfReflects (ObjectProperty.ι _)
    ((isLimitMapConeFanMkEquiv _ _ _).symm hK)
  let hQh := isLimitMapConeFanMkEquiv _ _ _
    (isLimitOfPreserves HomotopyCategory.KInjectives.Qh hF')
  refine Fan.IsLimit.ofIsos hQh (fun j ↦ ((quotientCompQhIso C).app (I j)).symm)
    ((quotientCompQhIso C).app (∏ᶜ I)).symm fun j ↦ ?_
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (quotientCompQhIso C).hom.naturality (Pi.π I j)

/-- If products of shape `J` are exact, the localization functor `Q` to the derived category
sends products of complexes to products. -/
noncomputable def isLimitFanQ [HasLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete J) C] (K : J → CochainComplex C ℤ) :
    IsLimit (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j)) := by
  choose I hI i _ hi using fun j ↦ HasKInjectiveResolutions.exists_isKInjective (K j)
  have (j : Discrete J) :
      QuasiIso ((Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor I)
        fun j ↦ i j.as).app j) := hi j.as
  have : QuasiIso (Limits.Pi.map i) := HomologicalComplex.quasiIso_limMap _
  refine Fan.IsLimit.ofIsos (isLimitFanQOfIsKInjective I)
    (fun j ↦ asIso (Q.map (i j))) (asIso (Q.map (Limits.Pi.map i))) fun j ↦ ?_
  simp [← Functor.map_comp]

instance [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C] :
    PreservesLimitsOfShape (Discrete J) (Q (C := C)) :=
  have (K : J → CochainComplex C ℤ) : PreservesLimit (Discrete.functor K) Q :=
    preservesLimit_of_preserves_limit_cone (productIsProduct K)
      ((isLimitMapConeFanMkEquiv _ _ _).symm (isLimitFanQ K))
  preservesLimitsOfShape_of_discrete Q

end DerivedCategory

namespace CategoryTheory.Limits

/-- For a cone `c` over a tower `F` and an endomorphism `t` of a product `∏ Fₙ` with components
`∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`, the composite `c.pt ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ` vanishes. -/
lemma Fan.IsLimit.lift_π_comp_one_sub_eq_zero {C : Type*} [Category* C] [Preadditive C]
    {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (Opposite.op n)} (hP : IsLimit P)
    (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (c : Cone F) :
    Fan.IsLimit.lift hP (fun n ↦ c.π.app (Opposite.op n)) ≫ (𝟙 P.pt - t) = 0 :=
  Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, ht]

/-- For a limit cone `c` over a tower `F`, the map `c.pt ⟶ ∏ Fₙ` is a kernel of `1 - t`, where
`t : ∏ Fₙ ⟶ ∏ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
noncomputable def Fan.IsLimit.isLimitKernelForkOneSub {C : Type*} [Category* C] [Preadditive C]
    {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (Opposite.op n)} (hP : IsLimit P)
    (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    {c : Cone F} (hc : IsLimit c) :
    IsLimit (KernelFork.ofι _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} h hh ↦ hc.lift (Cone.mk W (NatTrans.ofOpSequence (fun n ↦ h ≫ P.proj n)
      fun n ↦ by
        rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at hh
        have hh' : h ≫ t ≫ P.proj n = h ≫ P.proj n := by rw [← Category.assoc, ← hh]
        rw [Category.assoc, ← ht, hh']
        simp)))
    (fun {W} h hh ↦ Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp)
    (fun {W} h hh m hm ↦ hc.hom_ext fun n ↦ by
      rw [hc.fac]
      simp [← hm])

end CategoryTheory.Limits

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- Elements of a product of modules are determined by their components. -/
lemma ext_of_isLimit_fan {ι : Type*} {M : ι → ModuleCat.{u} R} {P : Fan M} (hP : IsLimit P)
    {x y : P.pt} (h : ∀ i, (P.proj i).hom x = (P.proj i).hom y) : x = y := by
  have := Fan.IsLimit.hom_ext hP (ofHom (LinearMap.toSpanSingleton R _ x))
    (ofHom (LinearMap.toSpanSingleton R _ y)) fun i ↦ by
      ext
      simp [h i]
  simpa using congrArg (fun f : ModuleCat.of R R ⟶ _ ↦ f.hom (1 : R)) this

/-- A family of elements of modules `Mᵢ` comes from an element of a product of the `Mᵢ`. -/
lemma exists_proj_eq_of_isLimit_fan {ι : Type*} {M : ι → ModuleCat.{u} R} {P : Fan M}
    (hP : IsLimit P) (x : ∀ i, M i) : ∃ y : P.pt, ∀ i, (P.proj i).hom y = x i :=
  ⟨(Fan.IsLimit.lift hP fun i ↦ ofHom (LinearMap.toSpanSingleton R _ (x i))).hom 1, fun i ↦ by
    exact (congrArg (fun f : ModuleCat.of R R ⟶ M i ↦ f.hom (1 : R))
      (Fan.IsLimit.fac hP _ i)).trans (one_smul R (x i))⟩

/-- For a tower `F` of modules with surjective transitions, the map `1 - t` on a product
`∏ Fₙ` is surjective, where `t` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: given `y`, the components
`xₙ` of a preimage are chosen inductively, `xₙ₊₁` lifting `xₙ - yₙ`. -/
lemma epi_one_sub_of_epi {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 P.pt - t) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  have hs (n : ℕ) := (ModuleCat.epi_iff_surjective _).1 (hF n)
  let x : ∀ n : ℕ, F.obj (op n) := fun n ↦ Nat.rec (motive := fun n ↦ F.obj (op n)) 0
    (fun n xn ↦ (hs n (xn - (P.proj n).hom y)).choose) n
  have hx (n : ℕ) : (F.map (homOfLE n.le_succ).op).hom (x (n + 1)) = x n - (P.proj n).hom y :=
    (hs n _).choose_spec
  obtain ⟨z, hz⟩ := exists_proj_eq_of_isLimit_fan hP x
  refine ⟨z, ext_of_isLimit_fan hP fun n ↦ ?_⟩
  have h₁ := congrArg (fun f ↦ f.hom z) (ht n)
  simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply] at h₁
  simp only [hom_sub, hom_id, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h₁, hz, hx,
    sub_sub_cancel]

end ModuleCat

namespace DerivedCategory

universe u

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]

/-- The image in the derived category of a limit cone `c` of a tower `T` of complexes of
modules whose transitions are degreewise surjective is a homotopy limit cone: in each degree
`0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact, and the triangle in the derived category
attached to this short exact sequence of complexes is the Milnor triangle. -/
theorem isHomotopyLimit_mapCone_Q_of_epi {T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) :
    IsHomotopyLimit (Q.mapCone c) := by
  let K (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ := T.obj (op n)
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hP : IsLimit P := productIsProduct K
  let t : P.pt ⟶ P.pt := Pi.lift fun n ↦ Pi.π K (n + 1) ≫ T.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ P.proj n = P.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  let S := ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      exact ModuleCat.epi_one_sub_of_epi (F := T ⋙ HomologicalComplex.eval _ _ i)
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hP) (t.f i)
        (fun n ↦ (HomologicalComplex.comp_f _ _ i).symm.trans
          ((congrArg (fun φ ↦ φ.f i) (ht n)).trans (HomologicalComplex.comp_f _ _ i)))
        fun n ↦ hT n i
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  let hQ := isLimitFanQ K
  refine ⟨_, hQ, triangleOfSESδ hS, isomorphic_distinguished _ (triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      Triangle.mk_mor₁, Iso.refl_hom, comp_id, fan_mk_proj, triangleOfSES_mor₁, id_comp]
    exact (Fan.IsLimit.fac hQ (fun n ↦ Q.map (c.π.app (op n))) n).trans (congrArg Q.map
      (Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n).symm |>.trans (Q.map_comp _ _))
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      towerShift, fan_mk_proj, Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.comp_map,
      triangleOfSES, Triangle.mk_mor₂, ← Functor.map_comp, Iso.refl_hom, comp_id,
      Preadditive.sub_comp, Functor.map_sub, CategoryTheory.Functor.map_id,
      Preadditive.comp_sub, id_comp, sub_right_inj, S, P]
    exact (Fan.IsLimit.fac hQ _ n).trans (congrArg Q.map (ht n).symm)
  · simp [triangleOfSES]

end DerivedCategory
