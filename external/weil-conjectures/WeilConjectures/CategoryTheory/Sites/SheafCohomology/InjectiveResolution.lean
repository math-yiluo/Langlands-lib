/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Homology.HomologyPiAb

/-!
# Computing the cohomology presheaves with an injective resolution

Let `F` be an abelian sheaf on a site and `F ⟶ I^•` an injective resolution. For every object
`V`, the group `H^n(V, F) = Ext^n(ℤ_V^#, F)` (`CategoryTheory.Sheaf.cohomologyPresheaf`) is the
`n`-th cohomology of the complex of abelian groups `I^•(V)`, naturally in `V`.

This rests on two facts:
* a morphism `ℤ_V^# ⟶ I` from the sheafified free abelian presheaf on `V` is a section of `I`
  over `V` (`CategoryTheory.Sheaf.sheafifyFreeYonedaHomAddEquiv`);
* `Ext^n(X, Y)` is the `n`-th cohomology of `Hom(X, I^•)` for an injective resolution `I^•` of `Y`
  (`CategoryTheory.InjectiveResolution.homologyAddEquivExt`, stated for any complex of abelian
  groups identified degreewise with `Hom(X, I^•)`).

## Main definitions

- `CategoryTheory.Sheaf.complexSections`: the presheaf of complexes `V ↦ K^•(V)` attached to a
  complex of sheaves `K`.
- `CategoryTheory.Sheaf.cohomologyPresheafIso`: for an injective resolution `I^•` of `F`, the
  isomorphism of presheaves `V ↦ H^n(I^•(V))` with `F.cohomologyPresheaf n`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y)

/-- In degree `0`, the class `R.extMk f` vanishes only if `f` does. -/
lemma extMk_eq_zero_iff_of_zero (f : X ⟶ R.cocomplex.X 0) (hf : f ≫ R.cocomplex.d 0 1 = 0) :
    R.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact R.extMk_zero 1 rfl⟩
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_zero, CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1)
    (by lia)] at h
  obtain ⟨g, hg⟩ := h
  have hg0 : g = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by lia)).eq_of_tgt _ _
  rw [hg0, zero_comp] at hg
  simpa using hg.symm

variable {M : CochainComplex AddCommGrpCat.{w} ℕ} (θ : ∀ n, M.X n ≃+ (X ⟶ R.cocomplex.X n))
  (hθ : ∀ n (m : M.X n), θ (n + 1) (M.d n (n + 1) m) = θ n m ≫ R.cocomplex.d n (n + 1))

omit [HasExt.{w} C] in
include hθ in
lemma comp_d_eq_zero_of_d_eq_zero {n : ℕ} (m : M.X n) (hm : M.d n (n + 1) m = 0) :
    θ n m ≫ R.cocomplex.d n (n + 1) = 0 := by
  rw [← hθ, hm, map_zero]

omit [HasExt.{w} C] in
include hθ in
lemma θ_iCycles_comp_d (n : ℕ) (z : M.cycles n) :
    θ n (M.iCycles n z) ≫ R.cocomplex.d n (n + 1) = 0 :=
  comp_d_eq_zero_of_d_eq_zero R θ hθ _ (by
    rw [← ConcreteCategory.comp_apply, M.iCycles_d]
    rfl)

/-- The map from the cycles of `M` in degree `n` to `Ext^n(X, Y)`. -/
noncomputable def cyclesToExt (n : ℕ) : M.cycles n →+ Ext X Y n where
  toFun z := R.extMk (θ n (M.iCycles n z)) (n + 1) rfl (θ_iCycles_comp_d R θ hθ n z)
  map_zero' := by simp
  map_add' z z' := by
    simp only [map_add]
    rw [R.add_extMk]

lemma cyclesToExt_apply (n : ℕ) (z : M.cycles n) :
    cyclesToExt R θ hθ n z = R.extMk (θ n (M.iCycles n z)) (n + 1) rfl
      (θ_iCycles_comp_d R θ hθ n z) :=
  rfl

lemma toCycles_cyclesToExt (n : ℕ) (m : M.X ((ComplexShape.up ℕ).prev n)) :
    cyclesToExt R θ hθ n (M.toCycles _ n m) = 0 := by
  rw [cyclesToExt_apply]
  obtain _ | p := n
  · have : M.iCycles 0 (M.toCycles _ 0 m) = 0 := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i,
        HomologicalComplex.shape _ _ _ (by simp)]
      rfl
    simp [this]
  · rw [R.extMk_eq_zero_iff _ _ _ _ p rfl]
    refine ⟨θ p ((M.XIsoOfEq (CochainComplex.prev_nat_succ p)).hom m), ?_⟩
    rw [← hθ]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      HomologicalComplex.toCycles_i, HomologicalComplex.XIsoOfEq_hom_comp_d]

/-- The map from the cohomology of `M` in degree `n` to `Ext^n(X, Y)`. -/
noncomputable def homologyToExt (n : ℕ) : M.homology n ⟶ AddCommGrpCat.of (Ext X Y n) :=
  (M.sc n).descHomology (AddCommGrpCat.ofHom (cyclesToExt R θ hθ n)) (by
    ext m
    exact toCycles_cyclesToExt R θ hθ n m)

lemma homologyToExt_homologyπ (n : ℕ) (z : M.cycles n) :
    homologyToExt R θ hθ n (M.homologyπ n z) = cyclesToExt R θ hθ n z := by
  rw [← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom ((M.sc n).π_descHomology _ _) z

lemma bijective_homologyToExt (n : ℕ) : Function.Bijective (homologyToExt R θ hθ n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨z, rfl⟩ := M.ab_homologyπ_surjective n h
    rw [homologyToExt_homologyπ, cyclesToExt_apply] at hh
    obtain _ | p := n
    · rw [extMk_eq_zero_iff_of_zero, AddEquivClass.map_eq_zero_iff] at hh
      rw [(M.ab_iCycles_injective 0 (hh.trans (map_zero _).symm)), map_zero]
    · obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff _ _ _ _ p rfl).1 hh
      rw [M.ab_homologyπ_eq_zero_iff' p (p + 1) (by simp)]
      refine ⟨(θ p).symm g, M.ab_iCycles_injective _ ((θ (p + 1)).injective ?_)⟩
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, hθ,
        AddEquiv.apply_symm_apply, hg]
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
    obtain ⟨z, hz⟩ := M.ab_exists_iCycles_eq' n (n + 1) (by simp) ((θ n).symm f)
      ((θ (n + 1)).injective (by rw [hθ, AddEquiv.apply_symm_apply, hf, map_zero]))
    refine ⟨M.homologyπ n z, ?_⟩
    rw [homologyToExt_homologyπ, cyclesToExt_apply]
    congr 1
    rw [hz, AddEquiv.apply_symm_apply]

/-- **`Ext` via an injective resolution.** If `R` is an injective resolution of `Y` and `M` is a
complex of abelian groups identified degreewise with `Hom(X, R^•)` compatibly with the
differentials, then the cohomology of `M` is `Ext^•(X, Y)`. -/
noncomputable def homologyIsoExt (n : ℕ) : M.homology n ≅ AddCommGrpCat.of (Ext X Y n) :=
  have := (ConcreteCategory.isIso_iff_bijective _).2 (bijective_homologyToExt R θ hθ n)
  asIso (homologyToExt R θ hθ n)

@[simp]
lemma homologyIsoExt_hom_homologyπ (n : ℕ) (z : M.cycles n) :
    (homologyIsoExt R θ hθ n).hom (M.homologyπ n z) =
      R.extMk (θ n (M.iCycles n z)) (n + 1) rfl (θ_iCycles_comp_d R θ hθ n z) :=
  homologyToExt_homologyπ R θ hθ n z

/-- Naturality of `homologyIsoExt` in `X`. -/
lemma homologyIsoExt_naturality {X' : C} (g : X' ⟶ X) {M' : CochainComplex AddCommGrpCat.{w} ℕ}
    (θ' : ∀ n, M'.X n ≃+ (X' ⟶ R.cocomplex.X n))
    (hθ' : ∀ n (m : M'.X n), θ' (n + 1) (M'.d n (n + 1) m) = θ' n m ≫ R.cocomplex.d n (n + 1))
    (ψ : M ⟶ M') (hψ : ∀ n (m : M.X n), θ' n (ψ.f n m) = g ≫ θ n m) (n : ℕ)
    (h : M.homology n) :
    (homologyIsoExt R θ' hθ' n).hom (HomologicalComplex.homologyMap ψ n h) =
      (Ext.mk₀ g).comp ((homologyIsoExt R θ hθ n).hom h) (zero_add n) := by
  obtain ⟨z, rfl⟩ := M.ab_homologyπ_surjective n h
  rw [← ConcreteCategory.comp_apply (M.homologyπ n) (HomologicalComplex.homologyMap ψ n),
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
    homologyIsoExt_hom_homologyπ, homologyIsoExt_hom_homologyπ, R.mk₀_comp_extMk]
  congr 1
  rw [← hψ, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.cyclesMap_i]

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism from the free abelian presheaf on `V` is a section over `V`. -/
noncomputable def freeYonedaHomAddEquiv (V : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj V ⋙ AddCommGrpCat.free ⟶ P) ≃+ P.obj (op V) where
  toFun φ := φ.app (op V) (FreeAbelianGroup.of (𝟙 V))
  invFun s :=
    { app T := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g ↦ P.map g.op s)
      naturality T T' g := by
        apply AddCommGrpCat.hom_ext
        refine FreeAbelianGroup.lift_ext _ _ fun x ↦ ?_
        change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of x)) =
          P.map g (FreeAbelianGroup.lift _ (FreeAbelianGroup.of x))
        rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
          FreeAbelianGroup.lift_apply_of]
        change P.map (g.unop ≫ x).op s = _
        rw [op_comp, P.map_comp]
        rfl }
  left_inv φ := by
    ext T : 2
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext _ _ fun x ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of x) = _
    rw [FreeAbelianGroup.lift_apply_of]
    have := ConcreteCategory.congr_hom (φ.naturality x.op) (FreeAbelianGroup.of (𝟙 V))
    refine this.symm.trans ?_
    change φ.app T (FreeAbelianGroup.map _ (FreeAbelianGroup.of (𝟙 V))) = _
    rw [FreeAbelianGroup.map_of_apply]
    simp
  right_inv s := by
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of _) = s
    rw [FreeAbelianGroup.lift_apply_of]
    simp
  map_add' _ _ := rfl

lemma freeYonedaHomAddEquiv_apply (V : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (φ : yoneda.obj V ⋙ AddCommGrpCat.free ⟶ P) :
    freeYonedaHomAddEquiv V P φ = φ.app (op V) (FreeAbelianGroup.of (𝟙 V)) :=
  rfl

variable [HasSheafify J AddCommGrpCat.{v}]

/-- A morphism from the sheafified free abelian presheaf `ℤ_V^#` on `V` to an abelian sheaf `I`
is a section of `I` over `V`. -/
noncomputable def sheafifyFreeYonedaHomAddEquiv (V : C) (I : Sheaf J AddCommGrpCat.{v}) :
    ((presheafToSheaf J _).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ I) ≃+ I.obj.obj (op V) :=
  ((sheafificationAdjunction J _).homAddEquiv _ I).trans (freeYonedaHomAddEquiv V I.obj)

lemma sheafifyFreeYonedaHomAddEquiv_comp (V : C) {I I' : Sheaf J AddCommGrpCat.{v}}
    (f : (presheafToSheaf J _).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ I) (g : I ⟶ I') :
    sheafifyFreeYonedaHomAddEquiv V I' (f ≫ g) =
      g.hom.app (op V) (sheafifyFreeYonedaHomAddEquiv V I f) := by
  simp only [sheafifyFreeYonedaHomAddEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

lemma sheafifyFreeYonedaHomAddEquiv_map_comp {V V' : C} (h : V' ⟶ V)
    {I : Sheaf J AddCommGrpCat.{v}}
    (f : (presheafToSheaf J _).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ I) :
    sheafifyFreeYonedaHomAddEquiv V' I ((presheafToSheaf J _).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map h)) ≫ f) =
      I.obj.map h.op (sheafifyFreeYonedaHomAddEquiv V I f) := by
  simp only [sheafifyFreeYonedaHomAddEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_left]
  erw [freeYonedaHomAddEquiv_apply, freeYonedaHomAddEquiv_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  have := ConcreteCategory.congr_hom
    (((sheafificationAdjunction J _).homEquiv _ I f).naturality h.op) (FreeAbelianGroup.of (𝟙 V))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  have e : (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map h)).app
      (op V') (FreeAbelianGroup.of (𝟙 V')) =
      (yoneda.obj V ⋙ AddCommGrpCat.free).map h.op (FreeAbelianGroup.of (𝟙 V)) := by
    erw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply]
    simp
  erw [e]
  exact this

/-- The presheaf of complexes of sections `V ↦ K^•(V)` of a complex of abelian sheaves `K`. -/
@[simps]
noncomputable def complexSections (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) :
    Cᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj V :=
    { X n := (K.X n).obj.obj V
      d i j := (K.d i j).hom.app V
      shape i j h := by rw [K.shape i j h]; rfl
      d_comp_d' i j k _ _ := by
        rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, K.d_comp_d]
        rfl }
  map f :=
    { f n := (K.X n).obj.map f
      comm' i j _ := (K.d i j).hom.naturality f }

lemma sheafifyFreeYonedaHomAddEquiv_symm_comp (V : C) {I I' : Sheaf J AddCommGrpCat.{v}}
    (g : I ⟶ I') (s : I.obj.obj (op V)) :
    (sheafifyFreeYonedaHomAddEquiv V I).symm s ≫ g =
      (sheafifyFreeYonedaHomAddEquiv V I').symm (g.hom.app (op V) s) := by
  apply (sheafifyFreeYonedaHomAddEquiv V I').injective
  rw [sheafifyFreeYonedaHomAddEquiv_comp, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

lemma map_comp_sheafifyFreeYonedaHomAddEquiv_symm {V V' : C} (h : V' ⟶ V)
    {I : Sheaf J AddCommGrpCat.{v}} (s : I.obj.obj (op V)) :
    (presheafToSheaf J _).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map h)) ≫
      (sheafifyFreeYonedaHomAddEquiv V I).symm s =
      (sheafifyFreeYonedaHomAddEquiv V' I).symm (I.obj.map h.op s) := by
  apply (sheafifyFreeYonedaHomAddEquiv V' I).injective
  rw [sheafifyFreeYonedaHomAddEquiv_map_comp, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] {F : Sheaf J AddCommGrpCat.{v}}
  (R : InjectiveResolution F)
lemma cohomologyPresheaf_map_apply
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {V V' : Cᵒᵖ} (h : V ⟶ V')
    (y : F.H' n V.unop) :
    (F.cohomologyPresheaf n).map h y = (Ext.mk₀ ((presheafToSheaf J _).map
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map h.unop)))).comp y
        (zero_add n) :=
  rfl


/-- The isomorphism `H^n(I^•(V)) ≅ H^n(V, F)` for an injective resolution `I^•` of `F`. -/
noncomputable def cohomologyPresheafIsoApp (n : ℕ) (V : Cᵒᵖ) :
    ((complexSections R.cocomplex).obj V).homology n ≅ (F.cohomologyPresheaf n).obj V :=
  R.homologyIsoExt (fun _ ↦ (sheafifyFreeYonedaHomAddEquiv V.unop _).symm)
    (fun _ _ ↦ (sheafifyFreeYonedaHomAddEquiv_symm_comp _ _ _).symm) n

lemma cohomologyPresheafIsoApp_naturality (n : ℕ) {V V' : Cᵒᵖ} (h : V ⟶ V')
    (x : ((complexSections R.cocomplex).obj V).homology n) :
    (cohomologyPresheafIsoApp R n V').hom
        (HomologicalComplex.homologyMap ((complexSections R.cocomplex).map h) n x) =
      (F.cohomologyPresheaf n).map h ((cohomologyPresheafIsoApp R n V).hom x) := by
  rw [cohomologyPresheaf_map_apply]
  exact R.homologyIsoExt_naturality _ _ _ _ _ ((complexSections R.cocomplex).map h)
    (fun _ m ↦ (map_comp_sheafifyFreeYonedaHomAddEquiv_symm h.unop m).symm) n x

/-- **Cohomology presheaves via an injective resolution.** For an injective resolution `I^•` of
`F`, the presheaf `V ↦ H^n(I^•(V))` is the cohomology presheaf `V ↦ H^n(V, F)`. -/
noncomputable def cohomologyPresheafIso (n : ℕ) :
    complexSections R.cocomplex ⋙ HomologicalComplex.homologyFunctor _ _ n ≅
      F.cohomologyPresheaf n :=
  NatIso.ofComponents (cohomologyPresheafIsoApp R n) (fun h ↦
    AddCommGrpCat.ext fun x ↦ cohomologyPresheafIsoApp_naturality R n h x)

end CategoryTheory.Sheaf
