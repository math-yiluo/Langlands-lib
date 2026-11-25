/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.Bidual
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Biduality for sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For a sheaf of modules `M` over `R`,
the biduality morphism `M ⟶ Hom(Hom(M, R), R)` (`SheafOfModules.bidual`) is natural in `M`, and
it is an isomorphism if `M` is finite locally free (`SheafOfModules.isIso_bidual`): it is then
bijective on sections over every object on which `M` is free.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

section

variable {U : C}
/-- A morphism `M|_U ⟶ N|_U` of sheaves of modules over `Over U`, as a morphism between the
restrictions to `Over U` of the underlying presheaves of modules. -/
noncomputable def toRestrictOverHom {M N : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U) :
    (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val where
  app W := f.val.app W
  naturality _ := f.val.naturality _

lemma toRestrictOverHom_app {M N : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U) (W) (x) :
    (toRestrictOverHom f).app W x = f.val.app W x := rfl

lemma toRestrictOverHom_comp {M N P : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U)
    (g : N.over U ⟶ P.over U) :
    toRestrictOverHom (f ≫ g) = toRestrictOverHom f ≫ toRestrictOverHom g := rfl


lemma toRestrictOverHom_id (M : SheafOfModules.{u} 𝓡) :
    toRestrictOverHom (𝟙 (M.over U)) = 𝟙 _ := rfl

lemma toRestrictOverHom_zero (M N : SheafOfModules.{u} 𝓡) :
    toRestrictOverHom (0 : M.over U ⟶ N.over U) = 0 := rfl

lemma toRestrictOverHom_add {M N : SheafOfModules.{u} 𝓡} (f g : M.over U ⟶ N.over U) :
    toRestrictOverHom (f + g) = toRestrictOverHom f + toRestrictOverHom g := rfl

lemma toRestrictOverHom_sum {M N : SheafOfModules.{u} 𝓡} {ι : Type*} (t : Finset ι)
    (f : ι → (M.over U ⟶ N.over U)) :
    toRestrictOverHom (∑ i ∈ t, f i) = ∑ i ∈ t, toRestrictOverHom (f i) :=
  map_sum (AddMonoidHom.mk' toRestrictOverHom toRestrictOverHom_add :
      (M.over U ⟶ N.over U) →+ ((PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
        (PresheafOfModules.restrictOver R.obj U).obj N.val)) f t

end

variable (M : SheafOfModules.{u} 𝓡)

/-- The biduality morphism `M ⟶ Hom(Hom(M, R), R)`, sending a section `m` to evaluation at
`m`. -/
noncomputable def bidual : M ⟶ homObj (homObj M (unit 𝓡)) (unit 𝓡) where
  val := PresheafOfModules.bidual (R := R.obj) M.val

variable {M} in
/-- The biduality morphism is natural. -/
@[reassoc]
lemma bidual_naturality {M' : SheafOfModules.{u} 𝓡} (f : M ⟶ M') :
    f ≫ bidual M' = bidual M ≫ homObjMap (homObjMap f (𝟙 _)) (𝟙 _) := by
  -- Reducing to `PresheafOfModules.bidual_naturality` makes the kernel very slow.
  ext1
  ext X m : 3
  refine PresheafOfModules.hom_ext
    (M₁ := (PresheafOfModules.restrictOver R.obj X.unop).obj
      (PresheafOfModules.homObj M'.val (PresheafOfModules.unit _)))
    (M₂ := (PresheafOfModules.restrictOver R.obj X.unop).obj (PresheafOfModules.unit _))
    fun W ↦ ?_
  ext φ
  change φ.app (op (Over.mk (𝟙 W.unop.left))) (M'.val.map W.unop.hom.op (f.val.app X m)) =
    φ.app (op (Over.mk (𝟙 W.unop.left))) (f.val.app (op W.unop.left) (M.val.map W.unop.hom.op m))
  rw [PresheafOfModules.naturality_apply]

variable {U : C} in
/-- If `M` is free of finite rank on `U`, then the biduality morphism is bijective on sections over
every `V ⟶ U`. -/
lemma bidual_app_bijective_of_iso_free [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] {I : Type u} [Finite I]
    (e : free I ≅ M.over U) {V : C} (g : V ⟶ U) :
    Function.Bijective ((bidual M).val.app (op V)) := by
  classical
  let := Fintype.ofFinite I
  let S (j : I) : (unit 𝓡).over U ⟶ M.over U := Sigma.ι (fun _ ↦ unit _) j ≫ e.hom
  let Cc (j : I) : M.over U ⟶ (unit 𝓡).over U :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = j then 𝟙 (unit _) else 0)
  have hsc (i j : I) : S j ≫ Cc i = if j = i then 𝟙 _ else 0 := by
    simp only [S, Cc, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc]
    rfl
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
      Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i = 𝟙 (free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_comp_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, Cc i ≫ S i = 𝟙 _ := by
    calc ∑ i, Cc i ≫ S i = e.inv ≫ (∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
          Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i) ≫ e.hom := by
          simp only [Cc, S, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
          rfl
      _ = 𝟙 _ := by rw [hsum, Category.id_comp, Iso.inv_hom_id]
  refine PresheafOfModules.bidual_app_bijective_of_hom (A := M.val) (U := U)
    (fun j ↦ toRestrictOverHom (S j)) (fun j ↦ toRestrictOverHom (Cc j)) (fun i j ↦ ?_) ?_ g
  · refine (congrArg toRestrictOverHom (hsc i j)).trans ?_
    split_ifs
    · exact toRestrictOverHom_id _
    · exact toRestrictOverHom_zero _ _
  · exact (toRestrictOverHom_sum Finset.univ (fun i ↦ Cc i ≫ S i)).symm.trans
      ((congrArg toRestrictOverHom htot).trans (toRestrictOverHom_id M))

/-- **Biduality.** The biduality morphism `M ⟶ Hom(Hom(M, R), R)` of a finite locally free
sheaf of modules is an isomorphism: it is bijective on sections over every object on which `M`
is free. -/
theorem isIso_bidual [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [M.IsFiniteLocallyFree] :
    IsIso (bidual M) := by
  obtain ⟨q, hq, hf⟩ := IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  have hb (V : C) (i : q.I) (g : V ⟶ q.X i) :
      Function.Bijective ((bidual M).val.app (op V)) := by
    have := (hf.isFiniteType i).finite
    have := hq.isIso i
    exact bidual_app_bijective_of_iso_free M (asIso (q.generators i).π) g
  have : IsIso ((toSheaf (𝓡)).map (bidual M)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨Presheaf.isLocallyInjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).2⟩
  exact isIso_of_reflects_iso _ (toSheaf (𝓡))

end SheafOfModules

