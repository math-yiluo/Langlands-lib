/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Flatness under algebraic inverse image

Source: Stacks Project, Modules on Sites, Tag 05VD, the inverse-image portion of
lemma-pullback-flat, before the final change of rings.
-/

@[expose] public section

universe uC vC uD vD r m w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false


section Sections

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private theorem finite_sections (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    [PreservesFiniteLimits L] {ι : Type} [Finite ι]
    (A : ι → Sheaf J (Type w)) (U : Dᵒᵖ) (x : ∀ i, (L.obj (A i)).obj.obj U) :
    ∃ z : (L.obj (∏ᶜ A)).obj.obj U,
      ∀ i, (L.map (Pi.π A i)).hom.app U z = x i := by
  let E := L ⋙ sheafToPresheaf K (Type w) ⋙ (CategoryTheory.evaluation Dᵒᵖ (Type w)).obj U
  let h := isLimitFanMkObjOfIsLimit E A (fun i ↦ Pi.π A i) (productIsProduct A)
  let z := Fan.IsLimit.lift h (fun i ↦ (↾fun _ : PUnit.{w + 1} ↦ x i))
  refine ⟨z PUnit.unit, ?_⟩
  intro i
  exact congrArg (fun k : PUnit.{w + 1} ⟶ E.obj (A i) ↦ k PUnit.unit)
    (Fan.IsLimit.fac h (fun i ↦ (↾fun _ : PUnit.{w + 1} ↦ x i)) i)

private def equationSub {A B : Sheaf J (Type w)} (f g : A ⟶ B) : Subfunctor A.obj where
  obj U := {x | f.hom.app U x = g.hom.app U x}
  map := by
    intro U V i x hx
    change f.hom.app V (A.obj.map i x) = g.hom.app V (A.obj.map i x)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx]

private def equationSheaf {A B : Sheaf J (Type w)} (f g : A ⟶ B) :
    Sheaf J (Type w) :=
  ⟨(equationSub f g).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply (Subfunctor.isSheaf_iff _
      ((isSheaf_iff_isSheaf_of_type J _).mp A.property)).mpr
    intro U x hx
    apply (((isSheaf_iff_isSheaf_of_type J _).mp B.property).isSeparated _ hx).ext
    intro V i hi
    change f.hom.app _ (A.obj.map i.op x) = g.hom.app _ (A.obj.map i.op x) at hi
    simpa only [NatTrans.naturality_apply] using hi⟩

private def equationι {A B : Sheaf J (Type w)} (f g : A ⟶ B) :
    equationSheaf f g ⟶ A := ⟨(equationSub f g).ι⟩

private theorem equation_condition {A B : Sheaf J (Type w)} (f g : A ⟶ B) :
    equationι f g ≫ f = equationι f g ≫ g := by
  ext U x
  exact x.property

private def equationIsLimit {A B : Sheaf J (Type w)} (f g : A ⟶ B) :
    IsLimit (Fork.ofι (equationι f g) (equation_condition f g)) := by
  refine Fork.IsLimit.mk' _ (fun s ↦ ?_)
  refine ⟨⟨{ app U := ↾fun x ↦ ⟨s.ι.hom.app U x,
      congrArg (fun k : s.pt ⟶ B ↦ k.hom.app U x) s.condition⟩
             naturality := ?_ }⟩, ?_, ?_⟩
  · intro U V i
    ext x
    apply Subtype.ext
    exact congrArg (fun k ↦ k x) (s.ι.hom.naturality i)
  · ext U x
    rfl
  · intro m hm
    ext U x
    apply Subtype.ext
    exact congrArg (fun k ↦ k.hom.app U x) hm

private theorem equation_sections (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    [PreservesFiniteLimits L] {A B : Sheaf J (Type w)} (f g : A ⟶ B)
    (U : Dᵒᵖ) (x : (L.obj A).obj.obj U)
    (hx : (L.map f).hom.app U x = (L.map g).hom.app U x) :
    ∃ z : (L.obj (equationSheaf f g)).obj.obj U,
      (L.map (equationι f g)).hom.app U z = x := by
  let E := L ⋙ sheafToPresheaf K (Type w) ⋙ (CategoryTheory.evaluation Dᵒᵖ (Type w)).obj U
  exact (Types.unique_of_type_equalizer (E.map (equationι f g))
    (by rw [← E.map_comp, ← E.map_comp, equation_condition])
    (isLimitForkMapOfIsLimit E (equation_condition f g) (equationIsLimit f g)) x hx).exists

private def equationsSub {ι : Type} {A : Sheaf J (Type w)}
    {B : ι → Sheaf J (Type w)} (f g : ∀ i, A ⟶ B i) : Subfunctor A.obj where
  obj U := {x | ∀ i, (f i).hom.app U x = (g i).hom.app U x}
  map := by
    intro U V a x hx i
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx i]

private def equationsSheaf {ι : Type} {A : Sheaf J (Type w)}
    {B : ι → Sheaf J (Type w)} (f g : ∀ i, A ⟶ B i) : Sheaf J (Type w) :=
  ⟨(equationsSub f g).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply (Subfunctor.isSheaf_iff _
      ((isSheaf_iff_isSheaf_of_type J _).mp A.property)).mpr
    intro U x hx i
    apply (((isSheaf_iff_isSheaf_of_type J _).mp (B i).property).isSeparated _ hx).ext
    intro V a ha
    have h := ha i
    simpa only [NatTrans.naturality_apply] using h⟩

private def equationsι {ι : Type} {A : Sheaf J (Type w)}
    {B : ι → Sheaf J (Type w)} (f g : ∀ i, A ⟶ B i) :
    equationsSheaf f g ⟶ A := ⟨(equationsSub f g).ι⟩

end Sections

section Operations

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  {R : Sheaf J CommRingCat.{r}}

private abbrev ringSets (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{r} ⋙
    uliftFunctor.{max r m, r})).obj R

private abbrev moduleSets (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})).obj M)

private def ringHom (T : Sheaf J (Type (max r m)))
    (f : ∀ U : Cᵒᵖ, T.obj.obj U → R.obj.obj U)
    (hf : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : T.obj.obj U),
      R.obj.map i (f U x) = f V (T.obj.map i x)) : T ⟶ ringSets R :=
  ⟨{ app U := ↾fun x ↦ ULift.up (f U x)
     naturality := by
       intro U V i
       ext x
       exact ULift.ext (hf i x).symm }⟩

private def moduleHom (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf J (Type (max r m)))
    (f : ∀ U : Cᵒᵖ, T.obj.obj U → M.val.obj U)
    (hf : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : T.obj.obj U),
      M.val.map i (f U x) = f V (T.obj.map i x)) : T ⟶ moduleSets M :=
  ⟨{ app U := ↾fun x ↦ ULift.up (f U x)
     naturality := by
       intro U V i
       ext x
       exact ULift.ext (hf i x).symm }⟩

private def moduleZero (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf J (Type (max r m))) : T ⟶ moduleSets M :=
  moduleHom M T (fun _ _ ↦ 0) (fun _ _ ↦ map_zero _)

private def moduleAdd {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} (a b : T ⟶ moduleSets M) : T ⟶ moduleSets M :=
  moduleHom M T (fun U x ↦ (a.hom.app U x).down + (b.hom.app U x).down) (by
    intro U V i x
    rw [map_add]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

private def moduleSMul {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} (a : T ⟶ ringSets R) (s : T ⟶ moduleSets M) :
    T ⟶ moduleSets M :=
  moduleHom M T (fun U x ↦ (show R.obj.obj U from (a.hom.app U x).down) •
    (show M.val.obj U from (s.hom.app U x).down)) (by
    intro U V i x
    rw [M.val.map_smul]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (s.hom.naturality i)).symm)

private def ringZero (T : Sheaf J (Type (max r m))) : T ⟶ ringSets R :=
  ringHom T (fun _ _ ↦ 0) (fun _ _ ↦ map_zero _)

private def ringAdd {T : Sheaf J (Type (max r m))} (a b : T ⟶ ringSets R) :
    T ⟶ ringSets R :=
  ringHom T (fun U x ↦ (a.hom.app U x).down + (b.hom.app U x).down) (by
    intro U V i x
    rw [map_add]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

private def ringMul {T : Sheaf J (Type (max r m))} (a b : T ⟶ ringSets R) :
    T ⟶ ringSets R :=
  ringHom T (fun U x ↦ (a.hom.app U x).down * (b.hom.app U x).down) (by
    intro U V i x
    rw [map_mul]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

private def moduleSum {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} :
    {n : ℕ} → (Fin n → (T ⟶ moduleSets M)) → (T ⟶ moduleSets M)
  | 0, _ => moduleZero M T
  | _ + 1, a => moduleAdd (a 0) (moduleSum (fun i ↦ a i.succ))

omit [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙
  uliftFunctor.{max r m, r})] in
private theorem moduleSum_apply {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} {n : ℕ}
    (a : Fin n → (T ⟶ moduleSets M)) (U : Cᵒᵖ) (x : T.obj.obj U) :
    @id (M.val.obj U) ((moduleSum a).hom.app U x).down =
      ∑ i, @id (M.val.obj U) ((a i).hom.app U x).down := by
  induction n with
  | zero => simp [moduleSum, moduleZero, moduleHom]
  | succ n ih =>
    change ((a 0).hom.app U x).down + ((moduleSum (fun i ↦ a i.succ)).hom.app U x).down = _
    dsimp only [id] at ih ⊢
    rw [ih, Fin.sum_univ_succ]

private def ringSum {T : Sheaf J (Type (max r m))} :
    {n : ℕ} → (Fin n → (T ⟶ ringSets R)) → (T ⟶ ringSets R)
  | 0, _ => ringZero T
  | _ + 1, a => ringAdd (a 0) (ringSum (fun i ↦ a i.succ))

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})] in
private theorem ringSum_apply {T : Sheaf J (Type (max r m))} {n : ℕ}
    (a : Fin n → (T ⟶ ringSets R)) (U : Cᵒᵖ) (x : T.obj.obj U) :
    @id (R.obj.obj U) ((ringSum a).hom.app U x).down =
      ∑ i, @id (R.obj.obj U) ((a i).hom.app U x).down := by
  induction n with
  | zero => simp [ringSum, ringZero, ringHom]
  | succ n ih =>
    change ((a 0).hom.app U x).down + ((ringSum (fun i ↦ a i.succ)).hom.app U x).down = _
    dsimp only [id] at ih ⊢
    rw [ih, Fin.sum_univ_succ]

private def relationVariables (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) :
    Fin n ⊕ Fin n → Sheaf J (Type (max r m)) :=
  Sum.elim (fun _ ↦ ringSets R) (fun _ ↦ moduleSets M)

private abbrev relationTuple (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) :=
  ∏ᶜ relationVariables M n

private def tupleA (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) (i : Fin n) :
    relationTuple M n ⟶ ringSets R := Pi.π (relationVariables M n) (.inl i)

private def tupleS (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) (i : Fin n) :
    relationTuple M n ⟶ moduleSets M := Pi.π (relationVariables M n) (.inr i)

private def tupleSum (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) :
    relationTuple M n ⟶ moduleSets M :=
  moduleSum (fun i ↦ moduleSMul (tupleA M n i) (tupleS M n i))

private def relationObj (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) :=
  equationSheaf (tupleSum M n) (moduleZero M (relationTuple M n))

private def relationι (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) :
    relationObj M n ⟶ relationTuple M n :=
  equationι (tupleSum M n) (moduleZero M (relationTuple M n))

private def relationA (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) (i : Fin n) :=
  relationι M n ≫ tupleA M n i

private def relationS (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ) (i : Fin n) :=
  relationι M n ≫ tupleS M n i

private theorem relation_equation (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n : ℕ)
    (U : Cᵒᵖ) (x : (relationObj M n).obj.obj U) :
    (∑ i, (@id (R.obj.obj U) ((relationA M n i).hom.app U x).down) •
      (@id (M.val.obj U) ((relationS M n i).hom.app U x).down)) = 0 := by
  have h := congrArg ULift.down x.property
  change @id (M.val.obj U) ((tupleSum M n).hom.app U x.val).down = 0 at h
  change (∑ i, (@id (R.obj.obj U) ((tupleA M n i).hom.app U x.val).down) •
      (@id (M.val.obj U) ((tupleS M n i).hom.app U x.val).down)) = 0
  dsimp only [tupleSum] at h
  rw [moduleSum_apply] at h
  exact h

private def witnessVariables (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    Unit ⊕ ((Fin n × Fin l) ⊕ Fin l) → Sheaf J (Type (max r m)) :=
  Sum.elim (fun _ ↦ relationObj M n)
    (Sum.elim (fun _ ↦ ringSets R) (fun _ ↦ moduleSets M))

private abbrev witnessTuple (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :=
  ∏ᶜ witnessVariables M n l

private def witnessBase (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    witnessTuple M n l ⟶ relationObj M n := Pi.π (witnessVariables M n l) (.inl ())

private def witnessB (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ)
    (i : Fin n) (j : Fin l) : witnessTuple M n l ⟶ ringSets R :=
  Pi.π (witnessVariables M n l) (.inr (.inl (i, j)))

private def witnessT (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ)
    (j : Fin l) : witnessTuple M n l ⟶ moduleSets M :=
  Pi.π (witnessVariables M n l) (.inr (.inr j))

private def witnessTargets (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    Fin n ⊕ Fin l → Sheaf J (Type (max r m)) :=
  Sum.elim (fun _ ↦ moduleSets M) (fun _ ↦ ringSets R)

private def witnessLeft (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    ∀ i, witnessTuple M n l ⟶ witnessTargets M n l i
  | .inl i => witnessBase M n l ≫ relationS M n i
  | .inr j => ringSum (fun i ↦ ringMul
      (witnessBase M n l ≫ relationA M n i) (witnessB M n l i j))

private def witnessRight (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    ∀ i, witnessTuple M n l ⟶ witnessTargets M n l i
  | .inl i => moduleSum (fun j ↦ moduleSMul (witnessB M n l i j) (witnessT M n l j))
  | .inr _ => ringZero (witnessTuple M n l)

private def witnessObj (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :=
  equationsSheaf (witnessLeft M n l) (witnessRight M n l)

private def witnessι (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    witnessObj M n l ⟶ witnessTuple M n l :=
  equationsι (witnessLeft M n l) (witnessRight M n l)

private def witnessMap (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ) :
    witnessObj M n l ⟶ relationObj M n := witnessι M n l ≫ witnessBase M n l

private theorem witness_factorization (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ)
    (i : Fin n) :
    witnessMap M n l ≫ relationS M n i =
      moduleSum (fun j ↦ moduleSMul (witnessι M n l ≫ witnessB M n l i j)
        (witnessι M n l ≫ witnessT M n l j)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro y
  apply ULift.ext
  have h := congrArg ULift.down (y.property (.inl i))
  change @id (M.val.obj U)
    ((witnessBase M n l ≫ relationS M n i).hom.app U y.val).down =
    @id (M.val.obj U)
      ((moduleSum (fun j ↦ moduleSMul (witnessB M n l i j)
        (witnessT M n l j))).hom.app U y.val).down at h
  rw [moduleSum_apply] at h
  change @id (M.val.obj U)
    ((witnessBase M n l ≫ relationS M n i).hom.app U y.val).down =
    @id (M.val.obj U)
      ((moduleSum (fun j ↦ moduleSMul (witnessι M n l ≫ witnessB M n l i j)
        (witnessι M n l ≫ witnessT M n l j))).hom.app U y).down
  rw [moduleSum_apply]
  exact h

private theorem witness_annihilation (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (n l : ℕ)
    (j : Fin l) :
    ringSum (fun i ↦ ringMul (witnessMap M n l ≫ relationA M n i)
      (witnessι M n l ≫ witnessB M n l i j)) = ringZero (witnessObj M n l) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro y
  apply ULift.ext
  have h := congrArg ULift.down (y.property (.inr j))
  change @id (R.obj.obj U)
    ((ringSum (fun i ↦ ringMul (witnessBase M n l ≫ relationA M n i)
      (witnessB M n l i j))).hom.app U y.val).down = 0 at h
  rw [ringSum_apply] at h
  change @id (R.obj.obj U)
    ((ringSum (fun i ↦ ringMul (witnessMap M n l ≫ relationA M n i)
      (witnessι M n l ≫ witnessB M n l i j))).hom.app U y).down = 0
  rw [ringSum_apply]
  exact h

private theorem witness_local
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify J AddCommGrpCat.{max r m}]
    (M : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hM : IsFlatOnSite M) (n : ℕ) (U : Cᵒᵖ) (x : (relationObj M n).obj.obj U) :
    ∃ S : Sieve U.unop, S ∈ J U.unop ∧
      ∀ (V : C) (f : V ⟶ U.unop), S f →
        ∃ (l : ℕ) (y : (witnessObj M n l).obj.obj (Opposite.op V)),
          (witnessMap M n l).hom.app (Opposite.op V) y =
            (relationObj M n).obj.map f.op x := by
  let a (i : Fin n) : R.obj.obj U := ((relationA M n i).hom.app U x).down
  let s (i : Fin n) : M.val.obj U := ((relationS M n i).hom.app U x).down
  obtain ⟨S, hS, hlocal⟩ := (isFlatOnSite_iff_local_equationalCriterion R M).mp hM
    U.unop n a s (relation_equation M n U x)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, hfac, hzero⟩ := hlocal V f hf
  let vals : ∀ i, (witnessVariables M n l i).obj.obj (Opposite.op V)
    | .inl _ => (relationObj M n).obj.map f.op x
    | .inr (.inl ij) => ULift.up (b ij.1 ij.2)
    | .inr (.inr j) => ULift.up (t j)
  obtain ⟨z, hz⟩ := finite_sections (𝟭 (Sheaf J (Type (max r m))))
    (witnessVariables M n l) (Opposite.op V) vals
  have hzbase : (witnessBase M n l).hom.app (Opposite.op V) z =
      (relationObj M n).obj.map f.op x := hz (.inl ())
  have hzb (i : Fin n) (j : Fin l) :
      @id (R.obj.obj (Opposite.op V)) ((witnessB M n l i j).hom.app
        (Opposite.op V) z).down = b i j :=
    congrArg ULift.down (hz (.inr (.inl (i, j))))
  have hzt (j : Fin l) :
      @id (M.val.obj (Opposite.op V)) ((witnessT M n l j).hom.app
        (Opposite.op V) z).down = t j :=
    congrArg ULift.down (hz (.inr (.inr j)))
  have hA (i : Fin n) : @id (R.obj.obj (Opposite.op V))
      ((witnessBase M n l ≫ relationA M n i).hom.app (Opposite.op V) z).down =
        R.obj.map f.op (a i) := by
    change ((relationA M n i).hom.app _ ((witnessBase M n l).hom.app _ z)).down = _
    rw [hzbase]
    exact congrArg ULift.down ((relationA M n i).hom.naturality_apply f.op x)
  have hS' (i : Fin n) : @id (M.val.obj (Opposite.op V))
      ((witnessBase M n l ≫ relationS M n i).hom.app (Opposite.op V) z).down =
        M.val.map f.op (s i) := by
    change ((relationS M n i).hom.app _ ((witnessBase M n l).hom.app _ z)).down = _
    rw [hzbase]
    exact congrArg ULift.down ((relationS M n i).hom.naturality_apply f.op x)
  have heq : ∀ i, (witnessLeft M n l i).hom.app (Opposite.op V) z =
      (witnessRight M n l i).hom.app (Opposite.op V) z := by
    intro i
    cases i with
    | inl i =>
      apply ULift.ext
      change @id (M.val.obj (Opposite.op V))
        ((witnessBase M n l ≫ relationS M n i).hom.app (Opposite.op V) z).down =
        @id (M.val.obj (Opposite.op V))
          ((moduleSum (fun j ↦ moduleSMul (witnessB M n l i j)
            (witnessT M n l j))).hom.app (Opposite.op V) z).down
      rw [moduleSum_apply, hS', hfac]
      apply Finset.sum_congr rfl
      intro j _
      change b i j • t j =
        (@id (R.obj.obj (Opposite.op V))
          ((witnessB M n l i j).hom.app (Opposite.op V) z).down) •
        (@id (M.val.obj (Opposite.op V))
          ((witnessT M n l j).hom.app (Opposite.op V) z).down)
      rw [hzb, hzt]
    | inr j =>
      apply ULift.ext
      change @id (R.obj.obj (Opposite.op V))
        ((ringSum (fun i ↦ ringMul (witnessBase M n l ≫ relationA M n i)
          (witnessB M n l i j))).hom.app (Opposite.op V) z).down = 0
      rw [ringSum_apply]
      calc
        _ = ∑ i, R.obj.map f.op (a i) * b i j := by
          apply Finset.sum_congr rfl
          intro i _
          change (@id (R.obj.obj (Opposite.op V))
            ((witnessBase M n l ≫ relationA M n i).hom.app (Opposite.op V) z).down) *
            (@id (R.obj.obj (Opposite.op V))
              ((witnessB M n l i j).hom.app (Opposite.op V) z).down) = _
          rw [hA, hzb]
        _ = 0 := hzero j
  exact ⟨l, ⟨z, heq⟩, hzbase⟩

end Operations

section ImageOperations

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  {R : Sheaf J CommRingCat.{r}} {RI : Sheaf K CommRingCat.{r}}
  {L : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m))}
  (I : AlgebraicInverseImageOfUniverses L R RI)
  {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
  {T : Sheaf J (Type (max r m))}

private abbrev imageR (a : T ⟶ ringSets R) : L.obj T ⟶ ringSets RI :=
  L.map a ≫ I.ringUnderlying.hom

private abbrev imageM (a : T ⟶ moduleSets M) : L.obj T ⟶ moduleSets (I.modules.obj M) :=
  L.map a ≫ I.moduleUnderlying.inv.app M

private theorem imageM_zero (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id ((I.modules.obj M).val.obj U)
      ((imageM I (moduleZero M T)).hom.app U x).down = 0 := by
  exact I.moduleZero M T (moduleZero M T) (fun _ _ ↦ rfl) U x

private theorem imageR_zero (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id (RI.obj.obj U) ((imageR I (ringZero T)).hom.app U x).down = 0 := by
  exact I.ringZero T (ringZero T) (fun _ _ ↦ rfl) U x

private theorem imageM_sum {n : ℕ} (a : Fin n → (T ⟶ moduleSets M))
    (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id ((I.modules.obj M).val.obj U) ((imageM I (moduleSum a)).hom.app U x).down =
      ∑ i, @id ((I.modules.obj M).val.obj U) ((imageM I (a i)).hom.app U x).down := by
  induction n with
  | zero =>
    simpa only [moduleSum, Finset.univ_eq_empty, Finset.sum_empty] using imageM_zero I U x
  | succ n ih =>
    change @id ((I.modules.obj M).val.obj U)
      ((imageM I (moduleAdd (a 0) (moduleSum (fun i ↦ a i.succ)))).hom.app U x).down = _
    have h := I.moduleAdd M T (a 0) (moduleSum (fun i ↦ a i.succ))
      (moduleAdd (a 0) (moduleSum (fun i ↦ a i.succ))) (fun _ _ ↦ rfl) U x
    change @id ((I.modules.obj M).val.obj U)
      ((imageM I (moduleAdd (a 0) (moduleSum (fun i ↦ a i.succ)))).hom.app U x).down =
      @id ((I.modules.obj M).val.obj U) ((imageM I (a 0)).hom.app U x).down +
        @id ((I.modules.obj M).val.obj U)
          ((imageM I (moduleSum (fun i ↦ a i.succ))).hom.app U x).down at h
    rw [h, ih, Fin.sum_univ_succ]

private theorem imageR_sum {n : ℕ} (a : Fin n → (T ⟶ ringSets R))
    (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id (RI.obj.obj U) ((imageR I (ringSum a)).hom.app U x).down =
      ∑ i, @id (RI.obj.obj U) ((imageR I (a i)).hom.app U x).down := by
  induction n with
  | zero =>
    simpa only [ringSum, Finset.univ_eq_empty, Finset.sum_empty] using imageR_zero I U x
  | succ n ih =>
    change @id (RI.obj.obj U)
      ((imageR I (ringAdd (a 0) (ringSum (fun i ↦ a i.succ)))).hom.app U x).down = _
    have h := I.ringAdd T (a 0) (ringSum (fun i ↦ a i.succ))
      (ringAdd (a 0) (ringSum (fun i ↦ a i.succ))) (fun _ _ ↦ rfl) U x
    change @id (RI.obj.obj U)
      ((imageR I (ringAdd (a 0) (ringSum (fun i ↦ a i.succ)))).hom.app U x).down =
      @id (RI.obj.obj U) ((imageR I (a 0)).hom.app U x).down +
        @id (RI.obj.obj U) ((imageR I (ringSum (fun i ↦ a i.succ))).hom.app U x).down at h
    rw [h, ih, Fin.sum_univ_succ]

private theorem imageM_sum_smul {n : ℕ}
    (a : Fin n → (T ⟶ ringSets R)) (s : Fin n → (T ⟶ moduleSets M))
    (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id ((I.modules.obj M).val.obj U)
      ((imageM I (moduleSum (fun i ↦ moduleSMul (a i) (s i)))).hom.app U x).down =
      ∑ i, (@id (RI.obj.obj U) ((imageR I (a i)).hom.app U x).down) •
        (@id ((I.modules.obj M).val.obj U) ((imageM I (s i)).hom.app U x).down) := by
  rw [imageM_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact I.moduleSMul M T (a i) (s i) (moduleSMul (a i) (s i)) (fun _ _ ↦ rfl) U x

private theorem imageR_sum_mul {n : ℕ}
    (a b : Fin n → (T ⟶ ringSets R)) (U : Dᵒᵖ) (x : (L.obj T).obj.obj U) :
    @id (RI.obj.obj U)
      ((imageR I (ringSum (fun i ↦ ringMul (a i) (b i)))).hom.app U x).down =
      ∑ i, (@id (RI.obj.obj U) ((imageR I (a i)).hom.app U x).down) *
        (@id (RI.obj.obj U) ((imageR I (b i)).hom.app U x).down) := by
  rw [imageR_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact I.ringMul T (a i) (b i) (ringMul (a i) (b i)) (fun _ _ ↦ rfl) U x

private theorem relation_lift [PreservesFiniteLimits L] (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (n : ℕ) (U : Dᵒᵖ) (a : Fin n → RI.obj.obj U)
    (s : Fin n → (I.modules.obj M).val.obj U) (h : (∑ i, a i • s i) = 0) :
    ∃ x : (L.obj (relationObj M n)).obj.obj U,
      (∀ i, @id (RI.obj.obj U) ((imageR I (relationA M n i)).hom.app U x).down = a i) ∧
      (∀ i, @id ((I.modules.obj M).val.obj U)
        ((imageM I (relationS M n i)).hom.app U x).down = s i) := by
  let vals : ∀ i, (L.obj (relationVariables M n i)).obj.obj U
    | .inl i => I.ringUnderlying.inv.hom.app U (ULift.up (a i))
    | .inr i => (I.moduleUnderlying.hom.app M).hom.app U (ULift.up (s i))
  obtain ⟨z, hz⟩ := finite_sections L (relationVariables M n) U vals
  have ha (i : Fin n) : @id (RI.obj.obj U)
      ((imageR I (tupleA M n i)).hom.app U z).down = a i := by
    change (I.ringUnderlying.hom.hom.app U
      ((L.map (Pi.π (relationVariables M n) (.inl i))).hom.app U z)).down = a i
    rw [hz]
    exact congrArg ULift.down (congrArg
      (fun k : ringSets RI ⟶ ringSets RI ↦ k.hom.app U (ULift.up (a i)))
      I.ringUnderlying.inv_hom_id)
  have hs (i : Fin n) : @id ((I.modules.obj M).val.obj U)
      ((imageM I (tupleS M n i)).hom.app U z).down = s i := by
    change ((I.moduleUnderlying.inv.app M).hom.app U
      ((L.map (Pi.π (relationVariables M n) (.inr i))).hom.app U z)).down = s i
    rw [hz]
    exact congrArg ULift.down (congrArg
      (fun k : moduleSets (I.modules.obj M) ⟶ moduleSets (I.modules.obj M) ↦
        k.hom.app U (ULift.up (s i))) (I.moduleUnderlying.app M).hom_inv_id)
  have hsum : @id ((I.modules.obj M).val.obj U)
      ((imageM I (tupleSum M n)).hom.app U z).down = 0 := by
    rw [tupleSum, imageM_sum_smul]
    simpa only [ha, hs] using h
  have hzrel : (L.map (tupleSum M n)).hom.app U z =
      (L.map (moduleZero M (relationTuple M n))).hom.app U z := by
    apply (CategoryTheory.mono_iff_injective
      ((I.moduleUnderlying.inv.app M).hom.app U)).mp inferInstance
    apply ULift.ext
    exact hsum.trans (imageM_zero I U z).symm
  obtain ⟨x, hx⟩ := equation_sections L (tupleSum M n)
    (moduleZero M (relationTuple M n)) U z hzrel
  refine ⟨x, ?_, ?_⟩
  · intro i
    change (I.ringUnderlying.hom.hom.app U
      ((L.map (relationι M n ≫ tupleA M n i)).hom.app U x)).down = a i
    rw [L.map_comp]
    change (I.ringUnderlying.hom.hom.app U
      ((L.map (tupleA M n i)).hom.app U ((L.map (relationι M n)).hom.app U x))).down = _
    exact (congrArg (fun z ↦
      (I.ringUnderlying.hom.hom.app U
        ((L.map (tupleA M n i)).hom.app U z)).down) hx).trans (ha i)
  · intro i
    change ((I.moduleUnderlying.inv.app M).hom.app U
      ((L.map (relationι M n ≫ tupleS M n i)).hom.app U x)).down = s i
    rw [L.map_comp]
    change ((I.moduleUnderlying.inv.app M).hom.app U
      ((L.map (tupleS M n i)).hom.app U ((L.map (relationι M n)).hom.app U x))).down = _
    exact (congrArg (fun z ↦
      ((I.moduleUnderlying.inv.app M).hom.app U
        ((L.map (tupleS M n i)).hom.app U z)).down) hx).trans (hs i)

private theorem image_witness_factorization (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (n l : ℕ) (i : Fin n) (U : Dᵒᵖ) (y : (L.obj (witnessObj M n l)).obj.obj U) :
    @id ((I.modules.obj M).val.obj U)
      ((imageM I (witnessMap M n l ≫ relationS M n i)).hom.app U y).down =
    ∑ j, (@id (RI.obj.obj U)
      ((imageR I (witnessι M n l ≫ witnessB M n l i j)).hom.app U y).down) •
      (@id ((I.modules.obj M).val.obj U)
        ((imageM I (witnessι M n l ≫ witnessT M n l j)).hom.app U y).down) := by
  rw [witness_factorization]
  exact imageM_sum_smul I _ _ U y

private theorem image_witness_annihilation (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (n l : ℕ) (j : Fin l) (U : Dᵒᵖ) (y : (L.obj (witnessObj M n l)).obj.obj U) :
    (∑ i, (@id (RI.obj.obj U)
      ((imageR I (witnessMap M n l ≫ relationA M n i)).hom.app U y).down) *
      (@id (RI.obj.obj U)
        ((imageR I (witnessι M n l ≫ witnessB M n l i j)).hom.app U y).down)) = 0 := by
  rw [← imageR_sum_mul, witness_annihilation]
  exact imageR_zero I U y

end ImageOperations

/-- Inverse image transports a flat module to a flat module over the inverse-image ring.
Source: Stacks Project, Modules on Sites, Tags 05VD and 08FC
(auxiliary; not a blueprint node).

Proof: For each finite length n, form the sheaf of tuples (a_i, s_i) satisfying
Σ a_i • s_i = 0, as an equalizer inside the product of n copies of the underlying
ring sheaf and n copies of the underlying module sheaf. For each matrix width l,
form the sheaf of witnesses (a, s, b, t) satisfying s_i = Σ b_ij • t_j and
Σ a_i * b_ij = 0. The source local equational criterion says that the projections
from these witness sheaves, indexed by l, are jointly locally surjective.

A left adjoint between sheaf categories preserves such families. Indeed, the
subsheaf locally generated by their mapped images is mono in the target. By
adjunction its direct image receives the original family, and local surjectivity
lifts the adjunction unit against that mono. Adjunction gives a retraction of the
target inclusion, so the mapped family remains jointly locally surjective.

Finite-limit preservation lifts every target tuple satisfying its relation to
the inverse image of the source relation sheaf. The graph equations of I identify
the transported finite sums, zeros, products and scalar multiplications with the
target operations. The mapped locally surjective witness family therefore gives
a covering on which the target tuple has the required finite matrix factorization.
Naturality identifies its coefficients and sections with the restrictions of the
original tuple. Apply the reverse local equational criterion on the target site.
The finite products, equalizers, and sums used here include the empty cases. -/
theorem isFlat_algebraicInverseImageOfUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify K AddCommGrpCat.{max r m}]
    {R : Sheaf J CommRingCat.{r}} {RI : Sheaf K CommRingCat.{r}}
    (uInv : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m)))
    (uPush : Sheaf K (Type (max r m)) ⥤ Sheaf J (Type (max r m)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImageOfUniverses uInv R RI)
    (F : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hF : IsFlatOnSite F) : IsFlatOnSite (I.modules.obj F) := by
  apply (isFlatOnSite_iff_local_equationalCriterion RI (I.modules.obj F)).mpr
  intro U n a s h
  obtain ⟨x, ha, hs⟩ := relation_lift I F n (Opposite.op U) a s h
  obtain ⟨S, hS, hlocal⟩ := CategoryTheory.Sheaf.map_jointly_locally_surjective
    uInv uPush adj (fun l ↦ witnessMap F n l)
    (fun V y ↦ witness_local F hF n V y) (Opposite.op U) x
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, y, hy⟩ := hlocal V f hf
  let b (i : Fin n) (j : Fin l) : RI.obj.obj (Opposite.op V) :=
    ((imageR I (witnessι F n l ≫ witnessB F n l i j)).hom.app (Opposite.op V) y).down
  let t (j : Fin l) : (I.modules.obj F).val.obj (Opposite.op V) :=
    ((imageM I (witnessι F n l ≫ witnessT F n l j)).hom.app (Opposite.op V) y).down
  have hA (i : Fin n) : @id (RI.obj.obj (Opposite.op V))
      ((imageR I (witnessMap F n l ≫ relationA F n i)).hom.app (Opposite.op V) y).down =
        RI.obj.map f.op (a i) := by
    change (I.ringUnderlying.hom.hom.app _
      ((uInv.map (witnessMap F n l ≫ relationA F n i)).hom.app _ y)).down = _
    rw [uInv.map_comp]
    change ((imageR I (relationA F n i)).hom.app (Opposite.op V)
      ((uInv.map (witnessMap F n l)).hom.app (Opposite.op V) y)).down = _
    rw [hy]
    have hn : @id (RI.obj.obj (Opposite.op V))
        ((imageR I (relationA F n i)).hom.app (Opposite.op V)
          ((uInv.obj (relationObj F n)).obj.map f.op x)).down =
        RI.obj.map f.op (@id (RI.obj.obj (Opposite.op U))
          ((imageR I (relationA F n i)).hom.app (Opposite.op U) x).down) :=
      congrArg ULift.down ((imageR I (relationA F n i)).hom.naturality_apply f.op x)
    exact hn.trans (congrArg (fun z : RI.obj.obj (Opposite.op U) ↦
      RI.obj.map f.op z) (ha i))
  have hS' (i : Fin n) : @id ((I.modules.obj F).val.obj (Opposite.op V))
      ((imageM I (witnessMap F n l ≫ relationS F n i)).hom.app (Opposite.op V) y).down =
        (I.modules.obj F).val.map f.op (s i) := by
    change ((I.moduleUnderlying.inv.app F).hom.app _
      ((uInv.map (witnessMap F n l ≫ relationS F n i)).hom.app _ y)).down = _
    rw [uInv.map_comp]
    change ((imageM I (relationS F n i)).hom.app (Opposite.op V)
      ((uInv.map (witnessMap F n l)).hom.app (Opposite.op V) y)).down = _
    rw [hy]
    have hn : @id ((I.modules.obj F).val.obj (Opposite.op V))
        ((imageM I (relationS F n i)).hom.app (Opposite.op V)
          ((uInv.obj (relationObj F n)).obj.map f.op x)).down =
        (I.modules.obj F).val.map f.op
          (@id ((I.modules.obj F).val.obj (Opposite.op U))
            ((imageM I (relationS F n i)).hom.app (Opposite.op U) x).down) :=
      congrArg ULift.down ((imageM I (relationS F n i)).hom.naturality_apply f.op x)
    exact hn.trans (congrArg
      (fun z : (I.modules.obj F).val.obj (Opposite.op U) ↦
        (I.modules.obj F).val.map f.op z) (hs i))
  refine ⟨l, b, t, ?_, ?_⟩
  · intro i
    exact (hS' i).symm.trans (image_witness_factorization I F n l i (Opposite.op V) y)
  · intro j
    have hz := image_witness_annihilation I F n l j (Opposite.op V) y
    simp only [hA] at hz
    dsimp only [id] at hz
    exact hz


end

end SheafOfModules
