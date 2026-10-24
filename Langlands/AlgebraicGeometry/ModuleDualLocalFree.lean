import Langlands.AlgebraicGeometry.ModuleDual
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens} {I : Type u}

local instance : DecidableEq I := Classical.decEq I

/-- A coordinate projection of the free sheaf on an open. -/
def freeCoordinate (U : X.Opens) (I : Type u) (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) := by
  classical
  exact Sigma.desc (fun j => if j = i then 𝟙 _ else 0)

@[reassoc (attr := simp)]
lemma ιFree_freeCoordinate (i j : I) :
    SheafOfModules.ιFree j ≫ freeCoordinate (X := X) U I i =
      if j = i then 𝟙 _ else 0 := by
  classical
  simp [freeCoordinate, SheafOfModules.ιFree]

lemma freeCoordinate_total [Fintype I] :
    ∑ i : I, freeCoordinate (X := X) U I i ≫ SheafOfModules.ιFree i =
      𝟙 (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  classical
  apply (SheafOfModules.isColimitFreeCofan I).hom_ext
  rintro ⟨j⟩
  change SheafOfModules.ιFree j ≫ _ = SheafOfModules.ιFree j ≫ _
  simp [Preadditive.comp_sum, ← Category.assoc, ite_comp]

variable {M : X.Modules}

/-- The coordinate local functional of a trivialization. -/
def localBasisCoordinate
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) (i : I) :
    LocalHom M (Langlands.SchemeModule.structureModule X) U :=
  e.inv ≫ freeCoordinate U I i

/-- The basis sections of a local trivialization, as a compatible family. -/
def localBasisSection
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) (i : I) :
    (M.over U).sections :=
  (M.over U).freeHomEquiv e.hom i

/-- Restrictions of a local functional form a section over the over-category. -/
def localDualSection (f : LocalHom M (Langlands.SchemeModule.structureModule X) U) :
    ((dual M).over U).sections :=
  PresheafOfModules.sectionsMk (fun V => LocalHom.restrict V.unop.hom f) (by
    intro V W j
    change LocalHom.restrict j.unop.left (LocalHom.restrict V.unop.hom f) =
      LocalHom.restrict W.unop.hom f
    rw [LocalHom.restrict_comp]
    rfl)

/-- The map sending the free generators to the coordinate local functionals. -/
def dualLocalFreeHom
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ (dual M).over U :=
  ((dual M).over U).freeHomEquiv.symm (fun i => localDualSection (localBasisCoordinate e i))

/-- Evaluation on a fixed compatible local section is a sheaf morphism. -/
def localDualEvaluation (s : (M.over U).sections) :
    (dual M).over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) where
  val :=
    { app := fun V => ModuleCat.ofHom
        { toFun := fun f => dualEval M V.unop.left f (s.val V)
          map_add' := by intros; rfl
          map_smul' := by intros; simp }
      naturality := by
        intro V W j
        ext f
        change dualEval M W.unop.left (LocalHom.restrict j.unop.left f) (s.val W) =
          X.presheaf.map j.unop.left.op (dualEval M V.unop.left f (s.val V))
        rw [← PresheafOfModules.sections_property s j]
        exact internalHomEval_restrict M _ j.unop.left f (s.val V) }

@[simp]
lemma dualLocalFreeHom_basis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (i : I) (V : Over U) :
    (dualLocalFreeHom e).val.app (op V) ((SheafOfModules.freeSection i).val (op V)) =
      LocalHom.restrict V.hom (localBasisCoordinate e i) := by
  exact congrArg (fun s => s.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => localDualSection (localBasisCoordinate e i)) i)

@[simp]
lemma localBasisCoordinate_basis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (i j : I) (V : Over U) :
    (show Γ(X, V.left) from
      LocalHom.app (localBasisCoordinate e i) V.hom ((localBasisSection e j).val (op V))) =
      if j = i then 1 else 0 := by
  have h : SheafOfModules.ιFree j ≫ e.hom ≫ e.inv ≫ freeCoordinate U I i =
      if j = i then 𝟙 _ else 0 := by simp
  have hh := congrArg (fun f => f.val.app (op V) (1 : Γ(X, V.left))) h
  by_cases hji : j = i
  · rw [ite_eq_left hji] at hh ⊢
    exact hh
  · rw [ite_eq_right hji] at hh ⊢
    exact hh

private lemma sum_app {A B : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    {J : Type u} (s : Finset J) (f : J → (A ⟶ B)) (V : (Over U)ᵒᵖ) (x : A.val.obj V) :
    (∑ j ∈ s, f j).val.app V x = ∑ j ∈ s, (f j).val.app V x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    change (f j).val.app V x + (∑ j ∈ s, f j).val.app V x = _
    rw [ih]

lemma localBasis_expansion [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) (x : Γ(M, V.left)) :
    ∑ i : I, (show Γ(X, V.left) from LocalHom.app (localBasisCoordinate e i) V.hom x) •
      (show Γ(M, V.left) from (localBasisSection e i).val (op V)) = x := by
  have h : ∑ i : I, (e.inv ≫ freeCoordinate U I i) ≫
      (SheafOfModules.ιFree i ≫ e.hom) = 𝟙 (M.over U) := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, freeCoordinate_total]
    simp
  have hh := congrArg (fun f => f.val.app (op V) x) h
  rw [sum_app] at hh
  change (∑ i : I, ((e.inv ≫ freeCoordinate U I i) ≫
      (SheafOfModules.ιFree i ≫ e.hom)).val.app (op V) x) = x at hh
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro i hi
  change _ = (SheafOfModules.ιFree i ≫ e.hom).val.app (op V)
    (LocalHom.app (localBasisCoordinate e i) V.hom x)
  have hs := ((SheafOfModules.ιFree i ≫ e.hom).val.app (op V)).hom.map_smul
      (show Γ(X, V.left) from LocalHom.app (localBasisCoordinate e i) V.hom x)
      (1 : Γ(X, V.left))
  rw [smul_eq_mul, mul_one] at hs
  exact hs.symm

lemma dualLocalFreeHom_evaluation
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) (i : I) :
    dualLocalFreeHom e ≫ localDualEvaluation (localBasisSection e i) =
      freeCoordinate U I i := by
  apply ((SheafOfModules.unit (X.ringCatSheaf.over U)).freeHomEquiv).injective
  funext j
  apply PresheafOfModules.sections_ext
  intro V
  change dualEval M V.unop.left
      ((dualLocalFreeHom e).val.app V ((SheafOfModules.freeSection j).val V))
      ((localBasisSection e i).val V) =
    (freeCoordinate U I i).val.app V ((SheafOfModules.freeSection j).val V)
  rw [dualLocalFreeHom_basis]
  change LocalHom.app (localBasisCoordinate e j) V.unop.hom
      ((localBasisSection e i).val V) = _
  refine (localBasisCoordinate_basis e j i V.unop).trans ?_
  have h := congrArg (fun f => f.val.app V (1 : Γ(X, V.unop.left)))
    (ιFree_freeCoordinate (X := X) (U := U) i j)
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl] at h ⊢
    exact h.symm
  · rw [ite_eq_right hij]
    rw [ite_eq_right (Ne.symm hij)] at h
    exact h.symm

/-- Evaluations on a finite local basis distinguish sheaf maps into the dual. -/
lemma localDualEvaluation_hom_ext [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {A : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (f g : A ⟶ (dual M).over U)
    (h : ∀ i, f ≫ localDualEvaluation (localBasisSection e i) =
      g ≫ localDualEvaluation (localBasisSection e i)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext a
  apply LocalHom.ext
  intro W j
  ext x
  let W' : Over U := Over.mk (j ≫ V.unop.hom)
  let k : W' ⟶ V.unop := Over.homMk j
  have hb (i : I) :
      LocalHom.app (f.val.app V a) j ((localBasisSection e i).val (op W')) =
      LocalHom.app (g.val.app V a) j ((localBasisSection e i).val (op W')) := by
    have hi := congrArg (fun p => p.val.app (op W') (A.val.map k.op a)) (h i)
    change dualEval M W ((f.val.app (op W')) (A.val.map k.op a)) _ =
      dualEval M W ((g.val.app (op W')) (A.val.map k.op a)) _ at hi
    rw [PresheafOfModules.naturality_apply f.val k.op a,
      PresheafOfModules.naturality_apply g.val k.op a] at hi
    exact hi
  rw [← localBasis_expansion e W' x]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => _ • z) (hb i))

/-- The inverse coordinate map, obtained by evaluating all basis vectors. -/
def dualLocalFreeInv [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    (dual M).over U ⟶ SheafOfModules.free (R := X.ringCatSheaf.over U) I :=
  ∑ i, localDualEvaluation (localBasisSection e i) ≫ SheafOfModules.ιFree i

lemma dualLocalFreeHom_inv [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    dualLocalFreeHom e ≫ dualLocalFreeInv e = 𝟙 _ := by
  simp only [dualLocalFreeInv, Preadditive.comp_sum, ← Category.assoc,
    dualLocalFreeHom_evaluation]
  exact freeCoordinate_total

lemma dualLocalFreeInv_hom [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    dualLocalFreeInv e ≫ dualLocalFreeHom e = 𝟙 _ := by
  apply localDualEvaluation_hom_ext e
  intro i
  simp only [Category.assoc, dualLocalFreeHom_evaluation, Category.id_comp,
    dualLocalFreeInv, Preadditive.sum_comp, ιFree_freeCoordinate]
  simp [comp_ite]

/-- Finite coordinate duality for the actual internal dual, with the same index type. -/
def dualLocalFreeIso [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ (dual M).over U := by
  letI := Fintype.ofFinite I
  exact { hom := dualLocalFreeHom e
          inv := dualLocalFreeInv e
          hom_inv_id := dualLocalFreeHom_inv e
          inv_hom_id := dualLocalFreeInv_hom e }

@[simp]
lemma dualLocalFreeIso_hom [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    (dualLocalFreeIso e).hom = dualLocalFreeHom e := rfl

/-- Each generator of the dual basis is the restricted coordinate local functional. -/
@[simp]
lemma dualLocalFreeIso_basis [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (i : I) (V : Over U) :
    (dualLocalFreeIso e).hom.val.app (op V) ((SheafOfModules.freeSection i).val (op V)) =
      LocalHom.restrict V.hom (localBasisCoordinate e i) :=
  dualLocalFreeHom_basis e i V

/-- The coordinate dual basis evaluates to the Kronecker delta on every smaller open. -/
lemma dualLocalFreeIso_eval [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : X.Opens) (h : V ⟶ U) (i j : I) :
    dualEval M V
      ((dualLocalFreeIso e).hom.val.app (op (Over.mk h))
        ((SheafOfModules.freeSection i).val (op (Over.mk h))))
      ((localBasisSection e j).val (op (Over.mk h))) =
        if j = i then 1 else 0 := by
  rw [dualLocalFreeIso_basis]
  exact localBasisCoordinate_basis e i j (Over.mk h)

end Langlands.Scheme.Modules
