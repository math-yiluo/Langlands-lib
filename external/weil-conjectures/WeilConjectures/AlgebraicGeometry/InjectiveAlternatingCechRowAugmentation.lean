/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The increasing-tuple augmented Čech row of an injective module

Source: Stacks Project, Tags 01EP and 01FM, as used in Tag 08C1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry


private theorem alternatingRow_d_apply {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens)
    (G : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (p : ℕ)
    (s : alternatingCechTerms U G p) (t : Fin (p + 2) ↪o Fin r) :
    (alternatingCechDifferential U G p).hom s t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom
          (s ((Fin.succAboveOrderEmb j).trans t)) := by
  change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection U q))) at s
  change ((∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
      (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))) s) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

private def intersectionCech {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W := fun p t ↦ ⨅ k : Fin (p + 1), U (t k)
  pr := fun _ t k ↦ homOfLE (iInf_le (fun k ↦ U (t k)) k)
  comm := fun _ _ _ ↦ Subsingleton.elim _ _
  universal := by
    intro p t Z a _
    refine ⟨homOfLE (le_iInf fun k ↦ leOfHom (a k)), ?_, ?_⟩
    · intro k; exact Subsingleton.elim _ _
    · intro b _; exact Subsingleton.elim _ _
  W_zero := by intro t; simp
  pr_zero := fun _ ↦ Subsingleton.elim _ _
  indexMap := fun t α ↦ homOfLE
    (le_iInf fun k ↦ iInf_le (fun k ↦ U (t k)) (α k))
  indexMap_pr := fun _ _ _ ↦ Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingRow_positive {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M]
    (p : ℕ) (hp : 0 < p) :
    (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj M)).ExactAt p := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  let F := P ⋙ forget₂ _ AddCommGrpCat
  let S := intersectionCech U
  let A := ((forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (alternatingCechComplex U P)
  let e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t}, F.obj (op (S.W p t.1))) :=
    fun p ↦
      { hom := AddCommGrpCat.ofHom
          { toFun := fun s t ↦ s (OrderEmbedding.ofStrictMono t.1 t.2)
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        inv := AddCommGrpCat.ofHom
          { toFun := fun s t ↦ s ⟨t, t.strictMono⟩
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        hom_inv_id := by apply AddCommGrpCat.ext; intro s; funext t; rfl
        inv_hom_id := by apply AddCommGrpCat.ext; intro s; funext t; rfl }
  let q : S.complex F ⟶ A := CochainComplex.ofHom
    (fun p ↦ AddCommGrpCat.ofHom
      { toFun := fun s t ↦ s t
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }) (by
      intro p
      apply AddCommGrpCat.ext
      intro s
      funext t
      simp only [SiteCechComplex.complex, A, alternatingCechComplex,
        Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
      change (alternatingCechDifferential U P p).hom
        (fun t : Fin (p + 1) ↪o Fin r ↦ s t) t = (S.differentialValue F p s) t
      rw [alternatingRow_d_apply]
      rfl)
  have hq : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → Fin r // StrictMono t}),
      (e p).hom ((q.f p) s) t = s t.1 := by intros; rfl
  obtain ⟨i, ⟨hqi⟩, ⟨hiq⟩⟩ :=
    Scheme.alternatingCechRestrictionHomotopy X U F S A e q hq
  let E : HomotopyEquiv (S.complex F) A := ⟨q, i, hqi, hiq⟩
  have hz : IsZero ((S.complex F).homology p) :=
    Scheme.Modules.module_injective_open_cover_cech_acyclic M ⊤ (Fin r) U
      (fun _ ↦ le_top) hU S p hp
  have hz' : IsZero (A.homology p) := hz.of_iso (E.toHomologyIso p).symm
  have he : A.ExactAt p := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hz'
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel (p - 1) p from by change p - 1 + 1 = p; omega)) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel (p - 1) p from by change p - 1 + 1 = p; omega)) (by simp),
    ShortComplex.ab_exact_iff] at he
  exact he

private def singletonTuple {r : ℕ} (i : Fin r) : Fin 1 ↪o Fin r :=
  OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    have : a = b := Subsingleton.elim _ _
    subst b
    exact False.elim (lt_irrefl _ hab))

private theorem singletonIntersection {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (i : Fin r) :
    alternatingCechIntersection U (singletonTuple i) = U i := by
  simp [alternatingCechIntersection, singletonTuple]

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingRow_zero_d {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens)
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :
    alternatingCechPresheafZero U P ≫ (alternatingCechComplex U P).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  change (alternatingCechDifferential U P 0).hom
    ((alternatingCechPresheafZero U P).hom s) t = 0
  rw [alternatingRow_d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  change (P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 0)).op).hom
    ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
      ((Fin.succAboveOrderEmb 0).trans t)))).op).hom s) +
    -(P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 1)).op).hom
      ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
        ((Fin.succAboveOrderEmb 1).trans t)))).op).hom s) = 0
  rw [add_neg_eq_zero]
  change ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
      ((Fin.succAboveOrderEmb 0).trans t)))).op ≫
    P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 0)).op).hom s) =
      ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
        ((Fin.succAboveOrderEmb 1).trans t)))).op ≫
      P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 1)).op).hom s)
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 3

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingRow_glue {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (c : alternatingCechTerms U ((alternatingCechModulePresheaf (X := X)).obj M) 0)
    (hc : (alternatingCechDifferential U
      ((alternatingCechModulePresheaf (X := X)).obj M) 0).hom c = 0) :
    ∃ s : ((alternatingCechModulePresheaf (X := X)).obj M).obj (op ⊤),
      (alternatingCechPresheafZero U
        ((alternatingCechModulePresheaf (X := X)).obj M)).hom s = c := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  let sf (i : Fin r) : P.obj (op (U i)) :=
    P.map (homOfLE (le_of_eq (singletonIntersection U i).symm)).op (c (singletonTuple i))
  let F := (SheafOfModules.forgetToSheafModuleCat (moduleRings X.toRingedSpace)
    (op ⊤) isTerminalTop.op).obj M
  let G : TopCat.Sheaf
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) X.toTopCat :=
    ⟨F.obj, F.property⟩
  have hlt (i j : Fin r) (hij : i < j) :
      P.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i) =
        P.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j) := by
    let t : Fin 2 ↪o Fin r := OrderEmbedding.ofStrictMono
      (Fin.cases i (fun _ ↦ j)) (by
        intro a b hab
        fin_cases a <;> fin_cases b
        · exact False.elim (lt_irrefl _ hab)
        · exact hij
        · simp at hab
        · exact False.elim (lt_irrefl _ hab))
    have ht : U i ⊓ U j ≤ alternatingCechIntersection U t := by
      apply le_iInf
      intro k
      fin_cases k
      · exact inf_le_left
      · exact inf_le_right
    have h0 : (Fin.succAboveOrderEmb (0 : Fin 2)).trans t = singletonTuple j := by
      ext k
      fin_cases k
      rfl
    have h1 : (Fin.succAboveOrderEmb (1 : Fin 2)).trans t = singletonTuple i := by
      ext k
      fin_cases k
      rfl
    have hct : (alternatingCechDifferential U P 0).hom c t = 0 := congrFun hc t
    have hh := congrArg (fun z ↦ P.map (homOfLE ht).op z) hct
    rw [alternatingRow_d_apply, Fin.sum_univ_two] at hh
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, map_add, map_neg, map_zero] at hh
    have transport (a b : Fin 1 ↪o Fin r)
        (ha : U i ⊓ U j ≤ alternatingCechIntersection U a)
        (hb : U i ⊓ U j ≤ alternatingCechIntersection U b) (hab : a = b) :
        P.map (homOfLE ha).op (c a) = P.map (homOfLE hb).op (c b) := by
      subst b
      rfl
    have face0 : P.map (homOfLE ht).op
        (P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 0)).op
          (c ((Fin.succAboveOrderEmb 0).trans t))) =
        P.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j) := by
      dsimp only [sf]
      rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
      exact transport _ _ _ _ h0
    have face1 : P.map (homOfLE ht).op
        (P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 1)).op
          (c ((Fin.succAboveOrderEmb 1).trans t))) =
        P.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i) := by
      dsimp only [sf]
      rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
      exact transport _ _ _ _ h1
    rw [face0, face1] at hh
    exact (add_neg_eq_zero.mp hh).symm
  have hcompat : TopCat.Presheaf.IsCompatible G.obj U sf := by
    intro i j
    change P.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i) =
      P.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j)
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hlt i j hij
    · rfl
    · have hh := hlt j i hji
      have hh' := congrArg (fun z ↦
        P.map (eqToHom (inf_comm (U i) (U j))).op z) hh.symm
      simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp] at hh'
      exact hh'
  obtain ⟨s, hs, _⟩ := G.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (by rw [hU]) sf hcompat
  refine ⟨s, ?_⟩
  funext t
  have ht : t = singletonTuple (t 0) := by
    ext k
    fin_cases k
    rfl
  obtain ⟨i, rfl⟩ : ∃ i, t = singletonTuple i := ⟨t 0, ht⟩
  have hh := congrArg (fun z ↦ P.map
    (homOfLE (le_of_eq (singletonIntersection U i))).op z) (hs _)
  change P.map (homOfLE (le_of_eq (singletonIntersection U i))).op
    (P.map (homOfLE (le_top (a := U i))).op s) =
      P.map (homOfLE (le_of_eq (singletonIntersection U i))).op (sf i) at hh
  dsimp only [sf] at hh
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp] at hh
  have he : (homOfLE (le_of_eq (singletonIntersection U i)) ≫
      homOfLE (le_of_eq (singletonIntersection U i).symm)) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [he, op_id, P.map_id, ConcreteCategory.id_apply] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingRow_mono {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    Mono (alternatingCechPresheafZero U
      ((alternatingCechModulePresheaf (X := X)).obj M)) := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  apply (ModuleCat.mono_iff_injective _).mpr
  intro s t hst
  let F := (SheafOfModules.forgetToSheafModuleCat (moduleRings X.toRingedSpace)
    (op ⊤) isTerminalTop.op).obj M
  let G : TopCat.Sheaf
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) X.toTopCat :=
    ⟨F.obj, F.property⟩
  apply G.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU]) s t
  intro i
  have hh := congrArg (fun z ↦ P.map
    (homOfLE (le_of_eq (singletonIntersection U i).symm)).op (z (singletonTuple i))) hst
  change P.map (homOfLE (le_of_eq (singletonIntersection U i).symm)).op
    (P.map (homOfLE (le_top (a := alternatingCechIntersection U (singletonTuple i)))).op s) =
      P.map (homOfLE (le_of_eq (singletonIntersection U i).symm)).op
        (P.map (homOfLE (le_top
          (a := alternatingCechIntersection U (singletonTuple i)))).op t) at hh
  simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The actual increasing-tuple row augmentation is a quasi-isomorphism.
Its degree-zero component is specified, so the map is uniquely determined.

Source: Stacks Project, Tags 01EP and 01FM; Tag 08C1, first paragraph.
(blueprint: lem-sc-injective-alternating-cech-row-augmentation)

Proof: Restriction of a global section to each increasing one-tuple has zero
Čech differential, because the two restrictions to every pair agree. Construct
this map in nonnegative degrees with fromSingle₀Equiv. For degree zero, evaluate
a cocycle on increasing pairs to show its singleton sections agree on pairwise
intersections (reverse the pair when necessary). Sheaf gluing gives a section
on the union, which is X by hU. Sheaf separatedness makes restriction injective.
The scalar identification at the top is the identity, so this proves that the
augmentation induces an isomorphism on degree-zero homology.
For positive degrees, construct the full-tuple SiteCechComplex with actual finite
intersections. Its injective Čech cohomology vanishes by Tag 01EP. Define a map
from it to the underlying abelian alternating row by evaluating on the underlying
function of each order embedding. Reindex strictly monotone functions as order
embeddings; the signed face formula verifies that this is a cochain map.
The existing Tag 01FM restriction homotopy theorem gives it a homotopy inverse,
so its map on homology is an isomorphism and the alternating row is exact in
positive degrees. The elementwise exactness criteria for abelian groups and
modules agree, so forgetting scalars reflects this exactness.
Extension by zero to integer degrees preserves quasi-isomorphisms. Identify the
extension of the single complex with the integer single complex via extendSingleIso;
its degree-zero formula gives exactly alternatingCechZero. All constructions also
work for the empty cover: the empty-family gluing axiom gives zero global sections.
The zero module case is included as well. -/
theorem injective_alternatingCech_row_augmentation
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    ∃ f : (HomologicalComplex.single
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (ComplexShape.up ℤ) 0).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M) ⟶
          (alternatingCechModuleFunctor U).obj M,
      f.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)).hom ≫
          alternatingCechZero U M ∧ QuasiIso f := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  let C := alternatingCechComplex U P
  let V := (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M
  let e := ModuleCat.restrictScalarsId'App
    ((moduleRings X.toRingedSpace).obj.map (isTerminalTop.op.to (op ⊤))).hom
    (Scheme.Modules.moduleCech_top_restriction X) (M.val.obj (op ⊤))
  let z : V ⟶ C.X 0 := e.inv ≫ alternatingCechPresheafZero U P
  have hz : z ≫ C.d 0 1 = 0 := by
    rw [Category.assoc, alternatingRow_zero_d, comp_zero]
  let b := (CochainComplex.fromSingle₀Equiv C V).symm ⟨z, hz⟩
  have hb : b.f 0 = z := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero z hz
  have hmono : Mono (alternatingCechPresheafZero U P) := alternatingRow_mono U hU M
  have hbq : QuasiIso b := by
    rw [quasiIso_iff]
    intro p
    by_cases hp : p = 0
    · subst p
      rw [CochainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros _ rfl rfl (C.shape _ _ (by simp))]
      constructor
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro c hc
        obtain ⟨s, hs⟩ := alternatingRow_glue U hU M c hc
        refine ⟨e.hom s, ?_⟩
        change b.f 0 (e.hom s) = c
        rw [hb]
        change (e.inv ≫ alternatingCechPresheafZero U P) (e.hom s) = c
        rw [← ConcreteCategory.comp_apply, e.hom_inv_id_assoc]
        exact hs
      · change Mono (b.f 0)
        rw [hb]
        change Mono (e.inv ≫ alternatingCechPresheafZero U P)
        infer_instance
    · apply (quasiIsoAt_iff_exactAt b p ?_).mpr (alternatingRow_positive U hU M p (by omega))
      exact HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0 V p hp
  have := hbq
  let E := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat V 0 0 rfl
  let f := E.inv ≫ HomologicalComplex.extendMap b ComplexShape.embeddingUpNat
  refine ⟨f, ?_, by dsimp [f]; infer_instance⟩
  dsimp only [f, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f b ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hb]
  dsimp only [z]
  simp [alternatingCechZero, P, C, V, e, Category.assoc,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

end AlgebraicGeometry
