/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Local finite free lifting

Source: Stacks Project, Modules, Tags 01B5 and 01B8.
(blueprint: lem-weil-pbc-module-finite-free-local-lift).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private noncomputable def flattenFunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {K : C} (A : Over K) :
    SheafOfModules.{u} ((R.over K).over A) ⥤ SheafOfModules.{u} (R.over A.left) :=
  SheafOfModules.pushforward (F := A.iteratedSliceBackward) (𝟙 (R.over A.left))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def flattenModuleIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {K : C} (A : Over K) (H : SheafOfModules.{u} R) :
    (flattenFunctor R A).obj ((H.over K).over A) ≅ H.over A.left :=
  (SheafOfModules.fullyFaithfulForget (R.over A.left)).preimageIso <|
    PresheafOfModules.isoMk (fun Z ↦ Iso.refl _) (by intro Z W f; rfl)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def flattenUnitIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {K : C} (A : Over K) :
    unit (R.over A.left) ≅ (flattenFunctor R A).obj (unit ((R.over K).over A)) :=
  (SheafOfModules.fullyFaithfulForget (R.over A.left)).preimageIso <|
    PresheafOfModules.isoMk (fun Z ↦ Iso.refl _) (by intro Z W f; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_generator_epi
    (X : TopCat.{u}) (R : X.Sheaf RingCat.{u}) (K : TopologicalSpace.Opens X)
    (H : SheafOfModules.{u} R)
    [(H.over K).IsFiniteType] (x : K) :
    ∃ (A : TopologicalSpace.Opens X) (_hAK : A ≤ K), (x : X) ∈ A ∧ ∃ (n : ℕ)
      (q : free (R := R.over A) (ULift.{u} (Fin n)) ⟶
        H.over A), Epi q := by
  classical
  obtain ⟨d, hd⟩ := IsFiniteType.exists_localGeneratorsData (H.over K)
  have hc := d.coversTop (Over.mk (𝟙 K))
  change Sieve.overEquiv (Over.mk (𝟙 K))
    (Sieve.ofObjects d.X (Over.mk (𝟙 K))) ∈ _root_.Opens.grothendieckTopology X K at hc
  obtain ⟨W, f, hf, hxW⟩ := hc x.val x.property
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨i, ⟨g⟩⟩ := hf
  let A := (d.X i).left
  have hAK : A ≤ K := leOfHom (d.X i).hom
  have hxA : x.val ∈ A := (leOfHom g.left) hxW
  let F := flattenFunctor R (d.X i)
  have : (d.X i).iteratedSliceBackward.IsLeftAdjoint :=
    (d.X i).iteratedSliceEquiv.symm.toAdjunction.isLeftAdjoint
  have : F.IsLeftAdjoint := SheafOfModules.isLeftAdjoint_pushforward_of_isIso
    (F := (d.X i).iteratedSliceBackward)
    (R := (R.over K).over (d.X i)) (𝟙 (R.over A))
  have : (d.generators i).IsFiniteType := hd.isFiniteType i
  let : Fintype (d.generators i).I := Fintype.ofFinite (d.generators i).I
  let n := Fintype.card (d.generators i).I
  let e : ULift.{u} (Fin n) ≃ (d.generators i).I :=
    Equiv.ulift.trans (Fintype.equivFin (d.generators i).I).symm
  let q₀ := (SheafOfModules.freeFunctor
    (R := (R.over K).over (d.X i))).mapIso e.toIso
  let eH := flattenModuleIso R (d.X i) H
  let η := flattenUnitIso R (d.X i)
  let q : free (R := R.over A) (ULift.{u} (Fin n)) ⟶ H.over A :=
    (mapFreeIso F (ULift.{u} (Fin n)) η).hom ≫
      F.map (q₀.hom ≫ (d.generators i).π) ≫ eH.hom
  refine ⟨A, hAK, hxA, n, q, ?_⟩
  dsimp only [q]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem local_section_lift
    (X : TopCat.{u}) (R : X.Sheaf RingCat.{u}) (V A : TopologicalSpace.Opens X) (hAV : A ≤ V)
    (G M : SheafOfModules.{u} (R.over V))
    (p : G ⟶ M) [Epi p]
    (t : M.val.obj (Opposite.op (Over.mk (homOfLE hAV)))) (x : A) :
    ∃ (U : TopologicalSpace.Opens X) (hUA : U ≤ A), (x : X) ∈ U ∧
      ∃ (g : G.val.obj (Opposite.op (Over.mk (homOfLE (hUA.trans hAV))))),
        p.val.app (Opposite.op (Over.mk (homOfLE (hUA.trans hAV)))) g =
          M.val.map (Over.homMk (homOfLE hUA)).op t := by
  let T := SheafOfModules.toSheaf.{u} (R.over V)
  have : Epi (T.map p) := inferInstance
  have hl := (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ (T.map p)).mpr inferInstance
  have hc := hl.imageSieve_mem t
  change Sieve.overEquiv (Over.mk (homOfLE hAV))
    (Presheaf.imageSieve (T.map p).hom t) ∈ _root_.Opens.grothendieckTopology X A at hc
  obtain ⟨U, f, hf, hxU⟩ := hc x.val x.property
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨g, hg⟩ := hf
  exact ⟨U, leOfHom f, hxU, g, hg⟩

private theorem free_comp_eq_of_sections
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) (I : Type u)
    [CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I) F]
    (η : unit S ≅ F.obj (unit R)) {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S}
    (l : free I ⟶ N) (p : N ⟶ F.obj M) (q : free I ⟶ M)
    (h : ∀ i, sectionsMap p (N.freeHomEquiv l i) =
      (F.obj M).unitHomEquiv (η.hom ≫ F.map (ιFree i ≫ q))) :
    l ≫ p = (mapFreeIso F I η).hom ≫ F.map q := by
  apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext (isColimitFreeCofan I)
  intro i
  simp only [freeCofan_inj]
  rw [← Category.assoc, ← Category.assoc, ιFree_mapFreeIso_hom,
    Category.assoc η.hom, ← F.map_comp]
  apply (F.obj M).unitHomEquiv.injective
  rw [unitHomEquiv_comp_apply]
  exact h i

set_option backward.isDefEq.respectTransparency false in
private theorem finite_free_lift
    (X : TopCat.{u}) (R : X.Sheaf RingCat.{u}) (V K : TopologicalSpace.Opens X) (hKV : K ≤ V)
    (H : SheafOfModules.{u} R)
    [(H.over K).IsFiniteType]
    (G : SheafOfModules.{u} (R.over V))
    (p : G ⟶ H.over V) [Epi p] (x : K) :
    ∃ (U : TopologicalSpace.Opens X) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ (n : ℕ)
      (l : free (R := R.over U) (ULift.{u} (Fin n)) ⟶
        (overMap R (homOfLE (hUK.trans hKV))).obj G),
      Epi (l ≫ (overMap R
        (homOfLE (hUK.trans hKV))).map p) := by
  classical
  obtain ⟨A, hAK, hxA, n, q, hq⟩ := finite_generator_epi X R K H x
  let I := ULift.{u} (Fin n)
  let s : I → (H.over A).sections := (H.over A).freeHomEquiv q
  have hl (i : I) := local_section_lift X R V A (hAK.trans hKV) G (H.over V) p
    ((s i).val (Opposite.op (Over.mk (𝟙 A)))) ⟨x.val, hxA⟩
  choose B hBA hxB g hg using hl
  let U := A ⊓ ⨅ i, B i
  have hUA : U ≤ A := inf_le_left
  have hUB (i : I) : U ≤ B i := inf_le_right.trans (iInf_le B i)
  have hxU : x.val ∈ U := by
    refine ⟨hxA, ?_⟩
    change x.val ∈ (⨅ i, B i : TopologicalSpace.Opens X)
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxB
  let F := overMap R (homOfLE (hUA.trans (hAK.trans hKV)))
  let FA := overMap R (homOfLE hUA)
  let t (i : I) : (F.obj G).sections :=
    PresheafOfModules.sectionsMk (fun Z ↦ G.val.map
      (Over.homMk (homOfLE ((leOfHom Z.unop.hom).trans (hUB i))) :
        (Over.map (homOfLE (hUA.trans (hAK.trans hKV)))).obj Z.unop ⟶
          Over.mk (homOfLE ((hBA i).trans (hAK.trans hKV)))).op (g i))
      (by
        intro Z W f
        change G.val.map ((Over.map (homOfLE
          (hUA.trans (hAK.trans hKV)))).map f.unop).op (G.val.map
          (Over.homMk (homOfLE ((leOfHom Z.unop.hom).trans (hUB i))) :
            (Over.map (homOfLE (hUA.trans (hAK.trans hKV)))).obj Z.unop ⟶
              Over.mk (homOfLE ((hBA i).trans (hAK.trans hKV)))).op (g i)) = _
        rw [← PresheafOfModules.map_comp_apply]
        rfl)
  let l : free (R := R.over U) I ⟶ F.obj G := (F.obj G).freeHomEquiv.symm t
  refine ⟨U, hUA.trans hAK, hxU, n, l, ?_⟩
  have heq : l ≫ F.map p =
      (mapFreeIso FA I (overMapUnitIso (R := R) (homOfLE hUA)).symm).hom ≫ FA.map q := by
    refine free_comp_eq_of_sections FA I _ (M := H.over A) l (F.map p) q (fun i ↦ ?_)
    simp only [l, Equiv.apply_symm_apply, overMapUnitIso, Iso.symm_hom, Iso.refl_inv]
    apply PresheafOfModules.sections_ext
    intro Z
    change p.val.app (Opposite.op ((Over.map (homOfLE
      (hUA.trans (hAK.trans hKV)))).obj Z.unop)) (G.val.map
      (Over.homMk (homOfLE ((leOfHom Z.unop.hom).trans (hUB i))) :
        (Over.map (homOfLE (hUA.trans (hAK.trans hKV)))).obj Z.unop ⟶
          Over.mk (homOfLE ((hBA i).trans (hAK.trans hKV)))).op (g i)) =
      (s i).val (Opposite.op ((Over.map (homOfLE hUA)).obj Z.unop))
    rw [PresheafOfModules.naturality_apply, hg i]
    rw [← PresheafOfModules.map_comp_apply]
    exact (s i).property
      (Over.homMk (homOfLE ((leOfHom Z.unop.hom).trans hUA)) :
        (Over.map (homOfLE hUA)).obj Z.unop ⟶ Over.mk (𝟙 A)).op
  rw [heq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A finite type target of an epimorphism admits, near each point, a finite free
map to the source whose composite is still an epimorphism.

Source: Stacks Project, Modules, Definition 01B5 and Lemma 01B8.
(blueprint: lem-weil-pbc-module-finite-free-local-lift).

Proof: On K choose finite local generators for H using its finite type hypothesis.
Each generator lifts locally through p, since an epimorphism of module sheaves
is locally surjective. Intersect the finitely many lifting neighbourhoods.
The lifts define a map from the finite free sheaf, and its composite with p is
precisely the restricted generating map, hence epi. Restriction preserves free
sheaves and epimorphisms. The slice over V and its further slice over U give
exactly the displayed restriction functor. With no generators use the zero map
from the free sheaf on Fin 0: the target is zero on the chosen neighbourhood.
There is no point to consider on empty K. No finite presentation is required. -/
theorem exists_finite_free_local_lift
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (p : G ⟶ H.over V) [Epi p] (x : K) :
    ∃ (U : X.Opens) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ (n : ℕ)
      (l : free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n)) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hUK.trans hKV))).obj G),
      Epi (l ≫ (overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map p) := by
  exact finite_free_lift (TopCat.of X) (moduleRings X.toRingedSpace) V K hKV H G p x

end AlgebraicGeometry.Scheme.Modules

