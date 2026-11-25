/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
import all WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import all WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses

/-! # The ordinary-to-resolved global Hom roof

Source: Stacks Project, dga.tex, Example 09L9 (example-category-complexes),
derived.tex, Lemma 070I (lemma-K-injective), and sites-cohomology.tex, Section 0B6E.
(blueprint: lem-sf-global-hom-resolution-roof)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.HomComplex

namespace CategoryTheory

variable (B : Type v) [CommRing B] {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]

/-- Product Hom with scalars retained, using Mathlib's cochains and exact signed differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHom (X Y : CochainComplex A ℤ) : CochainComplex (ModuleCat.{v} B) ℤ where
  X n := ModuleCat.of B (Cochain X Y n)
  d n m := ModuleCat.ofHom (δ_hom B X Y n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ n m k z

/-- The degreewise pre/postcomposition map on the existing linear cochains.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMapTerm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) :
    (globalLinearHom B X Y).X n ⟶ (globalLinearHom B X' Y').X n :=
  ModuleCat.ofHom
    { toFun := fun f ↦ (Cochain.ofHom a).comp (f.comp (Cochain.ofHom b) (add_zero n))
        (zero_add n)
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- The pre/postcomposition maps commute with the Hom differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof).
Proof: expand both differentials as `d_Y f - (-1)^n f d_X`, and use the chain-map
identities for `a` and `b`. The two expressions agree componentwise. -/
theorem globalLinearHomMap_comm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n m : ℤ) :
    globalLinearHomMapTerm B a b n ≫ (globalLinearHom B X' Y').d n m =
      (globalLinearHom B X Y).d n m ≫ globalLinearHomMapTerm B a b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ n m ((Cochain.ofHom a).comp
      (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)) =
    (Cochain.ofHom a).comp
      ((δ n m z).comp (Cochain.ofHom b) (add_zero m)) (zero_add m)
  rw [δ_ofHom_comp, δ_comp_ofHom]

/-- Actual pre/postcomposition chain map, with its prescribed component formula.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMap {X X' Y Y' : CochainComplex A ℤ} (a : X' ⟶ X) (b : Y ⟶ Y') :
    globalLinearHom B X Y ⟶ globalLinearHom B X' Y' where
  f := globalLinearHomMapTerm B a b
  comm' n m _ := globalLinearHomMap_comm B a b n m

/-- A resolution is only a complex and its given quasi-isomorphism, with the usual
K-injectivity predicate; no linear or functorial choice is part of this input.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolution (X : CochainComplex A ℤ) where
  I : CochainComplex A ℤ
  ι : X ⟶ I
  injective : I.IsKInjective
  quasiIso : QuasiIso ι

attribute [instance] GlobalHomResolution.injective GlobalHomResolution.quasiIso

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)]

/-- The identity resolution of a K-injective complex.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.self (X : CochainComplex A ℤ) [X.IsKInjective] :
    GlobalHomResolution X := ⟨X, 𝟙 X, inferInstance, inferInstance⟩

/-- Shift the actual augmentation, using the standard signed cochain shift.
Source: Stacks 09L9, 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.shift {X : CochainComplex A ℤ} (R : GlobalHomResolution X) (n : ℤ) :
    GlobalHomResolution (X⟦n⟧) :=
  ⟨R.I⟦n⟧, (shiftFunctor _ n).map R.ι, inferInstance, inferInstance⟩

/-- The resolved Hom object on the specified resolutions, exactly `q H(I_X,I_Y)`.
Source: Stacks 0B6E (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalResolvedHom {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) :
    DerivedCategory (ModuleCat.{v} B) :=
  DerivedCategory.Q.obj (globalLinearHom B R.I S.I)

/-- The actual class of an abstract cycle in the cohomology of the localized complex.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomClass (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (DerivedCategory.Q.obj (globalLinearHom B X Y)) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).inv.app
    (globalLinearHom B X Y) ((globalLinearHom B X Y).homologyπ n z)

private def roof_forgetIso (X Y : CochainComplex A ℤ) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (globalLinearHom B X Y) ≅ CochainComplex.HomComplex X Y :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro n m h
    ext z
    rfl)

omit [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
private theorem roof_precomp_quasiIso
    {X X' J : CochainComplex A ℤ} (a : X' ⟶ X) [QuasiIso a] [J.IsKInjective] :
    QuasiIso (globalLinearHomMap B a (𝟙 J)) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (globalLinearHomMap B a (𝟙 J)) (forget₂ (ModuleCat B) AddCommGrpCat)).mp
  have h : ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
      (globalLinearHomMap B a (𝟙 J)) =
      (roof_forgetIso B X J).hom ≫ externalMap a (𝟙 J) ≫
        (roof_forgetIso B X' J).inv := by
    ext n z
    change (Cochain.ofHom a).comp (z.comp (Cochain.ofHom (𝟙 J)) (add_zero n))
      (zero_add n) = ((Cochain.ofHom a).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 J)) (add_zero n)
    exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ _).symm
  rw [h]
  have := DerivedInternalHomSectionsModel.externalMap_quasiIso a (B := J)
  infer_instance

private theorem roof_precomp_quotient
    {K L T : CochainComplex A ℤ} (a : K ⟶ L) [QuasiIso a] [T.IsKInjective] :
    Function.Bijective (fun f :
      (HomotopyCategory.quotient A (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj T ↦
      (HomotopyCategory.quotient A (.up ℤ)).map a ≫ f) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let b := DerivedCategory.Qh.map (q.map a)
  have hb : IsIso b := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map a)
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) a).2 inferInstance
  have hK := CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) T
  have hL := CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) T
  constructor
  · intro f g h
    apply hL.injective
    apply (cancel_epi b).mp
    simpa only [b, q, Functor.map_comp] using congrArg DerivedCategory.Qh.map h
  · intro g
    obtain ⟨f, hf⟩ := hL.surjective (inv b ≫ DerivedCategory.Qh.map g)
    refine ⟨f, hK.injective ?_⟩
    rw [Functor.map_comp, hf]
    exact IsIso.hom_inv_id_assoc b _

private theorem roof_lifts (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (a : X ⟶ Y) :
    ∃ a' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a') (a ≫ S.ι)) ∧
      ∀ a'' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a'') (a ≫ S.ι)) →
        Nonempty (Homotopy a' a'') := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨f, hf⟩ := (roof_precomp_quotient R.ι).surjective (q.map (a ≫ S.ι))
  obtain ⟨a', rfl⟩ := q.map_surjective f
  have ha : q.map (R.ι ≫ a') = q.map (a ≫ S.ι) := by
    rw [Functor.map_comp]
    exact hf
  refine ⟨a', ⟨HomotopyCategory.homotopyOfEq _ _ ha⟩, ?_⟩
  intro a'' ⟨ha''⟩
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (roof_precomp_quotient R.ι).injective
  dsimp [q]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact ha.trans (HomotopyCategory.eq_of_homotopy _ _ ha'').symm

private theorem roof_comparison_lifts (X : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) :
    ∃ a : HomotopyEquiv R.I R'.I, Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨a, ⟨ha⟩, _⟩ := roof_lifts X X R R' (𝟙 X)
  obtain ⟨b, ⟨hb⟩, _⟩ := roof_lifts X X R' R (𝟙 X)
  have ha' : q.map R.ι ≫ q.map a = q.map R'.ι := by
    simpa using HomotopyCategory.eq_of_homotopy _ _ ha
  have hb' : q.map R'.ι ≫ q.map b = q.map R.ι := by
    simpa using HomotopyCategory.eq_of_homotopy _ _ hb
  refine ⟨⟨a, b, HomotopyCategory.homotopyOfEq _ _ ?_,
    HomotopyCategory.homotopyOfEq _ _ ?_⟩, ?_⟩
  · apply (roof_precomp_quotient R.ι).injective
    simp only [Functor.map_comp, Functor.map_id, Category.comp_id, ← Category.assoc]
    rw [ha', hb']
  · apply (roof_precomp_quotient R'.ι).injective
    simp only [Functor.map_comp, Functor.map_id, Category.comp_id, ← Category.assoc]
    rw [hb', ha']
  · simpa using Nonempty.intro ha

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
private theorem roof_map_id (X Y : CochainComplex A ℤ) :
    globalLinearHomMap B (𝟙 X) (𝟙 Y) = 𝟙 (globalLinearHom B X Y) := by
  ext n z
  change (Cochain.ofHom (𝟙 X)).comp (z.comp (Cochain.ofHom (𝟙 Y)) (add_zero n))
    (zero_add n) = z
  simp

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
private theorem roof_map_comp
    {X X' X'' Y Y' Y'' : CochainComplex A ℤ}
    (a : X' ⟶ X) (a' : X'' ⟶ X') (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    globalLinearHomMap B a b ≫ globalLinearHomMap B a' b' =
      globalLinearHomMap B (a' ≫ a) (b ≫ b') := by
  ext n z
  change (Cochain.ofHom a').comp
    (((Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n))
      (zero_add n)).comp (Cochain.ofHom b') (add_zero n)) (zero_add n) =
    (Cochain.ofHom (a' ≫ a)).comp (z.comp (Cochain.ofHom (b ≫ b'))
      (add_zero n)) (zero_add n)
  ext p q hpq
  simp

private def roof_precomp_homotopy {X X' Y : CochainComplex A ℤ}
    {a a' : X' ⟶ X} (h : Homotopy a a') :
    Homotopy (globalLinearHomMap B a (𝟙 Y)) (globalLinearHomMap B a' (𝟙 Y)) := by
  let s : Cochain (globalLinearHom B X Y) (globalLinearHom B X' Y) (-1) :=
    Cochain.mk fun j k hjk ↦ ModuleCat.ofHom
      { toFun := fun φ ↦ j.negOnePow • (Cochain.ofHomotopy h).comp φ (by omega)
        map_add' := fun φ ψ ↦ by simp [smul_add]
        map_smul' := fun b φ ↦ by simp [smul_comm b j.negOnePow] }
  refine (Cochain.equivHomotopy _ _).symm ⟨s, ?_⟩
  apply Cochain.ext₀
  intro j
  simp only [Cochain.add_v]
  rw [δ_v (-1) 0 (by omega) s j j (by omega) (j - 1) (j + 1)
    (by omega) (by omega)]
  simp only [Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  dsimp [s, globalLinearHomMap, globalLinearHomMapTerm, globalLinearHom, δ_hom]
  simp only [one_smul]
  change (Cochain.ofHom a).comp (φ.comp (Cochain.ofHom (𝟙 Y)) (add_zero j))
      (zero_add j) =
    δ (j - 1) j (j.negOnePow • (Cochain.ofHomotopy h).comp φ (by omega)) +
      (j + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ j (j + 1) φ) (by omega) +
      (Cochain.ofHom a').comp (φ.comp (Cochain.ofHom (𝟙 Y)) (add_zero j))
        (zero_add j)
  rw [δ_units_smul, δ_comp (Cochain.ofHomotopy h) φ (by omega)
    0 (j + 1) j (by omega) (by omega) rfl, δ_ofHomotopy]
  simp only [smul_add, smul_smul, Int.units_mul_self, one_smul,
    Int.negOnePow_succ, Units.neg_smul, Cochain.sub_comp, Cochain.comp_id]
  abel

private def roof_postcomp_homotopy {X Y Y' : CochainComplex A ℤ}
    {b b' : Y ⟶ Y'} (h : Homotopy b b') :
    Homotopy (globalLinearHomMap B (𝟙 X) b) (globalLinearHomMap B (𝟙 X) b') := by
  let s : Cochain (globalLinearHom B X Y) (globalLinearHom B X Y') (-1) :=
    Cochain.mk fun j k hjk ↦ ModuleCat.ofHom
      { toFun := fun φ ↦ φ.comp (Cochain.ofHomotopy h) (by omega)
        map_add' := fun φ ψ ↦ by simp
        map_smul' := fun b φ ↦ by simp }
  refine (Cochain.equivHomotopy _ _).symm ⟨s, ?_⟩
  apply Cochain.ext₀
  intro j
  simp only [Cochain.add_v]
  rw [δ_v (-1) 0 (by omega) s j j (by omega) (j - 1) (j + 1)
    (by omega) (by omega)]
  simp only [Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  dsimp [s, globalLinearHomMap, globalLinearHomMapTerm, globalLinearHom, δ_hom]
  simp only [one_smul]
  change (Cochain.ofHom (𝟙 X)).comp (φ.comp (Cochain.ofHom b) (add_zero j))
      (zero_add j) =
    δ (j - 1) j (φ.comp (Cochain.ofHomotopy h) (by omega)) +
      (δ j (j + 1) φ).comp (Cochain.ofHomotopy h) (by omega) +
      (Cochain.ofHom (𝟙 X)).comp (φ.comp (Cochain.ofHom b') (add_zero j))
        (zero_add j)
  rw [δ_comp φ (Cochain.ofHomotopy h) (by omega)
    (j + 1) 0 j (by omega) rfl (by omega), δ_ofHomotopy]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    Cochain.comp_sub, Cochain.id_comp]
  abel

omit [HasDerivedCategory.{w} A] in
private theorem roof_homotopy_invariance
    {X X' Y Y' : CochainComplex A ℤ} (a a' : X' ⟶ X) (b b' : Y ⟶ Y')
    (ha : Nonempty (Homotopy a a')) (hb : Nonempty (Homotopy b b')) :
    DerivedCategory.Q.map (globalLinearHomMap B a b) =
      DerivedCategory.Q.map (globalLinearHomMap B a' b') := by
  have he (a : X' ⟶ X) (b : Y ⟶ Y') :
      globalLinearHomMap B a b =
        globalLinearHomMap B a (𝟙 Y) ≫ globalLinearHomMap B (𝟙 X') b := by
    rw [roof_map_comp]
    simp
  rw [he a b, he a' b', Functor.map_comp, Functor.map_comp]
  rw [DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat B)
      (roof_precomp_homotopy B ha.some),
    DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat B)
      (roof_postcomp_homotopy B hb.some)]

private noncomputable def roof_c
    (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) :
    DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S :=
  letI := roof_precomp_quasiIso B R.ι (J := S.I)
  DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι) ≫
    inv (DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)))

private theorem roof_c_roof
    (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) :
    roof_c B X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι) := by
  have := roof_precomp_quasiIso B R.ι (J := S.I)
  dsimp [roof_c]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

omit [HasDerivedCategory.{w} A] in
private theorem roof_Q_comp
    {X X' X'' Y Y' Y'' : CochainComplex A ℤ}
    (a : X' ⟶ X) (a' : X'' ⟶ X') (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫
        DerivedCategory.Q.map (globalLinearHomMap B a' b') =
      DerivedCategory.Q.map (globalLinearHomMap B (a' ≫ a) (b ≫ b')) := by
  rw [← Functor.map_comp, roof_map_comp]

private theorem roof_naturality
    (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I)
    (ha : Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)))
    (hb : Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι))) :
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫ roof_c B X' Y' R' S' =
      roof_c B X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B a' b') := by
  have := roof_precomp_quasiIso B R'.ι (J := S'.I)
  have hj : DerivedCategory.Q.map (globalLinearHomMap B a' b') ≫
      DerivedCategory.Q.map (globalLinearHomMap B R'.ι (𝟙 S'.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) ≫
        DerivedCategory.Q.map (globalLinearHomMap B a b') := by
    rw [roof_Q_comp, roof_Q_comp]
    simpa only [Category.id_comp, Category.comp_id] using
      roof_homotopy_invariance B (R'.ι ≫ a') (a ≫ R.ι) b' b' ha
        ⟨Homotopy.refl _⟩
  apply (cancel_mono (DerivedCategory.Q.map (globalLinearHomMap B R'.ι (𝟙 S'.I)))).mp
  rw [Category.assoc, roof_c_roof, Category.assoc, hj,
    ← Category.assoc, roof_c_roof, roof_Q_comp, roof_Q_comp]
  simpa only [Category.id_comp, Category.comp_id] using
    (roof_homotopy_invariance B a a (S.ι ≫ b') (b ≫ S'.ι)
      ⟨Homotopy.refl _⟩ hb).symm

private def roof_homIso {X X' Y Y' : CochainComplex A ℤ}
    (a : HomotopyEquiv X X') (b : HomotopyEquiv Y Y') :
    DerivedCategory.Q.obj (globalLinearHom B X Y) ≅
      DerivedCategory.Q.obj (globalLinearHom B X' Y') where
  hom := DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)
  inv := DerivedCategory.Q.map (globalLinearHomMap B a.hom b.inv)
  hom_inv_id := by
    rw [roof_Q_comp, roof_homotopy_invariance B _ (𝟙 X) _ (𝟙 Y)
      ⟨a.homotopyHomInvId⟩ ⟨b.homotopyHomInvId⟩, roof_map_id, Functor.map_id]
  inv_hom_id := by
    rw [roof_Q_comp, roof_homotopy_invariance B _ (𝟙 X') _ (𝟙 Y')
      ⟨a.homotopyInvHomId⟩ ⟨b.homotopyInvHomId⟩, roof_map_id, Functor.map_id]

private def roof_e {X : CochainComplex A ℤ} (R R' : GlobalHomResolution X) :
    HomotopyEquiv R.I R'.I := (roof_comparison_lifts X R R').choose

private theorem roof_e_comm {X : CochainComplex A ℤ} (R R' : GlobalHomResolution X) :
    Nonempty (Homotopy (R.ι ≫ (roof_e R R').hom) R'.ι) :=
  (roof_comparison_lifts X R R').choose_spec

private theorem roof_lift_unique {X : CochainComplex A ℤ}
    (R R' : GlobalHomResolution X) (a b : R.I ⟶ R'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a) R'.ι))
    (hb : Nonempty (Homotopy (R.ι ≫ b) R'.ι)) : Nonempty (Homotopy a b) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ((roof_precomp_quotient R.ι).injective ?_)⟩
  simpa only [Functor.map_comp] using
    (HomotopyCategory.eq_of_homotopy _ _ ha.some).trans
      (HomotopyCategory.eq_of_homotopy _ _ hb.some).symm

omit [HasDerivedCategory.{w} A] in
private theorem roof_inv_homotopy {X Y : CochainComplex A ℤ}
    (a b : HomotopyEquiv X Y) (h : Nonempty (Homotopy a.hom b.hom)) :
    Nonempty (Homotopy a.inv b.inv) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := HomotopyCategory.isoOfHomotopyEquiv a
  have hh : q.map a.hom = q.map b.hom := HomotopyCategory.eq_of_homotopy _ _ h.some
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (cancel_epi e.hom).mp
  change q.map a.hom ≫ q.map a.inv = q.map a.hom ≫ q.map b.inv
  have hiA : q.map a.hom ≫ q.map a.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ a.homotopyHomInvId
  have hiB : q.map b.hom ≫ q.map b.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ b.homotopyHomInvId
  rw [hiA, hh, hiB]

private def roof_comparison (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y) :
    globalResolvedHom B R S ≅ globalResolvedHom B R' S' :=
  roof_homIso B (roof_e R R') (roof_e S S')

private theorem roof_comparison_formula (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι))
    (hb : Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι)) :
    (roof_comparison B X Y R R' S S').hom =
      DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom) := by
  apply roof_homotopy_invariance B
  · exact roof_inv_homotopy _ _ (roof_lift_unique R R' _ _ (roof_e_comm R R') ha)
  · exact roof_lift_unique S S' _ _ (roof_e_comm S S') hb

omit [HasDerivedCategory.{w} A] in
private theorem roof_equiv_inv_comm {X : CochainComplex A ℤ}
    (R R' : GlobalHomResolution X) (a : HomotopyEquiv R.I R'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι)) :
    Nonempty (Homotopy (R'.ι ≫ a.inv) R.ι) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have hh : q.map R.ι ≫ q.map a.hom = q.map R'.ι := by
    simpa only [Functor.map_comp] using HomotopyCategory.eq_of_homotopy _ _ ha.some
  have hi : q.map a.hom ≫ q.map a.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ a.homotopyHomInvId
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  change q.map (R'.ι ≫ a.inv) = q.map R.ι
  rw [Functor.map_comp, ← hh, Category.assoc, hi, Category.comp_id]

private theorem roof_comparison_roof (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y) :
    roof_c B X Y R S ≫ (roof_comparison B X Y R R' S S').hom =
      roof_c B X Y R' S' := by
  have h := roof_naturality B X X Y Y R R' S S' (𝟙 X) (𝟙 Y)
    (roof_e R R').inv (roof_e S S').hom
    (by simpa using roof_equiv_inv_comm R R' (roof_e R R') (roof_e_comm R R'))
    (by simpa using roof_e_comm S S')
  simpa only [roof_comparison, roof_homIso, roof_map_id, Functor.map_id,
    Category.id_comp] using h.symm

private theorem roof_comparison_refl (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) :
    (roof_comparison B X Y R R S S).hom = 𝟙 _ := by
  have h := roof_comparison_formula B X Y R R S S
    (HomotopyEquiv.refl R.I) (HomotopyEquiv.refl S.I)
    (by exact ⟨Homotopy.ofEq (by simp [HomotopyEquiv.refl])⟩)
    (by exact ⟨Homotopy.ofEq (by simp [HomotopyEquiv.refl])⟩)
  simpa only [roof_comparison, HomotopyEquiv.refl_hom, HomotopyEquiv.refl_inv,
    roof_map_id, Functor.map_id, globalResolvedHom] using h

omit [HasDerivedCategory.{w} A] in
private theorem roof_equiv_trans_comm {X : CochainComplex A ℤ}
    (R R' R'' : GlobalHomResolution X) (a : HomotopyEquiv R.I R'.I)
    (b : HomotopyEquiv R'.I R''.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι))
    (hb : Nonempty (Homotopy (R'.ι ≫ b.hom) R''.ι)) :
    Nonempty (Homotopy (R.ι ≫ (a.trans b).hom) R''.ι) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  have h₁ := HomotopyCategory.eq_of_homotopy _ _ ha.some
  have h₂ := HomotopyCategory.eq_of_homotopy _ _ hb.some
  simp only [Functor.map_comp] at h₁ h₂ ⊢
  simpa only [HomotopyEquiv.trans_hom, Functor.map_comp, ← Category.assoc, h₁]
    using h₂

private theorem roof_comparison_cocycle (X Y : CochainComplex A ℤ)
    (R R' R'' : GlobalHomResolution X) (S S' S'' : GlobalHomResolution Y) :
    (roof_comparison B X Y R R' S S').hom ≫
        (roof_comparison B X Y R' R'' S' S'').hom =
      (roof_comparison B X Y R R'' S S'').hom := by
  rw [roof_comparison_formula B X Y R R'' S S''
    ((roof_e R R').trans (roof_e R' R''))
    ((roof_e S S').trans (roof_e S' S''))
    (roof_equiv_trans_comm _ _ _ _ _ (roof_e_comm R R') (roof_e_comm R' R''))
    (roof_equiv_trans_comm _ _ _ _ _ (roof_e_comm S S') (roof_e_comm S' S''))]
  exact roof_Q_comp B _ _ _ _

private theorem roof_normalization (X Y : CochainComplex A ℤ)
    [X.IsKInjective] [Y.IsKInjective] :
    roof_c B X Y (GlobalHomResolution.self X) (GlobalHomResolution.self Y) = 𝟙 _ := by
  simp [roof_c, GlobalHomResolution.self, roof_map_id, Functor.map_id]

private def roof_targetShift (X Y : CochainComplex A ℤ) (n : ℤ) :
    globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s ↦ (Cochain.rightShiftLinearEquiv B X Y (s + n) n s rfl).symm.toModuleIso)
    (by
      intro s t h
      ext f
      change n.negOnePow • δ (s + n) (t + n) (f.rightUnshift (s + n) rfl) =
        (δ s t f).rightUnshift (t + n) rfl
      rw [Cochain.δ_rightUnshift _ _ rfl _ _ rfl]
      simp only [smul_smul, Int.units_mul_self, one_smul])

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
private theorem roof_targetShift_formula (X Y : CochainComplex A ℤ) (n s : ℤ)
    (f : Cochain X (Y⟦n⟧) s) :
    ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
      ((roof_targetShift B X Y n).hom.f s f) = f.rightUnshift (s + n) rfl := by
  rfl

private noncomputable def roof_unit (X : CochainComplex A ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
      globalLinearHom B X X := by
  change (HomologicalComplex.single (ModuleCat B) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of B B) ⟶ globalLinearHom B X X
  let φ : ModuleCat.of B B ⟶ (globalLinearHom B X X).X 0 := ModuleCat.ofHom
    { toFun := fun b ↦ b • Cochain.ofHom (𝟙 X)
      map_add' := by intro b c; simp [add_smul]
      map_smul' := by intro b c; simp [smul_smul] }
  exact HomologicalComplex.mkHomFromSingle φ (by
    intro k hk
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change δ 0 k (b • Cochain.ofHom (𝟙 X)) = 0
    simp)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
private theorem roof_unit_formula (X : CochainComplex A ℤ) (b : B) :
    (roof_unit B X).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of B B)).inv b) = b • Cochain.ofHom (𝟙 X) := by
  dsimp [roof_unit]
  rw [HomologicalComplex.mkHomFromSingle_f]
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of B B)).hom ((HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (ModuleCat.of B B)).inv b)) • Cochain.ofHom (𝟙 X) = _
  simp

/-- The target-shift square of `GlobalHomResolutionRoof.targetShift_roof`, for any `c` satisfying
the roof equation and any `targetShift` given by the family identification.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-shift-fields). -/
structure GlobalHomResolutionRoofShiftFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
      globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧) where
  targetShift_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    (∀ (X Y : CochainComplex A ℤ) (n s : ℤ) (f : Cochain X (Y⟦n⟧) s),
      ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
        ((targetShift X Y n).hom.f s f) = f.rightUnshift (s + n) rfl) →
    ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ),
    c X (Y⟦n⟧) R (S.shift n) ≫ DerivedCategory.Q.map (targetShift R.I S.I n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B R.I S.I) =
      DerivedCategory.Q.map (targetShift X Y n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B X Y) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{v} B)) n).map (c X Y R S)

/-- Ordinary composition and its two coherences, for any `c` satisfying the roof equation and
any `comparison` given by conjugation with representing homotopy equivalences.
Source: Stacks 09L9, 06XY (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
structure GlobalHomResolutionRoofCompositionFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (comparison : ∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y), globalResolvedHom B R S ≅ globalResolvedHom B R' S')
    where
  comp : ∀ (X Y Z : CochainComplex A ℤ),
    globalLinearHom B Y Z ⊗ globalLinearHom B X Y ⟶ globalLinearHom B X Z
  comp_formula : ∀ (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n)
    (g : Cochain Y Z r) (f : Cochain X Y s),
    (comp X Y Z).f n
        (HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y)
          r s n h (g ⊗ₜ[B] f)) = f.comp g (by omega)
  composition_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    ∀ (X Y Z : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (T : GlobalHomResolution Z),
    (c Y Z S T ⊗ₘ c X Y R S) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
          (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y Z)
        (globalLinearHom B X Y) ≫ DerivedCategory.Q.map (comp X Y Z) ≫ c X Z R T
  composition_comparison :
    (∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y) (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I),
      Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) →
      Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι) →
      (comparison X Y R R' S S').hom =
        DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)) →
    ∀ (X Y Z : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (T T' : GlobalHomResolution Z),
    ((comparison Y Z S S' T T').hom ⊗ₘ (comparison X Y R R' S S').hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S'.I T'.I)
          (globalLinearHom B R'.I S'.I) ≫ DerivedCategory.Q.map (comp R'.I S'.I T'.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
        (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) ≫
        (comparison X Z R R' T T').hom

/-- The unit roof and the cohomology interpretation, for any `c` satisfying the roof equation
and any `unit` given by the scalar formula.
Source: Stacks 070I, 0B6E (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
structure GlobalHomResolutionRoofCohomologyFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (unit : ∀ (X : CochainComplex A ℤ),
      (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
        globalLinearHom B X X) where
  unit_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    (∀ (X : CochainComplex A ℤ) (b : B),
      (unit X).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of B B)).inv b) = b • Cochain.ofHom (𝟙 X)) →
    ∀ (X : CochainComplex A ℤ) (R : GlobalHomResolution X),
    DerivedCategory.Q.map (unit X) ≫ c X X R R = DerivedCategory.Q.map (unit R.I)
  cohomology : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧)
  cohomology_resolved : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B R.I S.I).cycles n) (f : Cocycle R.I S.I n),
    (f : Cochain R.I S.I n) = (globalLinearHom B R.I S.I).iCycles n z →
    cohomology X Y R S n (globalLinearHomClass B R.I S.I n z) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I
  cohomology_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) (f : Cocycle X Y n),
    (f : Cochain X Y n) = (globalLinearHom B X Y).iCycles n z →
    cohomology X Y R S n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map (c X Y R S)
          (globalLinearHomClass B X Y n z)) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y
  cohomology_naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    ∀ (n : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (globalResolvedHom B R S)),
    cohomology X' Y' R' S' n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
          (DerivedCategory.Q.map (globalLinearHomMap B a' b')) z) =
      DerivedCategory.Q.map a ≫ cohomology X Y R S n z ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- Any `targetShift` satisfying the family formula is natural in pre/postcomposition. -/
private theorem roof_targetShift_naturality
    (targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
      globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧)
    (hshift : ∀ (X Y : CochainComplex A ℤ) (n s : ℤ) (f : Cochain X (Y⟦n⟧) s),
      ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
        ((targetShift X Y n).hom.f s f) = f.rightUnshift (s + n) rfl)
    {X X' Y Y' : CochainComplex A ℤ} (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) :
    globalLinearHomMap B a (b⟦n⟧') ≫ (targetShift X' Y' n).hom =
      (targetShift X Y n).hom ≫ (globalLinearHomMap B a b)⟦n⟧' := by
  ext s : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  have h₁ : ((targetShift X' Y' n).hom.f s (globalLinearHomMapTerm B a (b⟦n⟧') s f) :
      Cochain X' Y' (s + n)) =
      (globalLinearHomMapTerm B a (b⟦n⟧') s f).rightUnshift (s + n) rfl :=
    hshift X' Y' n s _
  have h₂ : ((targetShift X Y n).hom.f s f : Cochain X Y (s + n)) =
      f.rightUnshift (s + n) rfl := hshift X Y n s f
  change (targetShift X' Y' n).hom.f s (globalLinearHomMapTerm B a (b⟦n⟧') s f) =
    globalLinearHomMapTerm B a b (s + n) ((targetShift X Y n).hom.f s f)
  rw [h₁, h₂]
  change ((Cochain.ofHom a).comp (f.comp (Cochain.ofHom (b⟦n⟧')) (add_zero s))
      (zero_add s)).rightUnshift (s + n) rfl =
    (Cochain.ofHom a).comp ((f.rightUnshift (s + n) rfl).comp (Cochain.ofHom b)
      (add_zero _)) (zero_add _)
  ext p q hpq
  simp [Cochain.rightUnshift_v _ _ _ p q hpq (p + s) rfl,
    HomologicalComplex.XIsoOfEq_hom_naturality]

/-- The shift square holds for every `c` satisfying the roof equation and every `targetShift`
given by the family identification (both hypotheses of the field).
Source: Stacks 09L9 and step 7 of lem-sf-global-hom-resolution-roof.
Proof: the roof equation determines `c`, since `Q (globalLinearHomMap B R.ι (𝟙 S.I))` is
invertible (precomposition by a quasi-isomorphism into a K-injective is a quasi-isomorphism),
and the family formula determines `targetShift`. Pre- and postcomposition by degree-0 chain
maps commute with `rightUnshift`, so the family identification is natural for the
precomposition leg `j` (by `R.ι`) and the postcomposition leg `p` (by `S.ι`, resp. its shift).
Apply `Q` and naturality of `Q.commShiftIso`. Postcompose both sides with the shift of the
invertible `Q.map j`; by the roof equation both become the image of `Q.map p`; cancel.
(blueprint: lem-sf-global-hom-resolution-roof-shift-fields). -/
theorem globalHom_resolution_roof_shift_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
      globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧) :
    Nonempty (GlobalHomResolutionRoofShiftFields B c targetShift) := by
  refine ⟨⟨fun hroof hshift X Y R S n ↦ ?_⟩⟩
  have := roof_precomp_quasiIso B R.ι (J := S.I)
  have h := hroof X (Y⟦n⟧) R (S.shift n)
  apply (cancel_mono ((shiftFunctor (DerivedCategory (ModuleCat B)) n).map
    (DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I))))).mp
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp,
    hroof, ← Functor.commShiftIso_hom_naturality, ← Functor.commShiftIso_hom_naturality,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← roof_targetShift_naturality B targetShift hshift,
    ← roof_targetShift_naturality B targetShift hshift, Functor.map_id,
    Functor.map_comp_assoc, Functor.map_comp_assoc]
  exact (reassoc_of% h) _

section CompositionChainMap

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)]

/-- Composition of cochains `g ⊗ f ↦ f.comp g`, as a `B`-bilinear map in fixed degrees.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
def globalLinearHomCompBilin (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n) :
    Cochain Y Z r →ₗ[B] Cochain X Y s →ₗ[B] Cochain X Z n :=
  LinearMap.mk₂ B (fun g f ↦ f.comp g (by omega))
    (fun _ _ _ ↦ Cochain.comp_add _ _ _ _)
    (fun _ _ _ ↦ Cochain.comp_smul _ _ _ _)
    (fun _ _ _ ↦ Cochain.add_comp _ _ _ _)
    (fun _ _ _ ↦ Cochain.smul_comp _ _ _ _)

/-- The degree-`n` component of composition, out of the total-tensor coproduct.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
def globalLinearHomCompTerm (X Y Z : CochainComplex A ℤ) (n : ℤ) :
    (globalLinearHom B Y Z ⊗ globalLinearHom B X Y).X n ⟶ (globalLinearHom B X Z).X n :=
  HomologicalComplex.mapBifunctorDesc (fun r s h ↦
    ModuleCat.ofHom (TensorProduct.lift (globalLinearHomCompBilin B X Y Z r s n h)))

private theorem roof_compTerm_ι (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y) r s n h ≫
      globalLinearHomCompTerm B X Y Z n =
    ModuleCat.ofHom (TensorProduct.lift (globalLinearHomCompBilin B X Y Z r s n h)) :=
  HomologicalComplex.ι_mapBifunctorDesc _ r s h

/-- Composition commutes with the differentials, by the Leibniz rule
`δ (f.comp g) = f.comp (δ g) + (-1)^|g| (δ f).comp g`.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalLinearHomComp_comm (X Y Z : CochainComplex A ℤ) (n m : ℤ) :
    globalLinearHomCompTerm B X Y Z n ≫ (globalLinearHom B X Z).d n m =
      (globalLinearHom B Y Z ⊗ globalLinearHom B X Y).d n m ≫
        globalLinearHomCompTerm B X Y Z m := by
  by_cases hnm : n + 1 = m
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    change r + s = n at h
    change HomologicalComplex.ιTensorObj _ _ r s n h ≫ _ =
      HomologicalComplex.ιTensorObj _ _ r s n h ≫ _
    rw [← Category.assoc, roof_compTerm_ι, ← Category.assoc,
      CochainComplex.ιTensorObj_d _ _ r s n m h hnm]
    rw [Preadditive.add_comp, Linear.units_smul_comp]
    simp only [Category.assoc, roof_compTerm_ι]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro g f
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
      LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.hom_ofHom]
    change δ n m (f.comp g (by omega)) = f.comp (δ r (r + 1) g) (by omega) +
      (r.negOnePow : ℤ) • (δ s (s + 1) f).comp g (by omega)
    rw [δ_comp f g (by omega) (s + 1) (r + 1) m (by omega) rfl rfl, Units.smul_def]
  · have hn : ¬ (ComplexShape.up ℤ).Rel n m := hnm
    rw [(globalLinearHom B X Z).shape n m hn,
      (globalLinearHom B Y Z ⊗ globalLinearHom B X Y).shape n m hn]
    simp

/-- Ordinary composition `H(Y,Z) ⊗ H(X,Y) ⟶ H(X,Z)`, `g ⊗ f ↦ f.comp g`.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
def globalLinearHomComp (X Y Z : CochainComplex A ℤ) :
    globalLinearHom B Y Z ⊗ globalLinearHom B X Y ⟶ globalLinearHom B X Z where
  f := globalLinearHomCompTerm B X Y Z
  comm' n m _ := globalLinearHomComp_comm B X Y Z n m

/-- The pure-tensor formula for ordinary composition.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalLinearHomComp_formula (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n)
    (g : Cochain Y Z r) (f : Cochain X Y s) :
    (globalLinearHomComp B X Y Z).f n
        (HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y)
          r s n h (g ⊗ₜ[B] f)) = f.comp g (by omega) :=
  congrArg (fun φ ↦ φ.hom (g ⊗ₜ[B] f)) (roof_compTerm_ι B X Y Z r s n h)

private theorem roof_tensor_ext {K L M : CochainComplex (ModuleCat.{v} B) ℤ}
    {φ ψ : K ⊗ L ⟶ M}
    (h : ∀ (r s n : ℤ) (h : r + s = n) (x : K.X r) (y : L.X s),
      φ.f n (HomologicalComplex.ιTensorObj K L r s n h (x ⊗ₜ[B] y)) =
        ψ.f n (HomologicalComplex.ιTensorObj K L r s n h (x ⊗ₜ[B] y))) : φ = ψ := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h r s n hrs x y

private theorem roof_whiskerLeft_apply (K : CochainComplex (ModuleCat.{v} B) ℤ)
    {L L' : CochainComplex (ModuleCat.{v} B) ℤ} (φ : L ⟶ L')
    (r s n : ℤ) (h : r + s = n) (x : K.X r) (y : L.X s) :
    (K ◁ φ).f n (HomologicalComplex.ιTensorObj K L r s n h (x ⊗ₜ[B] y)) =
      HomologicalComplex.ιTensorObj K L' r s n h (x ⊗ₜ[B] φ.f s y) :=
  congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[B] y)) (CochainComplex.ιTensorObj_whiskerLeft_f K φ r s n h)

private theorem roof_whiskerRight_apply {K K' : CochainComplex (ModuleCat.{v} B) ℤ}
    (φ : K ⟶ K') (L : CochainComplex (ModuleCat.{v} B) ℤ)
    (r s n : ℤ) (h : r + s = n) (x : K.X r) (y : L.X s) :
    (φ ▷ L).f n (HomologicalComplex.ιTensorObj K L r s n h (x ⊗ₜ[B] y)) =
      HomologicalComplex.ιTensorObj K' L r s n h (φ.f r x ⊗ₜ[B] y) :=
  congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[B] y)) (CochainComplex.Monoidal.ι_whiskerRight φ r s n h)

/-- Composition is natural in the source: `j ∘ comp = A ∘ (1 ⊗ j)`.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalLinearHomComp_precomp {X X' Y Z : CochainComplex A ℤ} (a : X' ⟶ X) :
    globalLinearHomComp B X Y Z ≫ globalLinearHomMap B a (𝟙 Z) =
      globalLinearHom B Y Z ◁ globalLinearHomMap B a (𝟙 Y) ≫ globalLinearHomComp B X' Y Z := by
  apply roof_tensor_ext
  intro r s n h g f
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [roof_whiskerLeft_apply, globalLinearHomComp_formula, globalLinearHomComp_formula]
  change (Cochain.ofHom a).comp ((f.comp g _).comp (Cochain.ofHom (𝟙 Z)) (add_zero n))
      (zero_add n) =
    ((Cochain.ofHom a).comp (f.comp (Cochain.ofHom (𝟙 Y)) (add_zero s)) (zero_add s)).comp g _
  simp

/-- Composition is dinatural in the middle variable: `A ∘ (1 ⊗ p) = B' ∘ (j ⊗ 1)`.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalLinearHomComp_middle {X Y Y' Z : CochainComplex A ℤ} (b : Y ⟶ Y') :
    globalLinearHom B Y' Z ◁ globalLinearHomMap B (𝟙 X) b ≫ globalLinearHomComp B X Y' Z =
      globalLinearHomMap B b (𝟙 Z) ▷ globalLinearHom B X Y ≫ globalLinearHomComp B X Y Z := by
  apply roof_tensor_ext
  intro r s n h g f
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [roof_whiskerLeft_apply, roof_whiskerRight_apply, globalLinearHomComp_formula,
    globalLinearHomComp_formula]
  change ((Cochain.ofHom (𝟙 X)).comp (f.comp (Cochain.ofHom b) (add_zero s)) (zero_add s)).comp
      g _ =
    f.comp ((Cochain.ofHom b).comp (g.comp (Cochain.ofHom (𝟙 Z)) (add_zero r)) (zero_add r)) _
  simp

/-- Composition is natural in the target: `p ∘ comp = B' ∘ (p ⊗ 1)`.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalLinearHomComp_postcomp {X Y Z Z' : CochainComplex A ℤ} (c : Z ⟶ Z') :
    globalLinearHomComp B X Y Z ≫ globalLinearHomMap B (𝟙 X) c =
      globalLinearHomMap B (𝟙 Y) c ▷ globalLinearHom B X Y ≫ globalLinearHomComp B X Y Z' := by
  apply roof_tensor_ext
  intro r s n h g f
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [roof_whiskerRight_apply, globalLinearHomComp_formula, globalLinearHomComp_formula]
  change (Cochain.ofHom (𝟙 X)).comp ((f.comp g _).comp (Cochain.ofHom c) (add_zero n))
      (zero_add n) =
    f.comp ((Cochain.ofHom (𝟙 Y)).comp (g.comp (Cochain.ofHom c) (add_zero r)) (zero_add r)) _
  simp

end CompositionChainMap

omit [HasDerivedCategory.{w} A] in
/-- Abstract composition roof: if `c₁, c₂, c₃` satisfy roof equations along `a, b, e`, with the
final precomposition by `a` invertible after `Q`, then they are compatible with composition.
Source: Stacks 09L9, 06XY (blueprint: lem-sf-global-hom-resolution-roof-composition-fields).
Proof: naturality of `μ` and the three naturality squares of composition; cancel `Q.map j`. -/
theorem globalLinearHomComp_roof {X Y Z X' Y' Z' : CochainComplex A ℤ}
    (a : X ⟶ X') (b : Y ⟶ Y') (e : Z ⟶ Z')
    (c₁ : DerivedCategory.Q.obj (globalLinearHom B Y Z) ⟶
      DerivedCategory.Q.obj (globalLinearHom B Y' Z'))
    (c₂ : DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶
      DerivedCategory.Q.obj (globalLinearHom B X' Y'))
    (c₃ : DerivedCategory.Q.obj (globalLinearHom B X Z) ⟶
      DerivedCategory.Q.obj (globalLinearHom B X' Z'))
    (h₁ : c₁ ≫ DerivedCategory.Q.map (globalLinearHomMap B b (𝟙 Z')) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 Y) e))
    (h₂ : c₂ ≫ DerivedCategory.Q.map (globalLinearHomMap B a (𝟙 Y')) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) b))
    (h₃ : c₃ ≫ DerivedCategory.Q.map (globalLinearHomMap B a (𝟙 Z')) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) e))
    [IsIso (DerivedCategory.Q.map (globalLinearHomMap B a (𝟙 Z')))] :
    (c₁ ⊗ₘ c₂) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y' Z')
          (globalLinearHom B X' Y') ≫
        DerivedCategory.Q.map (globalLinearHomComp B X' Y' Z') =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y Z)
        (globalLinearHom B X Y) ≫ DerivedCategory.Q.map (globalLinearHomComp B X Y Z) ≫ c₃ := by
  apply (cancel_mono (DerivedCategory.Q.map (globalLinearHomMap B a (𝟙 Z')))).mp
  simp only [Category.assoc, h₃]
  rw [← Functor.map_comp, globalLinearHomComp_precomp, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    MonoidalCategory.tensorHom_def (C := DerivedCategory (ModuleCat.{v} B)),
    Category.assoc, ← whiskerLeft_comp_assoc, h₂,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    globalLinearHomComp_middle, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, ← comp_whiskerRight_assoc, h₁,
    Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp,
    ← globalLinearHomComp_postcomp, Functor.map_comp]

omit [HasDerivedCategory.{w} A] in
private theorem roof_conj_roof {X X' Y Y' : CochainComplex A ℤ}
    (a : HomotopyEquiv X X') (b : HomotopyEquiv Y Y') :
    DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom) ≫
        DerivedCategory.Q.map (globalLinearHomMap B a.hom (𝟙 Y')) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) b.hom) := by
  rw [roof_Q_comp]
  exact roof_homotopy_invariance B _ _ _ _ ⟨a.homotopyHomInvId⟩
    ⟨Homotopy.ofEq (Category.comp_id _)⟩

/-- Ordinary composition out of the total tensor exists, and is compatible with every `c`
satisfying the roof equation and every `comparison` given by conjugation with representing
homotopy equivalences (the hypotheses of the two coherence fields).
Source: Stacks 09L9, 06XY and steps 1, 8-10 of lem-sf-global-hom-resolution-roof.
Proof: composition is bilinear and satisfies `d(gf) = d(g)f + (-1)^|g| g d(f)`, so it
descends through the total-tensor coproduct, with the pure-tensor formula by construction.
For `composition_roof` use the mixed pairings `A : H(I_Y,I_Z) ⊗ H(X,I_Y) → H(X,I_Z)` and
`B' : H(Y,I_Z) ⊗ H(X,Y) → H(X,I_Z)`: associativity gives `j comp = A(1 ⊗ j)`,
`A(1 ⊗ p) = B'(j ⊗ 1)`, `B'(p ⊗ 1) = p comp`; apply `Q`, naturality of `μ`, the roof
equation twice, and cancel the invertible final `Q.map j`. For `composition_comparison`,
choose representing homotopy equivalences `a, b` (they exist by the K-injective lifting);
the hypothesis makes the comparison conjugation by them, with `b a - 1 = dh + hd`;
`S(g ⊗ f) = (-1)^|g| a g h f b` is a homotopy on the total tensor, so the inserted
middle factor disappears after `Q`.
(blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalHom_resolution_roof_composition_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (comparison : ∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y), globalResolvedHom B R S ≅ globalResolvedHom B R' S') :
    Nonempty (GlobalHomResolutionRoofCompositionFields B c comparison) := by
  refine ⟨⟨globalLinearHomComp B, globalLinearHomComp_formula B, ?_, ?_⟩⟩
  · intro hc X Y Z R S T
    have := roof_precomp_quasiIso B R.ι (J := T.I)
    exact globalLinearHomComp_roof B R.ι S.ι T.ι _ _ _ (hc Y Z S T) (hc X Y R S)
      (hc X Z R T)
  · intro hcomp X Y Z R R' S S' T T'
    have := roof_precomp_quasiIso B (roof_e R R').hom (J := T'.I)
    rw [hcomp X Y R R' S S' _ _ (roof_e_comm R R') (roof_e_comm S S'),
      hcomp Y Z S S' T T' _ _ (roof_e_comm S S') (roof_e_comm T T'),
      hcomp X Z R R' T T' _ _ (roof_e_comm R R') (roof_e_comm T T')]
    exact globalLinearHomComp_roof B (roof_e R R').hom (roof_e S S').hom (roof_e T T').hom
      _ _ _ (roof_conj_roof B _ _) (roof_conj_roof B _ _) (roof_conj_roof B _ _)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The cocycle underlying a cycle of the linear Hom complex.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalLinearHomCyclesCocycle (X Y : CochainComplex A ℤ) (n : ℤ) :
    (globalLinearHom B X Y).cycles n →+ Cocycle X Y n where
  toFun z := Cocycle.mk ((globalLinearHom B X Y).iCycles n z) (n + 1) rfl (by
    have h := congrArg (fun f ↦ f.hom z) ((globalLinearHom B X Y).iCycles_d n (n + 1))
    exact h)
  map_zero' := by ext1; simp
  map_add' x y := by ext1; simp

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The underlying cochain of `globalLinearHomCyclesCocycle` is the image of the cycle.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCyclesCocycle_coe (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    (globalLinearHomCyclesCocycle B X Y n z : Cochain X Y n) =
      (globalLinearHom B X Y).iCycles n z := by
  simp [globalLinearHomCyclesCocycle]

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- Cycles of the linear Hom complex are exactly the cocycles.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCyclesCocycle_bijective (X Y : CochainComplex A ℤ) (n : ℤ) :
    Function.Bijective (globalLinearHomCyclesCocycle B X Y n) := by
  constructor
  · intro x y h
    apply (ModuleCat.mono_iff_injective ((globalLinearHom B X Y).iCycles n)).mp inferInstance
    simpa [globalLinearHomCyclesCocycle_coe] using congrArg Subtype.val h
  · intro x
    refine ⟨(globalLinearHom B X Y).cyclesMk (x : Cochain X Y n) (n + 1) (by simp) ?_, ?_⟩
    · have := (Cocycle.mem_iff n (n + 1) rfl (x : Cochain X Y n)).mp x.2
      exact this
    · ext1
      rw [globalLinearHomCyclesCocycle_coe]
      exact (globalLinearHom B X Y).i_cyclesMk (x : Cochain X Y n) (n + 1) (by simp) _

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- Cycles of the linear Hom complex are exactly the cocycles.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalLinearHomCyclesAddEquiv (X Y : CochainComplex A ℤ) (n : ℤ) :
    (globalLinearHom B X Y).cycles n ≃+ Cocycle X Y n :=
  AddEquiv.ofBijective _ (globalLinearHomCyclesCocycle_bijective B X Y n)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The underlying cochain of the cocycle attached to a cycle.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCyclesAddEquiv_coe (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    (globalLinearHomCyclesAddEquiv B X Y n z : Cochain X Y n) =
      (globalLinearHom B X Y).iCycles n z :=
  globalLinearHomCyclesCocycle_coe B X Y n z

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The cocycle attached to a boundary is the corresponding coboundary.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCyclesAddEquiv_toCycles (X Y : CochainComplex A ℤ) (m n : ℤ)
    (β : Cochain X Y m) :
    (globalLinearHomCyclesAddEquiv B X Y n ((globalLinearHom B X Y).toCycles m n β) :
      Cochain X Y n) = δ m n β := by
  rw [globalLinearHomCyclesAddEquiv_coe]
  exact congrArg (fun f ↦ f.hom β) ((globalLinearHom B X Y).toCycles_i m n)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- Pre/postcomposition of cycles corresponds to pre/postcomposition of cocycles.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCyclesAddEquiv_cyclesMap {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) (z : (globalLinearHom B X Y).cycles n) :
    globalLinearHomCyclesAddEquiv B X' Y' n
        (HomologicalComplex.cyclesMap (globalLinearHomMap B a b) n z) =
      ((globalLinearHomCyclesAddEquiv B X Y n z).postcomp b).precomp a := by
  ext1
  rw [globalLinearHomCyclesAddEquiv_coe]
  have h := congrArg (fun f ↦ f.hom z)
    (HomologicalComplex.cyclesMap_i (globalLinearHomMap B a b) n)
  refine h.trans ?_
  simp only [Cocycle.precomp_coe, Cocycle.postcomp_coe, globalLinearHomCyclesAddEquiv_coe]
  rfl

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- From cohomology classes of cocycles to the homology of the linear Hom complex.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalLinearHomClassToHomology (X Y : CochainComplex A ℤ) (n : ℤ) :
    CohomologyClass X Y n →+ (globalLinearHom B X Y).homology n :=
  CohomologyClass.descAddMonoidHom
    (((globalLinearHom B X Y).homologyπ n).hom.toAddMonoidHom.comp
      (globalLinearHomCyclesAddEquiv B X Y n).symm.toAddMonoidHom) (by
    intro x hx
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x (n - 1) (by omega)).mp hx
    have : (globalLinearHomCyclesAddEquiv B X Y n).symm x =
        (globalLinearHom B X Y).toCycles (n - 1) n β := by
      apply (globalLinearHomCyclesAddEquiv B X Y n).injective
      rw [AddEquiv.apply_symm_apply]
      ext1
      rw [globalLinearHomCyclesAddEquiv_toCycles, hβ]
    change ((globalLinearHom B X Y).homologyπ n).hom
      ((globalLinearHomCyclesAddEquiv B X Y n).symm x) = 0
    rw [this]
    exact congrArg (fun f ↦ f.hom β)
      ((globalLinearHom B X Y).toCycles_comp_homologyπ (n - 1) n))

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The class of a cocycle is sent to the homology class of the corresponding cycle.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomClassToHomology_mk (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    globalLinearHomClassToHomology B X Y n
        (CohomologyClass.mk (globalLinearHomCyclesAddEquiv B X Y n z)) =
      (globalLinearHom B X Y).homologyπ n z := by
  simp [globalLinearHomClassToHomology]

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)] in
/-- The homology of the linear Hom complex is the group of cohomology classes.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomClassToHomology_bijective (X Y : CochainComplex A ℤ) (n : ℤ) :
    Function.Bijective (globalLinearHomClassToHomology B X Y n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := c.mk_surjective
    obtain ⟨z, rfl⟩ := (globalLinearHomCyclesAddEquiv B X Y n).surjective x
    rw [globalLinearHomClassToHomology_mk] at hc
    have hS : (ShortComplex.mk ((globalLinearHom B X Y).toCycles (n - 1) n)
        ((globalLinearHom B X Y).homologyπ n) (by simp)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _
        ((globalLinearHom B X Y).homologyIsCokernel (n - 1) n (by simp))
    obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS z hc
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    change Cochain X Y (n - 1) at β
    refine ⟨β, ?_⟩
    have h := globalLinearHomCyclesAddEquiv_toCycles B X Y (n - 1) n β
    refine h.symm.trans ?_
    exact congrArg (fun w ↦ (globalLinearHomCyclesAddEquiv B X Y n w : Cochain X Y n)) hβ
  · intro y
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((globalLinearHom B X Y).homologyπ n)).mp
      inferInstance y
    exact ⟨_, globalLinearHomClassToHomology_mk B X Y n z⟩


omit [HasDerivedCategory.{w} A] in
/-- Degree-`n` cohomology of the localized linear Hom complex is the group of cohomology
classes of degree-`n` cocycles.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalLinearHomCohomologyClassEquiv (X Y : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
        (DerivedCategory.Q.obj (globalLinearHom B X Y)) ≃+ CohomologyClass X Y n :=
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (DerivedCategory.Q.obj (globalLinearHom B X Y)) ≃+ (globalLinearHom B X Y).homology n :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).app
      (globalLinearHom B X Y)).toLinearEquiv.toAddEquiv
  e.trans (AddEquiv.ofBijective _ (globalLinearHomClassToHomology_bijective B X Y n)).symm

omit [HasDerivedCategory.{w} A] in
/-- The actual class of a cycle corresponds to the cohomology class of its cocycle.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomCohomologyClassEquiv_class (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    globalLinearHomCohomologyClassEquiv B X Y n (globalLinearHomClass B X Y n z) =
      CohomologyClass.mk (globalLinearHomCyclesAddEquiv B X Y n z) := by
  rw [globalLinearHomCohomologyClassEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  rw [show ∀ c, (AddEquiv.ofBijective _ (globalLinearHomClassToHomology_bijective B X Y n)) c =
    globalLinearHomClassToHomology B X Y n c from fun _ ↦ rfl]
  rw [globalLinearHomClassToHomology_mk]
  exact congrArg (fun f ↦ f.hom ((globalLinearHom B X Y).homologyπ n z))
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).app
      (globalLinearHom B X Y)).inv_hom_id

omit [HasDerivedCategory.{w} A] in
/-- Every degree-`n` cohomology class of the localized linear Hom complex is an actual class.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomClass_surjective (X Y : CochainComplex A ℤ) (n : ℤ) :
    Function.Surjective (globalLinearHomClass B X Y n) := by
  intro w
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((globalLinearHom B X Y).homologyπ n)).mp
    inferInstance (((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).app
      (globalLinearHom B X Y)).hom w)
  refine ⟨z, ?_⟩
  rw [globalLinearHomClass, hz]
  exact congrArg (fun f ↦ f.hom w)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).app
      (globalLinearHom B X Y)).hom_inv_id

omit [HasDerivedCategory.{w} A] in
/-- The actual class is natural for pre/postcomposition maps.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalLinearHomClass_naturality {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) (z : (globalLinearHom B X Y).cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
        (DerivedCategory.Q.map (globalLinearHomMap B a b)) (globalLinearHomClass B X Y n z) =
      globalLinearHomClass B X' Y' n
        (HomologicalComplex.cyclesMap (globalLinearHomMap B a b) n z) := by
  have h := congrArg (fun f ↦ f.hom ((globalLinearHom B X Y).homologyπ n z))
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).inv.naturality
      (globalLinearHomMap B a b))
  have h' := congrArg (fun f ↦ f.hom z)
    (HomologicalComplex.homologyπ_naturality (globalLinearHomMap B a b) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h h'
  refine h.symm.trans ?_
  exact congrArg (fun y ↦ ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).inv.app
    (globalLinearHom B X' Y')).hom y) h'

/-- Conjugation by isomorphisms, as an additive equivalence of Hom groups.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalHomIsoHomCongrAddEquiv {C : Type*} [Category* C] [Preadditive C] {X X' Y Y' : C}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { e₁.homCongr e₂ with map_add' := fun f g ↦ by simp [Iso.homCongr_apply] }


/-- Cohomology classes between resolutions are derived-category maps between the resolved
objects: maps into the K-injective `S.I⟦n⟧` in the homotopy category are maps in `D(A)`.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalHomResolutionClassAddEquiv {X Y : CochainComplex A ℤ} (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ) :
    CohomologyClass R.I S.I n ≃+ (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧) :=
  (CohomologyClass.homAddEquiv (K := R.I) (L := S.I) (n := n)).trans
    ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective _ (S.I⟦n⟧))).trans
      (globalHomIsoHomCongrAddEquiv
        ((DerivedCategory.quotientCompQhIso A).app R.I ≪≫
          (asIso (DerivedCategory.Q.map R.ι)).symm)
        ((DerivedCategory.quotientCompQhIso A).app (S.I⟦n⟧) ≪≫
          (DerivedCategory.Q.commShiftIso n).app S.I ≪≫
          (shiftFunctor (DerivedCategory A) n).mapIso (asIso (DerivedCategory.Q.map S.ι)).symm)))

/-- Formula for `globalHomResolutionClassAddEquiv`.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHomResolutionClassAddEquiv_apply {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (c : CohomologyClass R.I S.I n) :
    globalHomResolutionClassAddEquiv R S n c =
      DerivedCategory.Q.map R.ι ≫ (DerivedCategory.quotientCompQhIso A).inv.app R.I ≫
        DerivedCategory.Qh.map (CohomologyClass.toHom c) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app (S.I⟦n⟧) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I ≫
        (shiftFunctor (DerivedCategory A) n).map (inv (DerivedCategory.Q.map S.ι)) := by
  simp [globalHomResolutionClassAddEquiv, globalHomIsoHomCongrAddEquiv, Iso.homCongr_apply]

/-- The derived-category map attached to the class of a cocycle, after the shifted `Q.map S.ι`.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHomResolutionClassAddEquiv_mk {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ) (f : Cocycle R.I S.I n) :
    globalHomResolutionClassAddEquiv R S n (CohomologyClass.mk f) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I := by
  rw [globalHomResolutionClassAddEquiv_apply, CohomologyClass.toHom_mk]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.inv_hom_id_app_assoc]
  simp

/-- Two cocycles with the same cohomology class give the same derived-category map.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHom_Q_map_equivHomShift_eq {K L : CochainComplex A ℤ} {n : ℤ}
    (f g : Cocycle K L n) (h : CohomologyClass.mk f = CohomologyClass.mk g) :
    DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm g) := by
  have h' := congrArg CohomologyClass.toHom h
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk] at h'
  exact DerivedCategory.Q_map_eq_of_homotopy (C := A) (HomotopyCategory.homotopyOfEq _ _ h')

/-- The cohomology of resolved Hom, as derived-category maps `Q X ⟶ (Q Y)⟦n⟧`.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
def globalHomResolutionCohomology {X Y : CochainComplex A ℤ} (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧) :=
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      CohomologyClass R.I S.I n := globalLinearHomCohomologyClassEquiv B R.I S.I n
  e.trans (globalHomResolutionClassAddEquiv R S n)

/-- The cohomology of resolved Hom on the actual class of a cycle.
Source: Stacks 0B6E, 09L9 (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHomResolutionCohomology_class {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B R.I S.I).cycles n) :
    globalHomResolutionCohomology B R S n (globalLinearHomClass B R.I S.I n z) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫
        DerivedCategory.Q.map
          (Cocycle.equivHomShift.symm (globalLinearHomCyclesAddEquiv B R.I S.I n z)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I := by
  have h := globalHomResolutionClassAddEquiv_mk R S n (globalLinearHomCyclesAddEquiv B R.I S.I n z)
  rw [← globalLinearHomCohomologyClassEquiv_class] at h
  exact h

/-- The unit roof (for every `c` satisfying the roof equation and every `unit` given by the
scalar formula) and the cohomology interpretation of resolved Hom.
Source: Stacks 070I, 0B6E and steps 10-11 of lem-sf-global-hom-resolution-roof.
Proof: by the scalar formula `p (unit X) = R.ι = j (unit R.I)` on the generator, so the roof
equation and cancellation of the invertible `Q.map j` give `unit_roof`. Cohomology of
`H(R.I,S.I)` is maps `R.I → S.I⟦n⟧` modulo homotopy
(`CochainComplex.HomComplex.CohomologyClass.toHom_bijective`), and maps into the K-injective
`S.I⟦n⟧` in the homotopy category are maps in `D(A)` (`IsKInjective.Qh_map_bijective`);
conjugating by `Q.map R.ι` and `Q.map S.ι` defines `cohomology` and gives
`cohomology_resolved`. The roof equation on a cocycle `f : X → Y⟦n⟧` gives `cohomology_roof`;
naturality follows on representatives from the homotopy squares of the lifts.
(blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHom_resolution_roof_cohomology_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (unit : ∀ (X : CochainComplex A ℤ),
      (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
        globalLinearHom B X X) :
    Nonempty (GlobalHomResolutionRoofCohomologyFields B c unit) := by
  refine ⟨{ unit_roof := ?_
            cohomology := fun X Y R S n ↦ globalHomResolutionCohomology B R S n
            cohomology_resolved := ?_
            cohomology_roof := ?_
            cohomology_naturality := ?_ }⟩
  · intro hc hunit X R
    have := roof_precomp_quasiIso B R.ι (J := R.I)
    apply (cancel_mono (DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 R.I)))).mp
    rw [Category.assoc, hc, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    rw [← cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of B B)).inv]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    refine (congrArg (fun x ↦ ((globalLinearHomMap B (𝟙 X) R.ι).f 0).hom x)
      (hunit X b)).trans (Eq.trans ?_ (congrArg (fun x ↦
        ((globalLinearHomMap B R.ι (𝟙 R.I)).f 0).hom x) (hunit R.I b)).symm)
    change (Cochain.ofHom (𝟙 X)).comp ((b • Cochain.ofHom (𝟙 X)).comp (Cochain.ofHom R.ι)
        (add_zero 0)) (zero_add 0) =
      (Cochain.ofHom R.ι).comp ((b • Cochain.ofHom (𝟙 R.I)).comp (Cochain.ofHom (𝟙 R.I))
        (add_zero 0)) (zero_add 0)
    simp
  · intro X Y R S n z f hf
    have hz : globalLinearHomCyclesAddEquiv B R.I S.I n z = f := by
      ext1
      rw [globalLinearHomCyclesAddEquiv_coe, hf]
    have h := globalHomResolutionCohomology_class B R S n z
    rw [hz] at h
    exact h
  · intro hc X Y R S n z f hf
    dsimp only
    have hzf : globalLinearHomCyclesAddEquiv B X Y n z = f := by
      ext1
      rw [globalLinearHomCyclesAddEquiv_coe, hf]
    obtain ⟨z₀, hz₀⟩ := globalLinearHomClass_surjective B R.I S.I n
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map (c X Y R S)
        (globalLinearHomClass B X Y n z))
    have key := congrArg (fun φ ↦ ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map φ).hom
      (globalLinearHomClass B X Y n z)) (hc X Y R S)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at key
    have key₂ := (globalLinearHomClass_naturality B R.ι (𝟙 S.I) n z₀).symm.trans
      (Eq.trans (congrArg (fun x ↦ ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
        (DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)))).hom x) hz₀)
        (key.trans (globalLinearHomClass_naturality B (𝟙 X) S.ι n z)))
    have key' := congrArg (globalLinearHomCohomologyClassEquiv B X S.I n) key₂
    rw [globalLinearHomCohomologyClassEquiv_class, globalLinearHomCohomologyClassEquiv_class,
      globalLinearHomCyclesAddEquiv_cyclesMap, globalLinearHomCyclesAddEquiv_cyclesMap,
      hzf] at key'
    have hQ := globalHom_Q_map_equivHomShift_eq _ _ key'
    rw [Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_precomp,
      Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_postcomp] at hQ
    simp only [Functor.map_id, Category.comp_id, Category.id_comp, Functor.map_comp] at hQ
    rw [← hz₀]
    apply (cancel_mono ((shiftFunctor (DerivedCategory A) n).map
      (DerivedCategory.Q.map S.ι))).mp
    refine (globalHomResolutionCohomology_class B R S n z₀).trans ?_
    rw [← Category.assoc, hQ, Category.assoc, Category.assoc,
      Functor.commShiftIso_hom_naturality]
  · intro X X' Y Y' R R' S S' a b a' b' ha hb n w
    dsimp only
    obtain ⟨z₀, rfl⟩ := globalLinearHomClass_surjective B R.I S.I n w
    rw [globalLinearHomClass_naturality]
    apply (cancel_mono ((shiftFunctor (DerivedCategory A) n).map
      (DerivedCategory.Q.map S'.ι))).mp
    rw [globalHomResolutionCohomology_class, globalLinearHomCyclesAddEquiv_cyclesMap,
      Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp]
    have hb' : (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S'.ι) =
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) ≫
          (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b') := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
        DerivedCategory.Q_map_eq_of_homotopy (C := A) hb.some]
    have ha' : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map R.ι =
        DerivedCategory.Q.map R'.ι ≫ DerivedCategory.Q.map a' := by
      rw [← Functor.map_comp, ← Functor.map_comp,
        DerivedCategory.Q_map_eq_of_homotopy (C := A) ha.some]
    rw [Category.assoc, Category.assoc, hb', ← Category.assoc
      (globalHomResolutionCohomology B R S n _), globalHomResolutionCohomology_class]
    simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
    rw [← Category.assoc (DerivedCategory.Q.map a), ha', Category.assoc]

/-- The complete canonical resolution-roof assertion, with all maps specified on cochains.
The only data in the assertion are maps constrained by the displayed formulas; no
arbitrary comparison, tensor or resolution functor is an input.
Source: Stacks 09L9, 070I, 0B6E and 06XY; the resolution-roof extension in the node.
(blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolutionRoof where
  /-- Precomposition by every resolution is a quasi-isomorphism into any K-injective. -/
  precomp_quasiIso : ∀ (X J : CochainComplex A ℤ) (R : GlobalHomResolution X),
    J.IsKInjective → QuasiIso (globalLinearHomMap B R.ι (𝟙 J))
  /-- The ordinary-to-resolved map, for every individual pair of resolutions. -/
  c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S
  /-- The roof equation uniquely specifies `c`, since its right leg is invertible. -/
  roof : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)
  /-- Derived arrows of chain maps admit the required lifts, unique up to homotopy. -/
  lifts : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (a : X ⟶ Y),
    ∃ a' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a') (a ≫ S.ι)) ∧
      ∀ a'' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a'') (a ≫ S.ι)) →
        Nonempty (Homotopy a' a'')
  /-- Joint naturality, for any representatives of the lifted chain maps. -/
  naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫ c X' Y' R' S' =
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B a' b')
  /-- Chain homotopies do not change either ordinary or resolved localized Hom arrows. -/
  homotopy_invariance : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (a a' : X' ⟶ X) (b b' : Y ⟶ Y'),
    Nonempty (Homotopy a a') → Nonempty (Homotopy b b') →
    DerivedCategory.Q.map (globalLinearHomMap B a b) =
      DerivedCategory.Q.map (globalLinearHomMap B a' b')
  /-- The canonical comparison between any two pairs of resolutions. -/
  comparison : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y),
    globalResolvedHom B R S ≅ globalResolvedHom B R' S'
  /-- Identity derived arrows are represented by homotopy equivalences of resolutions. -/
  comparison_lifts : ∀ (X : CochainComplex A ℤ) (R R' : GlobalHomResolution X),
    ∃ a : HomotopyEquiv R.I R'.I, Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι)
  /-- Every such representative gives the same conjugation comparison. -/
  comparison_formula : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I),
    Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) →
    Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι) →
    (comparison X Y R R' S S').hom =
      DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)
  /-- The comparison carries the old roof to the new roof. -/
  comparison_roof : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y),
    c X Y R S ≫ (comparison X Y R R' S S').hom = c X Y R' S'
  /-- Identity normalization for resolution comparisons. -/
  comparison_refl : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    (comparison X Y R R S S).hom = 𝟙 _
  /-- The cocycle law for three choices. -/
  comparison_cocycle : ∀ (X Y : CochainComplex A ℤ)
    (R R' R'' : GlobalHomResolution X) (S S' S'' : GlobalHomResolution Y),
    (comparison X Y R R' S S').hom ≫ (comparison X Y R' R'' S' S'').hom =
      (comparison X Y R R'' S S'').hom
  /-- Identity resolutions give the identity roof. -/
  normalization : ∀ (X Y : CochainComplex A ℤ) [X.IsKInjective] [Y.IsKInjective],
    c X Y (GlobalHomResolution.self X) (GlobalHomResolution.self Y) = 𝟙 _
  /-- The signed target-shift isomorphism of ordinary Hom complexes. -/
  targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
    globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧
  /-- The shift map is the actual family identification in every integer degree. -/
  targetShift_formula : ∀ (X Y : CochainComplex A ℤ) (n s : ℤ)
    (f : Cochain X (Y⟦n⟧) s),
    ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
      ((targetShift X Y n).hom.f s f) = f.rightUnshift (s + n) rfl
  /-- Shifted augmentations commute with the roof; arbitrary choices use comparison_roof. -/
  targetShift_roof : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ),
    c X (Y⟦n⟧) R (S.shift n) ≫ DerivedCategory.Q.map (targetShift R.I S.I n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B R.I S.I) =
      DerivedCategory.Q.map (targetShift X Y n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B X Y) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{v} B)) n).map (c X Y R S)
  /-- Ordinary composition out of the actual direct-sum total tensor complex. -/
  comp : ∀ (X Y Z : CochainComplex A ℤ),
    globalLinearHom B Y Z ⊗ globalLinearHom B X Y ⟶ globalLinearHom B X Z
  /-- On every homogeneous pure tensor composition is exactly `g ∘ f`. -/
  comp_formula : ∀ (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n)
    (g : Cochain Y Z r) (f : Cochain X Y s),
    (comp X Y Z).f n
        (HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y)
          r s n h (g ⊗ₜ[B] f)) = f.comp g (by omega)
  /-- Localized ordinary composition, preceded by the canonical derived-to-ordinary
  comparison, is compatible with every roof. This is the stated equation for `m`. -/
  composition_roof : ∀ (X Y Z : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (T : GlobalHomResolution Z),
    (c Y Z S T ⊗ₘ c X Y R S) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
          (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y Z)
        (globalLinearHom B X Y) ≫ DerivedCategory.Q.map (comp X Y Z) ≫ c X Z R T
  /-- The composition descends through all canonical resolution comparisons. -/
  composition_comparison : ∀ (X Y Z : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (T T' : GlobalHomResolution Z),
    ((comparison Y Z S S' T T').hom ⊗ₘ (comparison X Y R R' S S').hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S'.I T'.I)
          (globalLinearHom B R'.I S'.I) ≫ DerivedCategory.Q.map (comp R'.I S'.I T'.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
        (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) ≫
        (comparison X Z R R' T T').hom
  /-- The identity cochain as an actual map from `B[0]`. -/
  unit : ∀ (X : CochainComplex A ℤ),
    (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
      globalLinearHom B X X
  /-- It sends a scalar to that scalar times the identity cochain. -/
  unit_formula : ∀ (X : CochainComplex A ℤ) (b : B),
    (unit X).f 0
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B B)).inv b) =
      b • Cochain.ofHom (𝟙 X)
  /-- The roof preserves the identity. -/
  unit_roof : ∀ (X : CochainComplex A ℤ) (R : GlobalHomResolution X),
    DerivedCategory.Q.map (unit X) ≫ c X X R R = DerivedCategory.Q.map (unit R.I)
  /-- The natural cohomology/derived-arrow interpretation, with the specified source and target. -/
  cohomology : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧)
  /-- Its value on a resolved cocycle is conjugation by the two augmentations. -/
  cohomology_resolved : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B R.I S.I).cycles n) (f : Cocycle R.I S.I n),
    (f : Cochain R.I S.I n) = (globalLinearHom B R.I S.I).iCycles n z →
    cohomology X Y R S n (globalLinearHomClass B R.I S.I n z) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I
  /-- On every ordinary cocycle, the map on cohomology is exactly `Q f`. -/
  cohomology_roof : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) (f : Cocycle X Y n),
    (f : Cochain X Y n) = (globalLinearHom B X Y).iCycles n z →
    cohomology X Y R S n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map (c X Y R S)
          (globalLinearHomClass B X Y n z)) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y
  /-- Naturality in both variables of the cohomology interpretation. -/
  cohomology_naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    ∀ (n : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (globalResolvedHom B R S)),
    cohomology X' Y' R' S' n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
          (DerivedCategory.Q.map (globalLinearHomMap B a' b')) z) =
      DerivedCategory.Q.map a ≫ cohomology X Y R S n z ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b)

/-- Canonical ordinary-to-resolved global Hom roof, including composition and cohomology.
Source: Stacks 09L9, 070I, 0B6E and 06XY; agent-formulated resolution-roof extension.
(blueprint: lem-sf-global-hom-resolution-roof).

Proof (the node's eleven steps):
1. The product cochains are B-modules. Expand the differential: its square is zero,
   and `d(gf) = d(g)f + (-1)^|g| g d(f)`. Composition therefore defines a map from
   the direct-sum total tensor, without any boundedness requirement.
2. By lem-sc-hom-cocycle-homotopy-quotient-formulas, Hom cohomology is maps to shifts
   modulo homotopy. Shifts preserve K-injectivity. Apply lem-weil-pbc-kinjective-hom-derived
   to conclude that precomposition by a quasi-isomorphism into a K-injective target
   is an isomorphism on every cohomology group, hence a quasi-isomorphism.
3. A homotopy `h` of target maps gives the Hom homotopy `f ↦ hf`; for source maps
   use `f ↦ (-1)^|f| fh`. Thus localized Hom arrows depend only on homotopy classes.
4. Define the roof by inverting its precomposition leg. The K-injective Hom bijection
   lifts derived arrows to chain maps uniquely up to homotopy, with augmentation squares.
5. For either variable, postcompose both naturality expressions with the invertible
   precomposition leg. The augmentation homotopies reduce both to the same map; cancel.
6. Lift identity derived arrows between two resolutions to homotopy equivalences.
   Conjugation on Hom is independent of representatives, preserves the roof, and
   satisfies the cocycle law by uniqueness of the lifted homotopy classes. Identities
   give the identity roof when both original complexes are K-injective.
7. The family identity gives `H(X,Y[n]) ≅ H(X,Y)[n]`: both differentials are
   `(-1)^n d_Y f - (-1)^s f d_X`. Shift the augmentation and use the preceding comparison.
8. Use prose-03-02 for the canonical lax localization map;
   the module Grothendieck and functorial-flat-resolution inputs are supplied by
   lem-weil-pbc-ring-modules-grothendieck-abelian and
   lem-sfb-abelian-functorial-flat-resolution. Define resolved composition by ordinary
   composition after this comparison.
9. For R=H(I,I), M=H(X,I), O=H(X,X), the three mixed-composition identities are
   `j comp_R = A(1 ⊗ j)`, `A(1 ⊗ p) = B(j ⊗ 1)`, `B(p ⊗ 1) = p comp_O`.
   Apply localization and naturality of the tensor comparison, substitute `j c = p`
   twice, and cancel the invertible final j. No tensor of a quasi-isomorphism with
   an arbitrary nonflat complex is inverted.
10. Both sides of the identity assertion map to the augmentation under j. Conjugation
    preserves composition: insert `b_Y a_Y - 1 = dh + hd`, and use the tensor homotopy
    `S(g ⊗ f) = (-1)^|g| a_Z g h f b_X`. Ordinary associativity and units and lax
    localization coherence give derived associativity and units.
11. Identify resolved Hom cohomology with derived arrows between the resolutions,
    then conjugate by the augmentations. The roof equation sends the class of an
    ordinary cocycle to exactly Qf. All constructions use products of sets only,
    with no flatness, boundedness or scalar-linear choice of resolutions.
In Lean, the roof data above are assembled with the shift, composition and cohomology
field theorems; the K-injective resolution hypothesis is not needed for this. -/
theorem globalHom_resolution_roof
    (_hres : ∀ X : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (uX : X ⟶ I), I.IsKInjective ∧ QuasiIso uX) :
    Nonempty (GlobalHomResolutionRoof.{u, v, w, t} B (A := A)) := by
  obtain ⟨sh⟩ := globalHom_resolution_roof_shift_fields B (roof_c B (A := A))
    (roof_targetShift B (A := A))
  obtain ⟨co⟩ := globalHom_resolution_roof_composition_fields B (roof_c B (A := A))
    (roof_comparison B (A := A))
  obtain ⟨ch⟩ := globalHom_resolution_roof_cohomology_fields B (roof_c B (A := A))
    (roof_unit B (A := A))
  exact ⟨{ precomp_quasiIso := fun _ J R _ ↦ roof_precomp_quasiIso B R.ι (J := J)
           c := roof_c B
           roof := roof_c_roof B
           lifts := roof_lifts
           naturality := roof_naturality B
           homotopy_invariance := fun _ _ _ _ a a' b b' ha hb ↦
             roof_homotopy_invariance B a a' b b' ha hb
           comparison := roof_comparison B
           comparison_lifts := roof_comparison_lifts
           comparison_formula := roof_comparison_formula B
           comparison_roof := roof_comparison_roof B
           comparison_refl := roof_comparison_refl B
           comparison_cocycle := roof_comparison_cocycle B
           normalization := fun X Y _ _ ↦ roof_normalization B X Y
           targetShift := roof_targetShift B
           targetShift_formula := roof_targetShift_formula B
           targetShift_roof := sh.targetShift_roof (roof_c_roof B) (roof_targetShift_formula B)
           comp := co.comp
           comp_formula := co.comp_formula
           composition_roof := co.composition_roof (roof_c_roof B)
           composition_comparison := co.composition_comparison (roof_comparison_formula B)
           unit := roof_unit B
           unit_formula := roof_unit_formula B
           unit_roof := ch.unit_roof (roof_c_roof B) (roof_unit_formula B)
           cohomology := ch.cohomology
           cohomology_resolved := ch.cohomology_resolved
           cohomology_roof := ch.cohomology_roof (roof_c_roof B)
           cohomology_naturality := ch.cohomology_naturality }⟩

end CategoryTheory
