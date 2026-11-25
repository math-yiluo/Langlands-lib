/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Canonical top cohomology of derived module pullback

Source: Stacks Project, derived.tex, Tag 05TC (dual upper-bound and truncation argument),
cohomology.tex, Tags 06YJ and 0D5S. Naturality and composition are the agent assembly
specified in the DAG (blueprint: lem-weil-pbc-derived-pullback-top-cohomology).

The comparison in degree n is the selected derived counit evaluated at the single
complex in degree n. The pinned counit shift theorem identifies it with c[-n].
The top projection is fixed by its identity action on cohomology, using the existing
bijection on maps from D^{≤n} to D^{≥n}; thus it is the standard truncation projection.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w uA uB vA vB wA wB
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The canonical projection C → H^n(C)[-n], characterized by identity on H^n.
The inverse below is the existing bijection of Hom sets. This construction works in
any abelian category and uses its existing standard truncation interface.
Source: Stacks, derived.tex, Tags 08J5 and 05TC
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedTopTruncationProjection
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (n : ℤ) (C : DerivedCategory A) (hC : C.IsLE n) :
    C ⟶ (DerivedCategory.singleFunctor A n).obj ((DerivedCategory.homologyFunctor A n).obj C) :=
  letI := hC
  (Equiv.ofBijective _
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n)).symm
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).inv.app
        ((DerivedCategory.homologyFunctor A n).obj C))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem topProjection_homology
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (n : ℤ) (C : DerivedCategory A) (hC : C.IsLE n) :
    (DerivedCategory.homologyFunctor A n).map (derivedTopTruncationProjection n C hC) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).inv.app
        ((DerivedCategory.homologyFunctor A n).obj C) := by
  have := hC
  exact (Equiv.ofBijective _
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem topProjection_naturality
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (n : ℤ) (C D : DerivedCategory A) (hC : C.IsLE n) (hD : D.IsLE n)
    (a : C ⟶ D) :
    a ≫ derivedTopTruncationProjection n D hD =
      derivedTopTruncationProjection n C hC ≫ (DerivedCategory.singleFunctor A n).map
        ((DerivedCategory.homologyFunctor A n).map a) := by
  have := hC
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).1
  simp only [Functor.map_comp, topProjection_homology]
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).inv.naturality
    ((DerivedCategory.homologyFunctor A n).map a))

/-- Evaluate a specified derived counit on a single module and apply the canonical
termwise/single identification. This generic construction avoids expanding the concrete
sheafification data when checking each use of the same pinned comparison.
Source: Stacks, cohomology.tex, Tags 06YJ and 08HY
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedSingleComparisonOfCounit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (n : ℤ) (M : A) :
    LF.obj ((DerivedCategory.singleFunctor A n).obj M) ⟶
      (DerivedCategory.singleFunctor B n).obj (F.obj M) :=
  cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor A n).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app M)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem topProjection_factor
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (n : ℤ) (C : DerivedCategory A) (hC : C.IsLE n) (M : A)
    (v : C ⟶ (DerivedCategory.singleFunctor A n).obj M) :
    derivedTopTruncationProjection n C hC ≫ (DerivedCategory.singleFunctor A n).map
      ((DerivedCategory.homologyFunctor A n).map v ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).hom.app M) = v := by
  have := hC
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).1
  dsimp only
  rw [Functor.map_comp, topProjection_homology]
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso A n
  change e.inv.app _ ≫ (DerivedCategory.singleFunctor A n ⋙
    DerivedCategory.homologyFunctor A n).map (_ ≫ e.hom.app M) = _
  rw [← e.inv.naturality]
  simp only [Functor.id_obj, Functor.id_map, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem topProjection_map_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (i : ℤ) (K : DerivedCategory A), K.IsLE i → (F.obj K).IsLE i)
    (n : ℤ) (C : DerivedCategory A) (hC : C.IsLE n) :
    IsIso ((DerivedCategory.homologyFunctor B n).map
      (F.map (derivedTopTruncationProjection n C hC))) := by
  have := hC
  let t := DerivedCategory.TStructure.t (C := A)
  let H := DerivedCategory.homologyFunctor A n
  let π := (t.truncGEπ n).app C
  let b := t.descTruncGE (derivedTopTruncationProjection n C hC) n
  have hb : π ≫ b = derivedTopTruncationProjection n C hC := by
    exact t.π_descTruncGE _ n
  have hπ : IsIso (H.map π) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app C n n le_rfl
  have hcomp : IsIso (H.map π ≫ H.map b) := by
    rw [← H.map_comp, hb]
    rw [show H.map (derivedTopTruncationProjection n C hC) = _ from
      topProjection_homology n C hC]
    infer_instance
  have : IsIso (H.map b) := IsIso.of_isIso_comp_left (H.map π) (H.map b)
  have : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    rcases lt_trichotomy i n with hi | rfl | hi
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.isZero_of_isGE _ n i hi).isoZero
        (DerivedCategory.isZero_of_isGE _ n i hi).isoZero
    · assumption
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.isZero_of_isLE _ n i hi).isoZero
        (DerivedCategory.isZero_of_isLE _ n i hi).isoZero
  let T := F.mapTriangle.obj ((t.triangleLTGE n).obj C)
  have hT : T ∈ distTriang _ := F.map_distinguished _ (t.triangleLTGE_distinguished n C)
  have : T.obj₁.IsLE (n - 1) := hF _ _ (t.isLE_truncLT_obj C n _ (by omega))
  have hm : Mono ((DerivedCategory.homologyFunctor B n).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₂_iff
      T hT n).2 ((DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _)
  have he : Epi ((DerivedCategory.homologyFunctor B n).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₂_iff
      T hT n (n + 1) rfl).2
        ((DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _)
  have hπF : IsIso ((DerivedCategory.homologyFunctor B n).map (F.map π)) :=
    isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B n).map T.mor₂)
  rw [← hb, F.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_eq_leftAdjointUniq_inv
    {A B : Type*} [Category A] [Category B]
    {F F' : A ⥤ B} {G G' : B ⥤ A} (a : F ⊣ G) (b : F' ⊣ G') (q : G' ≅ G) :
    ((conjugateIsoEquiv a b).symm q.symm).hom =
      (a.leftAdjointUniq (b.ofNatIsoRight q)).inv := by
  let c := (conjugateIsoEquiv a b).symm q.symm
  have hi : c.inv = (a.leftAdjointUniq (b.ofNatIsoRight q)).hom := by
    apply NatTrans.ext
    funext X
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simpa only [c, conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv,
      Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app] using
      (unit_conjugateEquiv_symm b a q.hom X).symm
  apply (cancel_epi c.inv).1
  rw [Iso.inv_hom_id, hi, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleMap_comp
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (n : ℤ) (M : A) :
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app
        ((CochainComplex.singleFunctor A n).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app M =
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app (F.obj M) ≫
      (CochainComplex.singleFunctor D n).map (c.hom.app M) := by
  apply HomologicalComplex.to_single_hom_ext
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
  simp only [← G.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Functor.comp_map, Category.assoc] using congrArg
    (fun t ↦ t ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) n (H.obj M)).inv)
    (c.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) n M).hom).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleComparison_naturality
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (n : ℤ) {M N : A} (a : M ⟶ N) :
    LF.map ((DerivedCategory.singleFunctor A n).map a) ≫
        derivedSingleComparisonOfCounit F LF ε n N =
      derivedSingleComparisonOfCounit F LF ε n M ≫
        (DerivedCategory.singleFunctor B n).map (F.map a) := by
  unfold derivedSingleComparisonOfCounit
  simp only [cast_eq]
  rw [← Category.assoc]
  have hn := ε.naturality ((HomotopyCategory.singleFunctor A n).map a)
  change LF.map ((DerivedCategory.singleFunctor A n).map a) ≫ _ = _ at hn
  rw [hn]
  simp only [Category.assoc]
  apply congrArg (fun k ↦ ε.app ((HomotopyCategory.singleFunctor A n).obj M) ≫ k)
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map ((CochainComplex.singleFunctor A n).map a))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app N)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app M)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
        ((CochainComplex.singleFunctor B n).map (F.map a)))
  simp only [← Functor.map_comp]
  exact congrArg (fun f ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient B (.up ℤ)).map f))
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.naturality a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem paste
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ D) (Q : B ⥤ D)
    {y : D} {m n o : A} {b₀ b₁ b₂ b₃ b₄ : B}
    (a : L.obj m ⟶ y) (e : y ⟶ Q.obj b₁) (β : m ⟶ n)
    (δ : L.obj n ⟶ Q.obj b₀) (c : b₀ ⟶ b₁)
    (r : b₁ ⟶ b₄) (q : n ⟶ o) (δ' : L.obj o ⟶ Q.obj b₂)
    (t : b₀ ⟶ b₂) (s : b₂ ⟶ b₃) (p : b₃ ⟶ b₄)
    (hfac : a ≫ e = L.map β ≫ δ ≫ Q.map c)
    (ht : c ≫ r = t ≫ s ≫ p)
    (hn : L.map q ≫ δ' = δ ≫ Q.map t) :
    a ≫ (e ≫ Q.map r) = L.map (β ≫ q) ≫ (δ' ≫ Q.map s) ≫ Q.map p := by
  calc
    _ = (a ≫ e) ≫ Q.map r := (Category.assoc _ _ _).symm
    _ = (L.map β ≫ δ ≫ Q.map c) ≫ Q.map r := by rw [hfac]
    _ = L.map β ≫ δ ≫ Q.map (c ≫ r) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = L.map β ≫ δ ≫ Q.map (t ≫ s ≫ p) := by rw [ht]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ L.map β ≫ k ≫ Q.map s ≫ Q.map p) hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem map_to_single_naturality
    {A D : Type*} [Category A] [Category D]
    (H : D ⥤ A) (S : A ⥤ D) (e : S ⋙ H ≅ 𝟭 A)
    {X : D} {M N : A} (v : X ⟶ S.obj M) (a : M ⟶ N) :
    H.map (v ≫ S.map a) ≫ e.hom.app N = H.map v ≫ e.hom.app M ≫ a := by
  rw [H.map_comp, Category.assoc]
  exact congrArg (fun t ↦ H.map v ≫ t) (e.hom.naturality a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem factor_composition
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ D) (S : B ⥤ D)
    {V W : D} {x₀ x₁ x₂ : A} {y z w : B}
    (a : L.obj x₀ ⟶ V) (b : V ⟶ W) (e : W ⟶ S.obj w)
    (v : x₀ ⟶ x₂) (τ : x₀ ⟶ x₁) (q : x₁ ⟶ x₂)
    (δ : L.obj x₂ ⟶ S.obj y) (δ' : L.obj x₁ ⟶ S.obj z)
    (κ : z ⟶ y) (θ : y ⟶ w)
    (hfac : a ≫ b ≫ e = L.map v ≫ δ ≫ S.map θ)
    (hf : τ ≫ q = v) (hn : L.map q ≫ δ = δ' ≫ S.map κ) :
    a ≫ b ≫ e = (L.map τ ≫ δ') ≫ S.map (κ ≫ θ) := by
  rw [hfac, ← hf, L.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (S.map θ), hn]
  simp only [S.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem map_composition_square
    {A D : Type*} [Category A] [Category D]
    (H : D ⥤ A) (S : A ⥤ D) (E : S ⋙ H ≅ 𝟭 A)
    {U V W X : D} {M N : A}
    (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ S.obj N)
    (d : U ⟶ X) (e : X ⟶ S.obj M) (p : M ⟶ N)
    (hv : a ≫ b ≫ c = (d ≫ e) ≫ S.map p) :
    H.map a ≫ (H.map b ≫ H.map c ≫ E.hom.app N) =
      (H.map d ≫ H.map e ≫ E.hom.app M) ≫ p := by
  calc
    _ = H.map (a ≫ b ≫ c) ≫ E.hom.app N := by
      simp only [H.map_comp, Category.assoc]
    _ = H.map ((d ≫ e) ≫ S.map p) ≫ E.hom.app N := by rw [hv]
    _ = _ := by
      rw [map_to_single_naturality H S E]
      simp only [H.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem counit_map_iso
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    (Q : A ⥤ D) (F : A ⥤ B) (L : D ⥤ E) (R : B ⥤ E) (H : E ⥤ C)
    (ε : Q ⋙ L ⟶ F ⋙ R) {P K : A} (s : P ⟶ K)
    [IsIso (Q.map s)] [IsIso (ε.app P)] [IsIso (H.map (R.map (F.map s)))] :
    IsIso (H.map (ε.app K)) := by
  have hn := H.congr_map (ε.naturality s)
  simp only [Functor.map_comp, Functor.comp_map] at hn
  have : IsIso (H.map (L.map (Q.map s)) ≫ H.map (ε.app K)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map (L.map (Q.map s))) (H.map (ε.app K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightExact_homology_degree_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) (n : ℤ) [F.Additive] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} [K.IsStrictlyLE n] [L.IsStrictlyLE n]
    (s : K ⟶ L) [QuasiIso s] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) n) := by
  have hK : (K.sc n).g = 0 := by
    change K.d n ((ComplexShape.up ℤ).next n) = 0
    rw [CochainComplex.next]
    exact (K.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
  have hL : (L.sc n).g = 0 := by
    change L.d n ((ComplexShape.up ℤ).next n) = 0
    rw [CochainComplex.next]
    exact (L.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
  have : F.PreservesLeftHomologyOf (K.sc n) := F.preservesLeftHomology_of_zero_g _ hK
  have : F.PreservesLeftHomologyOf (L.sc n) := F.preservesLeftHomology_of_zero_g _ hL
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map s) F
  have : IsIso (F.map (HomologicalComplex.homologyMap s n)) := inferInstance
  have hcomp : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) n ≫
        ((L.sc n).mapHomologyIso F).hom) := by
    erw [hn]
    change IsIso (((K.sc n).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap s n))
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((L.sc n).mapHomologyIso F).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullbackSectionAdjunction f =
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f) := by
  apply (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f).unique
  · exact (Classical.choose_spec
      (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f)).1
  · intro M U m
    exact Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction f) M
      (Opposite.op U) m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (perfectHomTensorComp f g).hom = (Scheme.Modules.tensorPullbackSectionComp f g).inv := by
  unfold perfectHomTensorComp Scheme.Modules.tensorPullbackSectionComp
  rw [sectionAdjunction_eq, sectionAdjunction_eq, sectionAdjunction_eq]
  exact mate_eq_leftAdjointUniq_inv _ _ _

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The pinned derived-to-tensor-pullback comparison on a single module in degree n.
For n=0 this is the specified counit representative of
`IsDerivedModulePullbackComparison`, normalized by the ordinary pullback unit.
For general n it is the shifted comparison, by pinned counit shift compatibility.
Source: Stacks, cohomology.tex, Tags 06YJ, 08HY and 0D5S
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def pinnedModulePullbackComparisonAt {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (M : S.Modules) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj M) ⟶
    (DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback g).obj M) :=
  letI : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive :=
    fun f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
  derivedSingleComparisonOfCounit
    (A := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (Scheme.Modules.tensorPullback g) (derivedPullback g) (pinnedPullbackCounit.{u, w} g) n M

/-- The specified κ: apply derived pullback to the top projection, apply the pinned
comparison on H^n(C)[-n], take H^n, and use the canonical single-complex cohomology iso.
Source: Stacks, derived.tex, Tag 05TC, dual truncation argument; cohomology.tex, Tag 06YJ
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedPullbackTopCohomology {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj
        ((derivedPullback g).obj C) ⟶
    (Scheme.Modules.tensorPullback g).obj ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C) :=
  (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
      ((derivedPullback g).map (derivedTopTruncationProjection n C hC)) ≫
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
      (pinnedModulePullbackComparisonAt g n ((DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).hom.app _

private instance moduleAbelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pinnedCounit_homology_isIso {X Y : Scheme.{u}} (a : X ⟶ Y)
    (n : ℤ) (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [K.IsStrictlyLE n] :
    let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a
    IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).map
        ((perfectHomTensorCounit a).app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F : A ⥤ B := Scheme.Modules.tensorPullback a
  let H := DerivedCategory.homologyFunctor.{w, u, u + 1} B n
  let q := HomotopyCategory.quotient A (.up ℤ)
  let ε : DerivedCategory.Qh.{w} (C := A) ⋙ derivedPullback a ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w} (C := B) :=
    perfectHomTensorCounit a
  change IsIso (H.map (ε.app (q.obj K)))
  let Pbound : ObjectProperty (CochainComplex A ℤ) :=
    fun P ↦ ∀ i : ℤ, n < i → IsZero (P.X i)
  let K' : Pbound.FullSubcategory := ⟨K, fun i hi ↦ K.isZero_of_isStrictlyLE n i hi⟩
  obtain ⟨R, π, hR⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology Y) Y.sheaf n
  obtain ⟨hflat, hbound, _, hs⟩ := hR K'
  let P := R.obj K'
  let s : P ⟶ K := π.app K'
  have : QuasiIso s := hs
  have : P.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff P n).2 hbound
  have hP := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    Y.toRingedSpace P ⟨n, hbound⟩ hflat
  have hε : IsIso (ε.app (q.obj P)) :=
    perfectHomTensorCounit_isIso a P hP
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesFiniteColimits F := inferInstance
  have hm := rightExact_homology_degree_isIso F n s
  let η := Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
      (DerivedCategory.Qh ⋙ H) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) H ≪≫
        DerivedCategory.homologyFunctorFactors B n)
  have hmap : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map s)))) :=
    (NatIso.isIso_map_iff η s).2 hm
  have : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  exact counit_map_iso DerivedCategory.Qh (F.mapHomotopyCategory (.up ℤ))
    (derivedPullback a) DerivedCategory.Qh H ε (q.map s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleComparison_homology_isIso {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (M : S.Modules) :
    IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
        (pinnedModulePullbackComparisonAt g n M)) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let H := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n
  have hc : IsIso (H.map ((perfectHomTensorCounit g).app
      ((HomotopyCategory.singleFunctor _ n).obj M))) :=
    pinnedCounit_homology_isIso g n ((CochainComplex.singleFunctor _ n).obj M)
  let j := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback g) (.up ℤ) n).app M
  have hj : IsIso (H.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map j.hom))) :=
    inferInstanceAs (IsIso (H.mapIso (DerivedCategory.Qh.mapIso
      ((HomotopyCategory.quotient _ (.up ℤ)).mapIso j))).hom)
  simp only [pinnedModulePullbackComparisonAt, derivedSingleComparisonOfCounit, cast_eq]
  change IsIso (H.map ((perfectHomTensorCounit g).app
      ((HomotopyCategory.singleFunctor _ n).obj M) ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map j.hom)))
  rw [H.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_isLE {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    ((derivedPullback g).obj C).IsLE n := by
  have := hC
  obtain ⟨K, hK, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE C n
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, n < i → IsZero (F.X i)
  let K' : B.FullSubcategory := ⟨K, fun i hi ↦ K.isZero_of_isStrictlyLE n i hi⟩
  obtain ⟨R, π, hR⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology S) S.sheaf n
  obtain ⟨hflat, hbound, _, hs⟩ := hR K'
  let P := R.obj K'
  let s : P ⟶ K := π.app K'
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have : P.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff P n).2 hbound
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let F := Scheme.Modules.tensorPullback g
  have hP := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    S.toRingedSpace P ⟨n, hbound⟩ hflat
  have hε := perfectHomTensorCounit_isIso g P hP
  let eP := asIso ((perfectHomTensorCounit g).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  let eF := (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))).symm.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).symm.app P)
  have : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).IsLE n := inferInstance
  let e := eF ≪≫ eP.symm ≪≫
    (derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso A).app P ≪≫
      asIso (DerivedCategory.Q.map s) ≪≫ eK.symm)
  exact DerivedCategory.TStructure.t.isLE_of_iso e n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTop_isIso {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    IsIso (derivedPullbackTopCohomology g n C hC) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨sL, hL⟩, _⟩ := derivedPullback_spec g
  let : (derivedPullback g).CommShift ℤ := sL
  let : (derivedPullback g).IsTriangulated := hL
  have hτ := topProjection_map_isIso (derivedPullback g) (pullback_isLE g) n C hC
  have hc := singleComparison_homology_isIso g n
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C)
  dsimp only [derivedPullbackTopCohomology]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTop_naturality {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C D : schemeDerivedCategory S) (hC : C.IsLE n) (hD : D.IsLE n)
    (a : C ⟶ D) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map ((derivedPullback g).map a) ≫
        derivedPullbackTopCohomology g n D hD =
      derivedPullbackTopCohomology g n C hC ≫ (Scheme.Modules.tensorPullback g).map
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).map a) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n
  have hc := singleComparison_naturality
    (A := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings T.toRingedSpace)) (Scheme.Modules.tensorPullback g)
    (derivedPullback g) (perfectHomTensorCounit g) n (HS.map a)
  change (derivedPullback g).map
      ((DerivedCategory.singleFunctor.{w, u, u + 1} _ n).map (HS.map a)) ≫
    pinnedModulePullbackComparisonAt g n (HS.obj D) =
    pinnedModulePullbackComparisonAt g n (HS.obj C) ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1} _ n).map ((Scheme.Modules.tensorPullback g).map
        (HS.map a)) at hc
  have ht := topProjection_naturality n C D hC hD a
  have hv : (derivedPullback g).map a ≫
      (derivedPullback g).map (derivedTopTruncationProjection n D hD) ≫
      pinnedModulePullbackComparisonAt g n (HS.obj D) =
    (derivedPullback g).map (derivedTopTruncationProjection n C hC) ≫
      pinnedModulePullbackComparisonAt g n (HS.obj C) ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1} _ n).map ((Scheme.Modules.tensorPullback g).map
        (HS.map a)) := by
    rw [← Functor.map_comp_assoc, ht, Functor.map_comp, Category.assoc, hc]
  have he := E.hom.naturality ((Scheme.Modules.tensorPullback g).map (HS.map a))
  change HT.map _ ≫ E.hom.app _ = E.hom.app _ ≫ _ at he
  dsimp only [derivedPullbackTopCohomology]
  change HT.map _ ≫ HT.map _ ≫ HT.map _ ≫ E.hom.app _ =
    (HT.map _ ≫ HT.map _ ≫ E.hom.app _) ≫ _
  have hh := congrArg (fun f ↦ HT.map f ≫ E.hom.app _) hv
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [he] at hh
  dsimp only [Functor.id_obj, Functor.id_map] at hh
  simpa only [HS, Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleComparison_composition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) (M : Z.Modules) :
    (@pinnedPullbackComposition.{u, w} _
        (fun {_ _} k ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} k)
        _ _ _ f g).hom.app ((DerivedCategory.singleFunctor.{w, u, u + 1} _ n).obj M) ≫
      pinnedModulePullbackComparisonAt (f ≫ g) n M =
    (derivedPullback f).map (pinnedModulePullbackComparisonAt g n M) ≫
      pinnedModulePullbackComparisonAt f n ((Scheme.Modules.tensorPullback g).obj M) ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1} _ n).map
        ((Scheme.Modules.tensorPullbackSectionComp f g).inv.app M) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} (f ≫ g)
  let F : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Scheme.Modules.tensorPullback g
  let G : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback f
  let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback (f ≫ g)
  let qX := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let qY := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  let K := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) n).obj M
  let jg := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app M
  let jf := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app (F.obj M)
  let jfg := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app M
  have ht := congrArg (fun k ↦ qX.map k)
    (singleMap_comp F G H (perfectHomTensorComp f g) n M)
  simp only [Functor.map_comp] at ht
  change qX.map ((perfectHomTensorComplexComp f g).hom.app
      ((CochainComplex.singleFunctor _ n).obj M)) ≫ qX.map jfg =
    (perfectHomTensorHomotopy f).map (qY.map jg) ≫ qX.map jf ≫
      (HomotopyCategory.singleFunctor _ n).map ((perfectHomTensorComp f g).hom.app M) at ht
  have hn := (perfectHomTensorCounit f).naturality (qY.map jg)
  change (derivedPullback f).map (DerivedCategory.Qh.map (qY.map jg)) ≫
      (perfectHomTensorCounit f).app ((HomotopyCategory.singleFunctor _ n).obj (F.obj M)) =
    (perfectHomTensorCounit f).app ((perfectHomTensorHomotopy g).obj K) ≫
      DerivedCategory.Qh.map ((perfectHomTensorHomotopy f).map (qY.map jg)) at hn
  have hfac := perfectHomTensorCounit_comp f g K
  have h := paste (derivedPullback f) DerivedCategory.Qh _ _ _ _ _ _ _ _ _ _ _
    hfac ht hn
  change _ ≫ (_ ≫ DerivedCategory.Qh.map (qX.map jfg)) =
    (derivedPullback f).map (_ ≫ DerivedCategory.Qh.map (qY.map jg)) ≫
      (_ ≫ DerivedCategory.Qh.map (qX.map jf)) ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).map
        ((perfectHomTensorComp f g).hom.app M) at h
  dsimp only [K, F, G, H, qX, qY, jf, jg, jfg] at h
  simpa only [pinnedModulePullbackComparisonAt, derivedSingleComparisonOfCounit,
    cast_eq, ← tensorComp_eq, Category.assoc, perfectHomComposition, pinnedPullbackComposition,
    perfectHomTensorCounit, pinnedPullbackCounit, DerivedCategory.singleFunctor,
    DerivedCategory.singleFunctors, HomotopyCategory.singleFunctor,
    HomotopyCategory.singleFunctors, CochainComplex.singleFunctor,
    SingleFunctors.postcomp, Functor.comp_obj, DerivedCategory.Qh,
    HomologicalComplexUpToQuasiIso.Qh, HomotopyCategory.quotient,
    Quotient.lift_obj_functor_obj, Quotient.lift_map_functor_map, DerivedCategory.Q] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pinnedComparison_naturality {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) {M N : S.Modules} (a : M ⟶ N) :
    (derivedPullback g).map ((DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).map a) ≫
      pinnedModulePullbackComparisonAt g n N =
    pinnedModulePullbackComparisonAt g n M ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
          ((Scheme.Modules.tensorPullback g).map a) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  exact singleComparison_naturality
    (A := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (Scheme.Modules.tensorPullback g) (derivedPullback g) (perfectHomTensorCounit g) n a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTop_factor {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n)
    (hbound : ((derivedPullback g).obj C).IsLE n) :
    derivedTopTruncationProjection n ((derivedPullback g).obj C) hbound ≫
      (DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
          (derivedPullbackTopCohomology g n C hC) =
    (derivedPullback g).map (derivedTopTruncationProjection n C hC) ≫
      pinnedModulePullbackComparisonAt g n
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  simpa only [derivedPullbackTopCohomology, Functor.map_comp, Category.assoc] using
    topProjection_factor n ((derivedPullback g).obj C) hbound _
      ((derivedPullback g).map (derivedTopTruncationProjection n C hC) ≫
        pinnedModulePullbackComparisonAt g n
          ((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTop_composition {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n)
    (hbound : ((derivedPullback g).obj C).IsLE n) (T' : Scheme.{u}) (h : T' ⟶ T) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n).map
        ((@pinnedPullbackComposition.{u, w} _
          (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
          _ _ _ h g).hom.app C) ≫
      derivedPullbackTopCohomology (h ≫ g) n C hC =
    derivedPullbackTopCohomology h n ((derivedPullback g).obj C) hbound ≫
      (Scheme.Modules.tensorPullback h).map (derivedPullbackTopCohomology g n C hC) ≫
      (Scheme.Modules.tensorPullbackSectionComp h g).inv.app
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} h
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n
  let HX := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n
  let SX := DerivedCategory.singleFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n
  let γ := @pinnedPullbackComposition.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ _ h g
  let θ := (Scheme.Modules.tensorPullbackSectionComp h g).inv.app (HS.obj C)
  let k := derivedPullbackTopCohomology g n C hC
  let τ := derivedTopTruncationProjection n C hC
  have hc := singleComparison_composition h g n (HS.obj C)
  have hn := γ.hom.naturality τ
  change (derivedPullback h).map ((derivedPullback g).map τ) ≫ _ =
    γ.hom.app C ≫ (derivedPullback (h ≫ g)).map τ at hn
  have hv : γ.hom.app C ≫ (derivedPullback (h ≫ g)).map τ ≫
      pinnedModulePullbackComparisonAt (h ≫ g) n (HS.obj C) =
    (derivedPullback h).map ((derivedPullback g).map τ ≫
      pinnedModulePullbackComparisonAt g n (HS.obj C)) ≫
      pinnedModulePullbackComparisonAt h n ((Scheme.Modules.tensorPullback g).obj (HS.obj C)) ≫
      SX.map θ := by
    rw [← Category.assoc, ← hn, Category.assoc, hc, Functor.map_comp, Category.assoc]
  have hf := pullbackTop_factor g n C hC hbound
  have hnat := pinnedComparison_naturality h n k
  have hv' := factor_composition (derivedPullback h) SX
    (γ.hom.app C) ((derivedPullback (h ≫ g)).map τ)
    (pinnedModulePullbackComparisonAt (h ≫ g) n (HS.obj C)) _ _ _ _ _
    ((Scheme.Modules.tensorPullback h).map k) θ hv hf hnat
  have hh := map_composition_square HX SX E _ _ _ _ _ _ hv'
  change HX.map (γ.hom.app C) ≫
      (HX.map ((derivedPullback (h ≫ g)).map τ) ≫
        HX.map (pinnedModulePullbackComparisonAt (h ≫ g) n (HS.obj C)) ≫ E.hom.app _) =
    (HX.map ((derivedPullback h).map
        (derivedTopTruncationProjection n ((derivedPullback g).obj C) hbound)) ≫
      HX.map (pinnedModulePullbackComparisonAt h n _) ≫ E.hom.app _) ≫
        (Scheme.Modules.tensorPullback h).map k ≫ θ
  simpa only [Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived pullback preserves the upper bound; H^0 of its normalized module comparison
and the specified top comparison are isomorphisms. The top comparison is natural for
all derived morphisms between upper-bounded objects and respects composition.
The existential `hbound` records the first conclusion and supplies its proof to κ_h.
Source: Stacks, derived.tex, Tags 05TC and 08J5, dual upper-bound/truncation argument;
cohomology.tex, Tags 06YJ and 0D5S. Naturality and composition are the DAG assembly
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology).

Proof:
1. Represent C by a complex K zero above n using the standard t-structure. Apply
lem-pc-kflat-bounded-flat-replacement at the same bound n. Its flat replacement P is
K-flat by lem-pc-bounded-above-flat-kflat, so lemma-coherent-base-change-invertible-sheaves--2
computes Lg*C by termwise g*P, with the counit selected by derived pullback composition.
2. The ordinary tensor pullback is left adjoint to pushforward
(lem-pc-module-pullback-adjunction), hence preserves cokernels. Its comparison
coker(g*d^{n-1}) → g*coker(d^{n-1}) is the map induced by the quotient of g*P^n.
3. The pulled-back complex is zero above n; its top cohomology is that cokernel.
Thus Lg*C has the asserted upper bound, without a lower bound.
4. Resolve M[0] with the same upper bound zero. Naturality of the fixed derived
counit at the resolution map identifies H^0(c_g,M) with the invertible cokernel
comparison followed by g* of the resolution's H^0 isomorphism. This verifies the
particular comparison of def-pc-derived-module-base-change-map.
5. On P the top projection has degree-n component P^n → H^n(P). Counit naturality
at this map and lem-pc-pinned-pullback-counit-shifts identify κ with the cokernel
isomorphism of step 3. Transport along Q(P) ≅ C gives the stated κ.
6. Smart truncation is functorial and preserves quasi-isomorphisms; it descends to
all derived morphisms. Its projection and the selected counit are natural, giving
the displayed naturality equation. On a single module in degree n, κ is H^0(c).
7. Apply lem-pc-canonical-single-pullback-composition to h,g,M. The explicit pinned
construction of lem-pc-canonical-single-pullback-comparison and the transpose formula
lem-pc-canonical-single-adjunction-transpose identify its single comparisons with c.
Transport the ordinary comparisons back through the unique adjunction-preserving
tensor-to-ordinary identifications. This gives the same equation with tensor pullback
and tensorPullbackSectionComp.inv. Shift it using the two pinned shift lemmas.
8. Apply step 6 for h to v = Lg*(τ_C) followed by c_g,H^n(C)[-n]. Its H^n is κ_g,C.
The target is the single g*H^n(C) in degree n, so its κ_h is H^0(c_h). Postcompose
with ordinary tensor composition; substitute step 7 and use naturality of derived
composition at τ_C. This gives exactly the displayed composition equation.
No inverse of c in the derived category is used. -/
theorem derivedPullback_topCohomology {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    ∃ hbound : ((derivedPullback g).obj C).IsLE n,
      (∀ M : S.Modules,
        IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
            (pinnedModulePullbackComparisonAt g 0 M))) ∧
      IsIso (derivedPullbackTopCohomology g n C hC) ∧
      (∀ (D : schemeDerivedCategory S) (hD : D.IsLE n) (a : C ⟶ D),
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map ((derivedPullback g).map a) ≫
            derivedPullbackTopCohomology g n D hD =
          derivedPullbackTopCohomology g n C hC ≫
            (Scheme.Modules.tensorPullback g).map ((DerivedCategory.homologyFunctor.{w, u, u + 1}
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).map a)) ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n).map
            ((@pinnedPullbackComposition.{u, w} _
              (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
              _ _ _ h g).hom.app C) ≫
            derivedPullbackTopCohomology (h ≫ g) n C hC =
          derivedPullbackTopCohomology h n ((derivedPullback g).obj C) hbound ≫
            (Scheme.Modules.tensorPullback h).map (derivedPullbackTopCohomology g n C hC) ≫
            (Scheme.Modules.tensorPullbackSectionComp h g).inv.app
              ((DerivedCategory.homologyFunctor.{w, u, u + 1}
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C)) := by
  refine ⟨pullback_isLE g n C hC, singleComparison_homology_isIso g 0,
    pullbackTop_isIso g n C hC, ?_, ?_⟩
  · intro D hD a
    exact pullbackTop_naturality g n C D hC hD a
  · intro T' h
    exact pullbackTop_composition g n C hC (pullback_isLE g n C hC) T' h

end AlgebraicGeometry
