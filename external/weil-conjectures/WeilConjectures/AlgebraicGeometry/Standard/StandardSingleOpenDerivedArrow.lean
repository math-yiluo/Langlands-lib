/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
import all WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparisonCompat

/-! # Open restriction of the canonical single-module derived arrow

Source: Stacks Project, Tags 08HY, 0DJ9 and 08FE.
(blueprint: lem-pc-standard-single-open-derived-arrow).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section
private theorem cancelSingleMaps
    {A C : Type*} [Category A] [Category C] (F : A ⥤ C)
    {X Y : C} {U V : A} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
    (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

private theorem changeCoefficient
    {C : Type*} [Category C] {X Y X0 Y0 X1 Y1 : C}
    (m : X ⟶ Y) (n : X0 ⟶ Y0) (n' : X1 ⟶ Y1)
    (s : X ≅ X0) (t : Y ≅ Y0) (es : X0 ≅ X1) (et : Y0 ≅ Y1)
    (h : m ≫ t.hom = s.hom ≫ n) (hn : es.hom ≫ n' = n ≫ et.hom) :
    m ≫ (t ≪≫ et).hom = (s ≪≫ es).hom ≫ n' := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, h, Category.assoc, ← hn]

private theorem appendCoefficientNaturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X X' : D} {Y Y' Z Z' : C}
    (a : X ⟶ X') (l : X ⟶ F.obj Y) (r : X' ⟶ F.obj Y')
    (c : Y ⟶ Z) (c' : Y' ⟶ Z') (k : Y ⟶ Y') (t : Z ⟶ Z')
    (h : a ≫ r = l ≫ F.map k) (hc : k ≫ c' = c ≫ t) :
    a ≫ (r ≫ F.map c') = (l ≫ F.map c) ≫ F.map t := by
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp, hc]
  simp only [F.map_comp, Category.assoc]

private theorem pinnedSingle_comp_naturality {D : Type*} [Category D]
    {A₀ A₁ A₂ B₀ B₁ B₂ : D}
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂)
    (p : A₀ ⟶ A₂) (q : B₀ ⟶ B₂)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (hp : p = a₀ ≫ a₁) (hq : q = b₀ ≫ b₁) :
    f₀ ≫ q = p ≫ f₂ := by
  rw [hp, hq, ← Category.assoc, h₀, Category.assoc, h₁, Category.assoc]

section
variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
  (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

-- Naturality compares the derived adjunctions and composition isomorphisms.
private theorem pinnedBaseChange_naturality
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {A B : schemeDerivedCategory X} (a : A ⟶ B) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g g' h B =
      schemeDerivedBaseChangeMap f f' g g' h A ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map a) := by
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f')
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f')
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f'))
  let c₁ := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) f' g)
  let c₂ := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) g' f)
  let d : derivedPullback (f' ≫ g) ≅ derivedPullback (g' ≫ f) :=
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm)
  let t : ∀ K : schemeDerivedCategory X,
      (derivedPullback f').obj ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj K)) ⟶ (derivedPullback g').obj K :=
    fun K ↦ c₁.hom.app ((schemeDerivedDirectImage f).obj K) ≫
      d.hom.app ((schemeDerivedDirectImage f).obj K) ≫
      c₂.inv.app ((schemeDerivedDirectImage f).obj K) ≫
      (derivedPullback g').map (adj.counit.app K)
  have hd (K : schemeDerivedCategory X) :
      d.hom.app ((schemeDerivedDirectImage f).obj K) =
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) := by
    exact eqToHom_app (congrArg (fun k ↦ derivedPullback k) h.symm) _
  have ht : (derivedPullback f').map
        ((derivedPullback g).map ((schemeDerivedDirectImage f).map a)) ≫ t B =
      t A ≫ (derivedPullback g').map a := by
    dsimp only [t]
    rw [← Functor.comp_map, c₁.hom.naturality_assoc,
      d.hom.naturality_assoc, c₂.inv.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp]
    rw [show (derivedPullback f).map ((schemeDerivedDirectImage f).map a) ≫
        adj.counit.app B = adj.counit.app A ≫ a from adj.counit.naturality a]
    simp only [Functor.map_comp, Category.assoc]
  have happ (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (t K) := by
    simp only [t, hd]
    rfl
  rw [happ A, happ B, ← adj'.homEquiv_naturality_left,
    ← adj'.homEquiv_naturality_right, ht]

attribute [local implicit_reducible] HomotopyCategory.singleFunctors
attribute [local irreducible] Scheme.Modules.tensorPullbackObj
  schemeDerivedBaseChangeMap Scheme.picardTermwiseSingleMap
attribute [local implicit_reducible] Scheme.Modules.tensorPullback
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

private theorem pinnedSingle_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    IsDerivedModulePullbackComparison f M (Scheme.picardTermwiseSingleMap f M) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  refine ⟨ε, ?_, ?_⟩
  · exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  · simpa only [cast_eq] using Scheme.single_map_normalize f M

private theorem pinnedSingle_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (k : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map k) ≫
        Scheme.picardTermwiseSingleMap f N =
      Scheme.picardTermwiseSingleMap f M ≫
        (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.tensorPullback f).map k) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let H := HomotopyCategory.quotient X.Modules (.up ℤ)
  let r := HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0
  let HY := HomotopyCategory.singleFunctor Y.Modules 0
  let SY := DerivedCategory.singleFunctor Y.Modules 0
  let SX := DerivedCategory.singleFunctor X.Modules 0
  let T := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)
  have hε := ε.naturality (HY.map k)
  change (derivedPullback f).map (SY.map k) ≫ ε.app (HY.obj N) =
    ε.app (HY.obj M) ≫ DerivedCategory.Qh.map (T.map (HY.map k)) at hε
  have hr := congrArg (fun b ↦ DerivedCategory.Qh.map (H.map b)) (r.hom.naturality k)
  simp only [Functor.map_comp, Functor.comp_map] at hr
  change DerivedCategory.Qh.map (T.map (HY.map k)) ≫
      DerivedCategory.Qh.map (H.map (r.hom.app N)) =
    DerivedCategory.Qh.map (H.map (r.hom.app M)) ≫
      SX.map ((Scheme.Modules.tensorPullback f).map k) at hr
  exact pinnedSingle_comp_naturality
    ((derivedPullback f).map (SY.map k)) (DerivedCategory.Qh.map (T.map (HY.map k)))
    (SX.map ((Scheme.Modules.tensorPullback f).map k))
    (ε.app (HY.obj M)) (DerivedCategory.Qh.map (H.map (r.hom.app M)))
    (ε.app (HY.obj N)) (DerivedCategory.Qh.map (H.map (r.hom.app N)))
    (Scheme.picardTermwiseSingleMap f M) (Scheme.picardTermwiseSingleMap f N)
    hε hr (Scheme.single_map_normalize f M) (Scheme.single_map_normalize f N)

-- The coefficient transports compare dependent derived-category witnesses.
/-- The derived arrow square before taking homology or stalks.

Proof: Apply restricted_base_change_compatibility to the chosen pullback square.
For each coefficient use the pinned homotopy counit at the single complex, followed
by singleMapHomologicalComplex. Expand canonicalSinglePullbackMap and cancel the
single images of the adjunction comparison and its inverse; the resulting map is
picardTermwiseSingleMap. The comparison predicate is witnessed by the pinned
left-derived structure. The theorem gives source and target restriction isomorphisms
and their commuting square with coefficients H = schemeOpenRestriction(Y,p⁻¹S)(M).
Use overFunctorEquiv at p⁻¹S to identify H with the literal restriction MS.
Naturality of the derived mate and of the pinned counit under this coefficient
isomorphism transports both sides of the square to MS. Compose the source comparison
with derivedPullback of derivedDirectImage of the single image of that isomorphism;
compose the target comparison with derivedDirectImage of the single image of its
tensor pullback. Their naturality gives exactly the displayed equation. No homology,
stalk, finiteness, flatness or quasi-coherence condition is involved. Empty opens
and top opens use the same natural isomorphisms.
Source: Stacks Project, Tag 08HY, Remark base-change; Tag 0DJ9, locality paragraph;
Tag 08FE, restriction of derived direct image.
(blueprint: lem-pc-standard-single-open-derived-arrow). -/
theorem standardSingle_open_derived_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B)
    (S : B.Opens) (V : A.Opens) (hVS : V ≤ g ⁻¹ᵁ S) :
    let R := (schemeOpenRestriction A V).mapDerivedCategory
    let pS := p ∣_ S
    let MS := M.restrict (p ⁻¹ᵁ S).ι
    let j := g.resLE S V hVS
    let b := schemeDerivedBaseChangeMap p (pullback.snd p g) g (pullback.fst p g)
      pullback.condition ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (schemeDerivedDirectImage (pullback.snd p g)).map
          (Scheme.picardTermwiseSingleMap (pullback.fst p g) M)
    let bS := schemeDerivedBaseChangeMap pS (pullback.snd pS j) j (pullback.fst pS j)
      pullback.condition ((DerivedCategory.singleFunctor _ 0).obj MS) ≫
        (schemeDerivedDirectImage (pullback.snd pS j)).map
          (Scheme.picardTermwiseSingleMap (pullback.fst pS j) MS)
    ∃ (s : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
        (derivedPullback j).obj ((schemeDerivedDirectImage pS).obj
          ((DerivedCategory.singleFunctor _ 0).obj MS)))
      (t : R.obj ((schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))) ≅
        (schemeDerivedDirectImage (pullback.snd pS j)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst pS j) MS))),
      R.map b ≫ t.hom = s.hom ≫ bS := by
  classical
  let : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive :=
    fun f ↦ Scheme.Modules.canonicalTensorPullbackAdditive f
  intro R pS MS j b bS
  let U := p ⁻¹ᵁ S
  let H : U.toScheme.Modules := (schemeOpenRestriction Y U).obj M
  let e : H ≅ MS := (Scheme.Modules.overFunctorEquiv U).app M
  let P := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0
  let q := pullback.fst pS j
  let r := pullback.snd pS j
  obtain ⟨s, t, h⟩ := restricted_base_change_compatibility p g
    (pullback.fst p g) (pullback.snd p g) (IsPullback.of_hasPullback p g) M
    (Scheme.picardTermwiseSingleMap (pullback.fst p g) M)
    (pinnedSingle_comparison (pullback.fst p g) M) S V hVS
    (Scheme.picardTermwiseSingleMap q H) (pinnedSingle_comparison q H)
  let es := (derivedPullback j).mapIso ((schemeDerivedDirectImage pS).mapIso (P.mapIso e))
  let et := (schemeDerivedDirectImage r).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso ((Scheme.Modules.tensorPullback q).mapIso e))
  let mk (N : U.toScheme.Modules) :=
    schemeDerivedBaseChangeMap pS r j q pullback.condition (P.obj N) ≫
      (schemeDerivedDirectImage r).map (Scheme.picardTermwiseSingleMap q N)
  refine ⟨s ≪≫ es, t ≪≫ et, ?_⟩
  have nat : (derivedPullback j).map ((schemeDerivedDirectImage pS).map (P.map e.hom)) ≫
      bS =
    mk H ≫
      (schemeDerivedDirectImage r).map
        ((DerivedCategory.singleFunctor _ 0).map
          ((Scheme.Modules.tensorPullback q).map e.hom)) := by
    exact appendCoefficientNaturality (schemeDerivedDirectImage r)
      ((derivedPullback j).map ((schemeDerivedDirectImage pS).map (P.map e.hom)))
      (schemeDerivedBaseChangeMap pS r j q pullback.condition (P.obj H))
      (schemeDerivedBaseChangeMap pS r j q pullback.condition (P.obj MS))
      (Scheme.picardTermwiseSingleMap q H) (Scheme.picardTermwiseSingleMap q MS)
      ((derivedPullback q).map (P.map e.hom))
      ((DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.tensorPullback q).map e.hom))
      (pinnedBaseChange_naturality pS r j q pullback.condition (P.map e.hom))
      (pinnedSingle_naturality q e.hom)
  have he : R.map b ≫ t.hom = s.hom ≫ mk H := h
  exact changeCoefficient (R.map b) (mk H) bS
    s t es et he nat

end
end
end AlgebraicGeometry
