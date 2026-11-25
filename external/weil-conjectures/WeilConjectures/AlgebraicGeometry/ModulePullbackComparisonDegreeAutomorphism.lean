/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # Changing the derived-to-ordinary comparison in any integer degree

Source: Stacks Project, Tags 06YJ and 08HY; the degree-n truncation argument
in Step 4 of `lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- A witnessing tensor-pullback counit at the single complex in degree n.
Source: Stacks Project, Tag 08HY
(blueprint: lem-pc-module-pullback-degree-target-automorphism). -/
def IsModulePullbackComparisonInDegree
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) (n : ℤ)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G) ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback a).obj G)) : Prop :=
  ∃ ε : DerivedCategory.Qh ⋙ derivedPullback a ⟶
      (Scheme.Modules.tensorPullback a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)),
    (derivedPullback a).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      c = cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) n).hom.app G)))

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

/-- Every witnessing left-derived pullback comparison is invertible on degree-n homology.
Source: Stacks Project, Tag 06YJ, and the degree-n tensor calculation in Step 1 of
lem-pc-module-pullback-comparison-target-automorphism.

Proof: Choose a flat resolution of G supported in degrees at most n, augmented to
G[n]. Tensor pullback preserves its support. Its degree-n homology is the cokernel of
the pulled-back differential in degrees n - 1 and n. Right exactness of tensor pullback
identifies this cokernel with a*G. The standard left-derived counit induces precisely
this identification. For any other witnessing counit, uniqueness of the right Kan
extension supplies an invertible natural transformation of the derived pullback whose
composition with the standard counit is the given counit. Evaluating at G[n] and
applying Hn expresses the given map as a composite of isomorphisms. The final
single-complex identification is also an isomorphism. No flatness of G is required;
for the zero module or empty scheme the same cokernel argument applies. -/
private theorem modulePullbackComparison_homology_degree_isIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) (n : ℤ)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsModulePullbackComparisonInDegree a G n c) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).map c) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨ε, hε, rfl⟩ := hc
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F : A ⥤ B := Scheme.Modules.tensorPullback a
  let H := DerivedCategory.homologyFunctor B n
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let K := (CochainComplex.singleFunctor A n).obj G
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
  obtain ⟨I, hI, hImap, _, _, _, _, E, hE, hEmap, hEadd, ε₀, hL, _, hKflat⟩ :=
    (derivedPullback_spec a)
  have he : E = F := CategoryTheory.Functor.ext hE (fun M N f ↦ hEmap f)
  subst E
  have : (derivedPullback a).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hL
  have : (derivedPullback a).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hε
  let e := Functor.leftDerivedUnique (derivedPullback a) (derivedPullback a) ε ε₀
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hfac : e.hom.app (DerivedCategory.Qh.obj (q.obj P)) ≫ ε₀.app (q.obj P) =
      ε.app (q.obj P) := by
    simp [e, Functor.leftDerivedUnique]
  have : IsIso (ε₀.app (q.obj P)) := hKflat P hP
  have : IsIso (ε.app (q.obj P)) := by rw [← hfac]; infer_instance
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesFiniteColimits F := inferInstance
  have : K.IsStrictlyLE n := by dsimp [K]; infer_instance
  have hm := rightExact_homology_degree_isIso F n s
  let η := Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ H) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) H ≪≫
        DerivedCategory.homologyFunctorFactors B n)
  have hmap : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map s)))) :=
    (NatIso.isIso_map_iff η s).2 hm
  have : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have hn := ε.naturality (q.map s)
  have hn' := H.congr_map hn
  simp only [Functor.map_comp, Functor.comp_map] at hn'
  have hcomp : IsIso (H.map ((derivedPullback a).map
      (DerivedCategory.Qh.map (q.map s))) ≫ H.map (ε.app (q.obj K))) := by
    rw [hn']
    infer_instance
  have : IsIso (H.map (ε.app (q.obj K))) :=
    IsIso.of_isIso_comp_left (H.map ((derivedPullback a).map
      (DerivedCategory.Qh.map (q.map s)))) (H.map (ε.app (q.obj K)))
  let j := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app G
  have hj : IsIso (H.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map j.hom))) :=
    inferInstanceAs (IsIso (H.mapIso (DerivedCategory.Qh.mapIso
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso j))).hom)
  change IsIso (H.map (ε.app (q.obj K) ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map j.hom)))
  rw [H.map_comp]
  infer_instance


private theorem modulePullback_single_isLE
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) (G : Y.Modules) (n : ℤ) :
    ((derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G)).IsLE n := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let K := (CochainComplex.singleFunctor A n).obj G
  let B : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, n < i → IsZero (F.X i)
  let K' : B.FullSubcategory := ⟨K, fun i hi ↦ K.isZero_of_isStrictlyLE n i hi⟩
  obtain ⟨R, ε, hR⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology Y) Y.sheaf n
  obtain ⟨hflat, hbound, _, hq⟩ := hR K'
  let P := R.obj K'
  let s : P ⟶ K := ε.app K'
  have : QuasiIso s := hq
  have : IsIso (DerivedCategory.Q.map s) :=
    by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  obtain ⟨F, _, _, hAdd, _, _, e, _⟩ :=
    flatComplexDerivedPullback a P ⟨n, hbound⟩ hflat
  have : F.Additive := hAdd
  have : P.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff P n).2 hbound
  let e' := e ≪≫ (derivedPullback a).mapIso
    ((DerivedCategory.quotientCompQhIso A).app P ≪≫ asIso (DerivedCategory.Q.map s))
  have : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) n :=
    inferInstance
  have hLE : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).IsLE n := inferInstance
  let eF := (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).symm.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).symm.app P)
  exact DerivedCategory.TStructure.t.isLE_of_iso (eF ≪≫ e') n

/-- Two left-derived counits on a single module differ by an automorphism of its
ordinary pullback. There is no cover, direct image or base-change square in this lemma.
Source: Stacks Project, Tags 06YJ and 08HY; Step 4 of the affine alternating model
factorization proof (the truncation argument is written out here).
(blueprint: lem-pc-module-pullback-degree-target-automorphism).

Proof: A bounded-above flat resolution supported in degrees at most n shows that
left-derived pullback of G[n] is in D≤n. Right exactness of tensor pullback identifies
its degree-n homology with the ordinary pullback module. On a K-flat resolution the
counit is invertible, and naturality along the resolution augmentation proves that
its component at G[n] is invertible on Hn. Right Kan extension uniqueness transfers
this fact to every witnessing counit. Maps from a D≤n object to a single module in
degree n are determined by Hn, by t-structure orthogonality. For the two comparisons,
compose the inverse of Hn(c₀) with Hn(c), and transport through the single-module
homology identification to obtain the module automorphism α. Naturality of that
identification gives equality on Hn, and the homology-map bijection gives
c = c₀ followed by α[n]. This includes negative n, zero modules and empty schemes;
no flatness of G is used. -/
theorem modulePullbackComparison_degree_target_automorphism
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) (n : ℤ)
    (c₀ c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc₀ : IsModulePullbackComparisonInDegree a G n c₀)
    (hc : IsModulePullbackComparisonInDegree a G n c) :
    ∃ α : (Scheme.Modules.tensorPullback a).obj G ≅
        (Scheme.Modules.tensorPullback a).obj G,
      c = c₀ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).map α.hom := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := DerivedCategory.singleFunctor C n
  let H := DerivedCategory.homologyFunctor C n
  let M := (Scheme.Modules.tensorPullback a).obj G
  have : IsIso (H.map c₀) := modulePullbackComparison_homology_degree_isIso a G n c₀ hc₀
  have : IsIso (H.map c) := modulePullbackComparison_homology_degree_isIso a G n c hc
  let e : H.obj (S.obj M) ≅ M :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app M
  let α : M ≅ M := e.symm ≪≫ (asIso (H.map c₀)).symm ≪≫ asIso (H.map c) ≪≫ e
  refine ⟨α, ?_⟩
  have : ((derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj G)).IsLE n :=
    modulePullback_single_isLE a G n
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).1
  change H.map c = H.map (c₀ ≫ S.map α.hom)
  rw [H.map_comp]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.naturality
    α.hom
  change H.map (S.map α.hom) ≫ e.hom = e.hom ≫ α.hom at hn
  apply (cancel_mono e.hom).1
  rw [Category.assoc, hn]
  simp [α, e]


end AlgebraicGeometry
