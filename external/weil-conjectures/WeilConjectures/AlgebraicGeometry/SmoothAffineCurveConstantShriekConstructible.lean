/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Constant.ConstantShriekRelativeDimensionOne
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportBaseChangeQcqs
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesGenericDiagram
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesPreimageConstructible
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesFiniteModule
import WeilConjectures.AlgebraicGeometry.ProperSmoothCurvesFiniteModuleAllChar
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# Constructible compact support for constant finite coefficients on affine smooth curves

Source: Stacks Project, `more-etale.tex`, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`,
lines 4511--4613 (blueprint: lem-fd-smooth-affine-curve-constant-shriek-constructible).

The theorem states constructibility of every cohomology sheaf of the bounded-below derived
lower shriek of a finite constant module on a separated affine smooth relative curve over an
affine Noetherian finite-dimensional base. The proof follows the closed-subset induction,
compact-support base change, good-curves diagram, quasi-finite boundary, proper-smooth models,
open-closed triangles, and descent steps recorded in the DAG node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem properSmooth_finiteEtale_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {C T V : Scheme.{u}} [IsNoetherian V]
    (p : C ⟶ T) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (t : T ⟶ V) [IsFinite t] [AlgebraicGeometry.Etale t]
    (hdim : ∀ s : T, topologicalKrullDim (p.fiber s) ≤ 1)
    (M : ModuleCat.{u + 1} Λ) [Finite M] (c : Compactification (p ≫ t)) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let cp := Compactification.ofIsProper p
  let ct := Compactification.ofIsProper t
  have : QuasiCompact ct.i := ct.quasiCompact_openImmersion inferInstance
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let e : rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp ≅
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso (openImmersionLowerShriekId _ C) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫ Functor.leftUnitor _
  have hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp).obj K)) := by
    intro q
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (properSmoothCurves_finiteModule_higherDirectImage_constructible_all_char
        p hdim Λ M q)
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (e.app K).symm)
  have hqf : t.IsQuasiFinite := ⟨inferInstance, inferInstance, fun x ↦ isOpen_discrete _⟩
  have h := constructibleCohomology_lowerShriek_of_quasiFinite Λ t hqf
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp).obj K) hK ct
  obtain ⟨ec⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ p t cp ct c
  intro q
  have hq : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp) ⋙
          (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ct)).obj K)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (h q)
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (ec.app K))

private theorem goodCurves_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V : Scheme.{u}} [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hW : ∀ v : V, Dense (f.fiberι v ⁻¹' (W : Set X)))
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    (hthick : IsThickening (Limits.pullback.snd ν W.ι))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (c : Compactification f) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))  := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let cW := HasCompactification.compactification (W.ι ≫ f)
  let cZ := HasCompactification.compactification (W.closedComplement ≫ f)
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
  have : QuasiCompact cZ.i := cZ.quasiCompact_openImmersion inferInstance
  have hmodels (i : Fin n) (ci : Compactification (p i ≫ t i)) (q : ℤ) :
      Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ci).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf (Ybar i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
    have : IsFinite (t i) := (ht i).1
    have : AlgebraicGeometry.Etale (t i) := (ht i).2
    have : Smooth (p i) := (hp i).1
    have : IsProper (p i) := (hp i).2.1
    have : GeometricallyConnected (p i) :=
      (GeometricallyConnected.iff_geometricallyConnected_fiber (p i)).mpr
        (fun s ↦ ((hp i).2.2 s).1)
    exact properSmooth_finiteEtale_constantShriek_constructible Λ (p i) (t i)
      (fun s ↦ ((hp i).2.2 s).2) M ci q
  apply constantShriek_openClosed Λ f W M c cW cZ
  · exact goodCurvesOpen_constantShriek_constructible Λ f n T Y Ybar t j p ν
      hcomm ht hj hjp hp W hWi hthick M hmodels cW
  · intro q
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    exact constructibleCohomology_lowerShriek_of_quasiFinite Λ (W.closedComplement ≫ f)
      (denseOpenCurve_complement_quasiFinite f W hW)
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))
      (constantSingle_constructible Λ _ M) cZ q

/-- Generic step: over a nonempty affine Noetherian base, the compactly supported cohomology
of a finite constant module on a separated affine smooth relative curve is constructible on a
nonempty open of the base, in every characteristic.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
private theorem generic_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [IsNoetherian S] [IsAffine S] [Nonempty S]
    (f : X ⟶ S) [IsSeparated f] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (c : Compactification f) :
    ∃ U : S.Opens, Nonempty U ∧ ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let x : S := Classical.choice inferInstance
  let η := isIrreducible_irreducibleComponent (x := x) |>.genericPoint
  have hη : ∃ C ∈ irreducibleComponents S, IsGenericPoint η C :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      isIrreducible_irreducibleComponent.isGenericPoint_genericPoint
        (isClosed_irreducibleComponent (x := x))⟩
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField η) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hdim : topologicalKrullDim (f.fiber η) ≤ 1 :=
    topologicalKrullDim_le_of_smoothOfRelativeDimension (f.fiberToSpecResidueField η) 1
  obtain ⟨U, hU, V, g, hgfin, hgsur, _, n, T, Y, Ybar, t, j, p, ν,
    hνfin, hνsur, hcomm, ht, hj, hjp, hp, W, hW, hWi, hthick⟩ :=
    exists_good_curves_generic_diagram f η hη hdim
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set S))
  have : IsFinite g := hgfin
  have : Surjective g := hgsur
  have : IsFinite ν := hνfin
  have : Surjective ν := hνsur
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g ≫ U.ι)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian V := {}
  refine ⟨U, ⟨⟨η, hU⟩⟩, fun q ↦ ?_⟩
  let F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback g _).mpr
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have : IsAffineHom (Limits.pullback.snd f (g ≫ U.ι)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd f (g ≫ U.ι)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have := goodCurves_constantShriek_constructible Λ (Limits.pullback.snd f (g ≫ U.ι))
    n T Y Ybar t j p ν hcomm ht hj hjp hp W hW hWi hthick M (c.baseChange (g ≫ U.ι)) q
  obtain ⟨ebc⟩ := nonempty_constantShriekBaseChangeIso Λ f (g ≫ U.ι) M c q
  exact Scheme.IsConstructibleSheaf.of_iso
    (ebc.symm ≪≫ (upperStarComp (ModuleCat.{u + 1} Λ) g U.ι).app F)

/-- Compactly supported cohomology of a finite constant module on a separated affine
smooth relative curve over an affine Noetherian finite-dimensional base is constructible
in every characteristic.

Source: Stacks Project, `more-etale.tex`, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`,
lines 4511--4613 (blueprint: lem-fd-smooth-affine-curve-constant-shriek-constructible).

Proof: The base is Noetherian. Induct on closed subsets, allowing every closed subscheme
structure, and use open-closed gluing of constructible sheaves. Compact-support base change,
exact inverse image and constant pullback reduce the induction step to the base-changed
smooth affine curve over the closed base. Choose a generic point of an irreducible component
and a good-curves diagram. Surjective-pullback descent reduces constructibility on a nonempty
open of the base to the finite cover in that diagram.

The curve's boundary is quasi-finite: its fibre is a closed complement of a dense open in a
Noetherian space of dimension at most one, hence zero-dimensional and discrete. Quasi-finite
shriek constructibility and the open-closed triangle reduce to the dense open. Its finite
closed cover is a thickening; the open-closed triangle for that closed cover has zero first
term, and therefore reduces to the inverse image of the dense open.

For each proper model, use the identity compactification and the all-characteristic proper
smooth finite-module lemma; then compose with the finite etale map using quasi-finite shriek
constructibility. The good-curves-preimage lemma assembles those models. This proves the
generic step, and open-closed gluing completes the induction. The last comparison converts
finite-stalk constructibility to the finite-constant-value predicate of the statement. No
invertibility of the characteristic is used, and the finiteness of the Krull dimension of the
base is not needed by this argument.
-/
theorem constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one_all_char
    (ell : ℕ) (A : Type (u + 1)) [Field A] [Finite A] [CharP A ell]
    (S : Scheme.{u}) [IsAffine S] [IsNoetherian S]
    (hSdim : topologicalKrullDim S ≠ ⊤)
    (T : Scheme.{u}) (h : T ⟶ S) [IsSeparated h] [IsAffineHom h]
    [SmoothOfRelativeDimension 1 h]
    (M : ModuleCat.{u + 1} A) [Finite M] (c : Compactification h)
    [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
            ((constantSheaf T.smallEtaleTopology
              (ModuleCat.{u + 1} A)).obj M)))) := by
  have _ := hSdim
  have : Smooth h := SmoothOfRelativeDimension.smooth 1 h
  have : IsAffine T := isAffine_of_isAffineHom h
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  apply constructible_of_closed_nonempty_generic
  intro Z i _ _
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsNoetherian Z := {}
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  let f := Limits.pullback.snd h i
  have : IsAffineHom f := MorphismProperty.pullback_snd _ _ inferInstance
  have : SmoothOfRelativeDimension 1 f :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  obtain ⟨U, hU, hgen⟩ := generic_constantShriek_constructible A f M (c.baseChange i)
  refine ⟨U, hU, ?_⟩
  have hgenq := hgen q
  obtain ⟨ebc⟩ := nonempty_constantShriekBaseChangeIso A h i M c q
  exact Scheme.IsConstructibleSheaf.of_iso
    ((upperStar (ModuleCat.{u + 1} A) U.ι).mapIso ebc.symm)

end AlgebraicGeometry.Etale
