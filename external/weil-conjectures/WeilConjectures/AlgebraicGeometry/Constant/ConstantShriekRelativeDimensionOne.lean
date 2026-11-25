/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportBaseChangeQcqs
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesPreimageConstructible
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesGenericDiagram
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesFiniteModule
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Constructible compact support for constant finite coefficients on affine smooth curves

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, specialized to
finite commutative coefficients and affine bases of finite type over the integers.
(blueprint: lem-weil-pbc-etale-constant-shriek-rel-dim-1)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Compactly supported cohomology of a finite constant module commutes with arbitrary base
change of a qcqs base: the inverse image along `g` of the `q`-th cohomology sheaf of the lower
shriek is isomorphic to the `q`-th cohomology sheaf of the lower shriek of the base change.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
theorem nonempty_constantShriekBaseChangeIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S T : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : T ⟶ S) (M : ModuleCat.{u + 1} Λ) (c : Compactification f) (q : ℤ) :
    Nonempty ((upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) ≅
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.baseChange g)).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf (Limits.pullback f g).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  obtain ⟨bc⟩ := etale_compactSupport_baseChange_qcqs Λ f g c
  let gs := upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f g)
  let e := (gs.mapDerivedCategoryPlusSingleFunctor 0).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≪≫
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ)
        (Limits.pullback.fst f g)).app M)
  let gt := upperStar (ModuleCat.{u + 1} Λ) g
  exact ⟨(gt.mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (bc.app K ≪≫
        (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.baseChange g)).mapIso e)⟩

private theorem constructible_of_empty
    {S : Scheme.{u}} [IsEmpty S] {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Scheme.IsConstructibleSheaf F := by
  exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty F)

/-- Noetherian induction for constructibility: a sheaf on a Noetherian scheme is constructible
if its restriction to every nonempty closed subscheme is constructible on some nonempty open.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
theorem constructible_of_closed_nonempty_generic
    {S : Scheme.{u}} [IsNoetherian S] {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ (Z : Scheme.{u}) (i : Z ⟶ S) [IsClosedImmersion i] [Nonempty Z],
      ∃ U : Z.Opens, Nonempty U ∧ Scheme.IsConstructibleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((upperStar (ModuleCat.{u + 1} Λ) i).obj F))) :
    Scheme.IsConstructibleSheaf F := by
  classical
  suffices H : ∀ C : TopologicalSpace.Closeds S, ∀ (Z : Scheme.{u}) (i : Z ⟶ S)
      [IsClosedImmersion i], Set.range i = C →
        Scheme.IsConstructibleSheaf ((upperStar (ModuleCat.{u + 1} Λ) i).obj F) by
    have : Scheme.IsConstructibleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) (𝟙 S)).obj F) := H ⊤ S (𝟙 S) (by simp)
    exact Scheme.IsConstructibleSheaf.of_iso ((upperStarId (ModuleCat.{u + 1} Λ) S).app F)
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    intro Z i _ hi
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := {}
    by_cases hZ : IsEmpty Z
    · exact constructible_of_empty _
    have : Nonempty Z := not_isEmpty_iff.mp hZ
    obtain ⟨U, hU, hFU⟩ := hF Z i
    have : Nonempty U := hU
    let C' : TopologicalSpace.Closeds S :=
      ⟨Set.range (U.closedComplement ≫ i),
        (U.closedComplement ≫ i).isClosedEmbedding.isClosed_range⟩
    have hlt : C' < C := by
      refine lt_of_le_of_ne ?_ fun heq ↦ ?_
      · rintro _ ⟨z, rfl⟩
        rw [← SetLike.mem_coe, ← hi]
        exact Set.mem_range_self _
      · obtain ⟨z⟩ := hU
        have hz : i z.1 ∈ (C' : Set S) := by
          rw [heq, ← hi]
          exact Set.mem_range_self _
        obtain ⟨w, hw⟩ := hz
        have hw' : U.closedComplement w = z.1 := i.isEmbedding.injective hw
        have hwc : U.closedComplement w ∉ (U : Set Z) := by
          have := Set.mem_range_self (f := U.closedComplement) w
          simpa only [Scheme.Opens.range_closedComplement, Set.mem_compl_iff] using this
        exact hwc (hw'.symm ▸ z.2)
    have : Scheme.IsConstructibleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) (U.closedComplement ≫ i)).obj F) :=
      ih C' hlt _ (U.closedComplement ≫ i) rfl
    have hFC : Scheme.IsConstructibleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) U.closedComplement).obj
          ((upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
      Scheme.IsConstructibleSheaf.of_iso
        ((upperStarComp (ModuleCat.{u + 1} Λ) U.closedComplement i).app F)
    exact (Scheme.isConstructibleSheaf_iff_upperStar U.ι U.closedComplement
      (by rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]) _).mpr ⟨hFU, hFC⟩

private theorem dense_open_complement_dimension_zero
    {B : Type*} [TopologicalSpace B] [TopologicalSpace.NoetherianSpace B]
    [QuasiSober B] [T0Space B] {O : Set B} (hO : IsOpen O) (hdense : Dense O)
    (hdim : topologicalKrullDim B ≤ 1) : topologicalKrullDim (Oᶜ : Set B) ≤ 0 := by
  have hlt : topologicalKrullDim (Oᶜ : Set B) < (1 : WithBot ℕ∞) := by
    apply topologicalKrullDim_lt_of_forall_exists_specializes
      (Z := Set.univ) isClosed_univ hO.isClosed_compl (Set.subset_univ Oᶜ)
    · intro w _
      let C := irreducibleComponent w
      have hC := irreducibleComponent_mem_irreducibleComponents w
      have hη := hC.1.isGenericPoint_genericPoint (isClosed_irreducibleComponent (x := w))
      refine ⟨hC.1.genericPoint, Set.mem_univ _, hη.specializes mem_irreducibleComponent, ?_⟩
      intro hbad
      have hCO : C ⊆ Oᶜ := by
        dsimp only [C]
        rw [← hη.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hbad) hO.isClosed_compl
      obtain ⟨U, hU, hUne, hUC⟩ :=
        TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
      obtain ⟨z, hzU, hzO⟩ := hdense.inter_open_nonempty U hU hUne
      exact hCO (hUC hzU) hzO
    · exact (topologicalKrullDim_subspace_le B Set.univ).trans hdim |>.trans_lt (by decide)
  exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hlt)

/-- The closed complement of a fibrewise dense open of a smooth separated affine relative curve
over a Noetherian base is quasi-finite over the base.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
theorem denseOpenCurve_complement_quasiFinite
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (W : X.Opens) (hW : ∀ s : S, Dense (f.fiberι s ⁻¹' (W : Set X))) :
    (W.closedComplement ≫ f).IsQuasiFinite := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : LocallyOfFiniteType (W.closedComplement ≫ f) := inferInstance
  have : QuasiCompact (W.closedComplement ≫ f) := inferInstance
  refine ⟨inferInstance, inferInstance, fun z ↦ ?_⟩
  let i := W.closedComplement
  let g := i ≫ f
  let s := g z
  let j : g.fiber s ⟶ f.fiber s := Limits.pullback.map
    g (S.fromSpecResidueField s) f (S.fromSpecResidueField s)
    i (𝟙 _) (𝟙 _) (by simp [g]) (by simp)
  have hsq : IsPullback j (g.fiberι s) (f.fiberι s) i := by
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
    · simpa [j, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, g] using
        (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).flip
    · simp [j, Scheme.Hom.fiberι]
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hrange : Set.range j = (f.fiberι s ⁻¹' (W : Set X))ᶜ := by
    dsimp only [j, Scheme.Hom.fiber]
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Hom.fiberι, i]
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have : IsNoetherian (f.fiber s) := {}
  have hdim : topologicalKrullDim (g.fiber s) ≤ 0 := by
    rw [j.isEmbedding.topologicalKrullDim_eq_range, hrange]
    exact dense_open_complement_dimension_zero
      (W.isOpen.preimage (f.fiberι s).continuous) (hW s)
      (topologicalKrullDim_le_of_smoothOfRelativeDimension (f.fiberToSpecResidueField s) 1)
  have : IsLocallyNoetherian (g.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField s)
  have : IsLocallyArtinian (g.fiber s) := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact isOpen_discrete _

private noncomputable def constantSinglePullbackIso
    {X S : Scheme.{u}} (f : X ⟶ S) {Λ : Type (u + 1)} [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusSingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).app M)

/-- Open-closed gluing for compactly supported cohomology of a constant sheaf: if the
cohomology sheaves for an open `U` and its closed complement are constructible, so are those
for the whole scheme.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
theorem constantShriek_openClosed
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U : X.Opens) [QuasiCompact U.ι]
    (M : ModuleCat.{u + 1} Λ) (c : Compactification f)
    (cU : Compactification (U.ι ≫ f)) (cZ : Compactification (U.closedComplement ≫ f))
    (hU : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))
    (hZ : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))))) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT, _⟩ :=
    exists_compactSupport_openClosed_triangle Λ f U.ι U.closedComplement
      (by rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]) K c cU cZ
  let P := _root_.DerivedCategory.homologyProperty
    (constructibleSheaf (ModuleCat.{u + 1} Λ) S)
  have h₁ : P T.obj₁ := P.prop_of_iso
    (e₁ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).mapIso
        (constantSinglePullbackIso U.ι M))).symm hU
  have h₃ : P T.obj₃ := P.prop_of_iso
    (e₃ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cZ).mapIso
        (constantSinglePullbackIso U.closedComplement M))).symm hZ
  exact P.prop_of_iso e₂ (P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃)

private theorem constantShriek_closedCover
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (M : ModuleCat.{u + 1} Λ) (c : Compactification f)
    (ci : Compactification (i ≫ f))
    (hi : ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ci).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let O : X.Opens := ⊥
  let cO := HasCompactification.compactification (O.ι ≫ f)
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  have hij : Set.range i.base = (Set.range O.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι, show (O : Set X) = ∅ from rfl, Set.compl_empty]
    exact i.surjective.range_eq
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT, _⟩ :=
    exists_compactSupport_openClosed_triangle Λ f O.ι i hij K c cO ci
  let P := _root_.DerivedCategory.homologyProperty
    (constructibleSheaf (ModuleCat.{u + 1} Λ) S)
  have h₁ : P T.obj₁ := by
    have : IsEmpty O.toScheme := ⟨fun x ↦ x.2⟩
    have hzero : Limits.IsZero
        (((upperStar (ModuleCat.{u + 1} Λ) O.ι).mapDerivedCategoryPlus).obj K) := by
      apply Limits.IsZero.of_iso _ (constantSinglePullbackIso O.ι M)
      exact Functor.map_isZero _ (Scheme.Etale.isZero_sheaf_of_isEmpty _)
    have hz := Functor.map_isZero
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cO) hzero
    have hz' := Functor.map_isZero _root_.DerivedCategory.Plus.ι hz
    have hzT := hz'.of_iso e₁
    intro q
    exact Scheme.IsConstructibleSheaf.of_isZero
      (Functor.map_isZero (_root_.DerivedCategory.homologyFunctor _ q) hzT)
  have h₃ : P T.obj₃ := P.prop_of_iso
    (e₃ ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ci).mapIso
        (constantSinglePullbackIso i M))).symm hi
  exact P.prop_of_iso e₂ (P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃)

private theorem properSmooth_finiteEtale_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {C T V : Scheme.{u}} [IsNoetherian V]
    (p : C ⟶ T) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (t : T ⟶ V) [IsFinite t] [AlgebraicGeometry.Etale t]
    (hdim : ∀ s : T, topologicalKrullDim (p.fiber s) ≤ 1)
    (hΛ : ∀ (a : Λ) (s : T), IsUnit (addOrderOf a : T.presheaf.stalk s))
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
      (properSmoothCurves_finiteModule_higherDirectImage_constructible p hdim Λ hΛ M q)
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (e.app K).symm)
  have hqf : t.IsQuasiFinite := ⟨inferInstance, inferInstance, fun x ↦ isOpen_discrete _⟩
  have h := constructibleCohomology_lowerShriek_of_quasiFinite Λ t hqf
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp).obj K) hK ct
  obtain ⟨ec⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ p t cp ct c
  intro q
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cp) ⋙
          (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ct)).obj K)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (h q)
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (ec.app K))

/-- Given a good-curves diagram over a Noetherian base whose proper smooth models have
constructible compactly supported cohomology, the compactly supported cohomology of the
constant sheaf on the dense open `W` is constructible.
Source: Stacks Project, Tag 0GKX, proof of `lemma-constant-shriek-rel-dim-1`. -/
theorem goodCurvesOpen_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
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
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    (hthick : IsThickening (Limits.pullback.snd ν W.ι))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hmodels : ∀ (i : Fin n) (ci : Compactification (p i ≫ t i)) (q : ℤ),
      Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ci).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf (Ybar i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))
    (cW : Compactification (W.ι ≫ f)) :
    ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf W.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
  have : IsNoetherian W.toScheme := {}
  have : IsClosedImmersion (Limits.pullback.snd ν W.ι) := hthick.1
  have : Surjective (Limits.pullback.snd ν W.ι) := hthick.2
  let ci := HasCompactification.compactification
    (Limits.pullback.snd ν W.ι ≫ W.ι ≫ f)
  apply constantShriek_closedCover Λ (W.ι ≫ f) (Limits.pullback.snd ν W.ι) M cW ci
  exact goodCurvesPreimage_constantShriek_constructible Λ f n T Y Ybar t j p ν
    hcomm ht hj hjp hp W hWi M hmodels ci

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
    (hΛ : ∀ (a : Λ) (v : V), IsUnit (addOrderOf a : V.presheaf.stalk v))
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
      (fun s ↦ ((hp i).2.2 s).2)
      (fun a s ↦ by simpa using (hΛ a (t i s)).map ((t i).stalkMap s).hom) M ci q
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

private theorem generic_constantShriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [IsNoetherian S] [IsAffine S] [Nonempty S]
    (f : X ⟶ S) [IsSeparated f] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (hΛ : ∀ (a : Λ) (s : S), IsUnit (addOrderOf a : S.presheaf.stalk s))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (c : Compactification f) :
    ∃ U : S.Opens, Nonempty U ∧ ∀ q : ℤ, Scheme.IsConstructibleSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))  := by
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
    n T Y Ybar t j p ν hcomm ht hj hjp hp W hW hWi hthick
    (fun a v ↦ by simpa using (hΛ a ((g ≫ U.ι) v)).map ((g ≫ U.ι).stalkMap v).hom)
    M (c.baseChange (g ≫ U.ι)) q
  obtain ⟨ebc⟩ := nonempty_constantShriekBaseChangeIso Λ f (g ≫ U.ι) M c q
  exact Scheme.IsConstructibleSheaf.of_iso
    (ebc.symm ≪≫
      (upperStarComp (ModuleCat.{u + 1} Λ) g U.ι).app F)

/-- Compact support of a finite constant module on an affine smooth relative curve over
an affine base of finite type over the integers, on which the additive orders of the
coefficients are invertible, has constructible cohomology in every degree.

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`.
(blueprint: lem-weil-pbc-etale-constant-shriek-rel-dim-1)

Proof: The base is Noetherian. Induct on closed subsets, allowing every closed subscheme
structure, and use open-closed gluing of constructible sheaves. Compact-support base change,
exact inverse image and constant pullback reduce the induction step to the base-changed
smooth affine curve over the closed base. Choose a generic point of an irreducible component
and a good-curves diagram. Surjective-pullback descent reduces constructibility on a nonempty
open of the base to the finite cover in that diagram.

The original curve's boundary is quasi-finite: its fibre is a closed complement of a dense
open in a Noetherian space of dimension at most one, hence zero-dimensional and discrete.
Quasi-finite shriek constructibility and the open-closed triangle reduce to the dense open.
Its finite closed cover is a thickening. The open-closed triangle for that closed cover has
zero first term, and therefore reduces to the inverse image of the dense open.

For each proper model, use the identity compactification and the proper smooth finite-module
lemma (the coefficient orders stay invertible on every scheme over the base); then compose
with the finite etale map using quasi-finite shriek constructibility.
The remaining good-curves-preimage lemma assembles those models and removes their boundaries.
This proves the generic step. Open-closed gluing completes the induction, including nilpotent
closed subschemes directly. The last comparison converts finite-stalk constructibility to
the finite-constant-value predicate of the statement. -/
theorem constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated h] [IsAffineHom h] [SmoothOfRelativeDimension 1 h]
    (hΛ : ∀ (a : Λ) (s : Spec (CommRingCat.of A)),
      IsUnit (addOrderOf a : (Spec (CommRingCat.of A)).presheaf.stalk s))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (c : Compactification h) [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))  := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : Smooth h := SmoothOfRelativeDimension.smooth 1 h
  have : IsAffine X := isAffine_of_isAffineHom h
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian h
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
  obtain ⟨U, hU, hgen⟩ := generic_constantShriek_constructible Λ f
    (fun a z ↦ by simpa using (hΛ a (i z)).map (i.stalkMap z).hom) M (c.baseChange i)
  refine ⟨U, hU, ?_⟩
  have := hgen q
  obtain ⟨ebc⟩ := nonempty_constantShriekBaseChangeIso Λ h i M c q
  exact Scheme.IsConstructibleSheaf.of_iso
    ((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapIso ebc.symm)

end AlgebraicGeometry.Etale
