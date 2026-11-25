/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelDescent
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkReduction
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Descended etale stalk data before finite-level local trivialization

Source: Stacks Project, Tag 09C6, the normalized algebraic stalk diagram;
Tags 09AL and 09B1 for finite coefficient descent.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-stalk-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A descended finite quotient diagram and the coefficient transport from its stalk.

The transport is conditional on a supplied etale isomorphism with the stalk complex.
It supplies neither such an isomorphism nor a covering on which one exists. It includes
further restriction along every arrow to a supplied etale chart.
Source: Stacks Tags 09C6, 09AL and 09B1.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-stalk-data). -/
structure FinitePerfectAdicEtaleStalkData (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (E : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))) where
  connected : ConnectedSpace V.left
  point : V.left
  level : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  bounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj (level n))
  lisse : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj (level n))
  transport : ∀ (n : ℕ) (U : V.left.Etale), Nonempty
    ((AlgebraicGeometry.Etale.upperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
        (level n) ≅
      (constantSheaf U.left.smallEtaleTopology
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))).mapDerivedCategory.obj
          ((finitePerfectAdicEtaleStalk V.left _ point).obj (level n))) →
    ∀ (W : X.Etale), (W ⟶ Etale.mk (U.hom ≫ V.hom)) → Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1))).obj (E n))))

/-- Pulling back the model sieve preserves its bounds and its actual quotient models. -/
private theorem finitePerfectAdic_models_pullback
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (a b : ℤ)
    {V W : X.Etale} (g : W ⟶ V)
    (h : FinitePerfectModelsOn X d φ M n V a b) :
    FinitePerfectModelsOn X d φ M n W a b := by
  obtain ⟨T, hT, hlocal⟩ := h
  exact ⟨T.pullback g, X.smallEtaleTopology.pullback_stable g hT,
    fun Z f hf ↦ hlocal Z (f ≫ g) hf⟩

/-- Every point of a locally Noetherian scheme has a connected open neighborhood,
obtained as a component of an affine neighborhood. -/
private theorem finitePerfectAdic_connected_neighborhood
    (Y : Scheme.{t}) [IsLocallyNoetherian Y] (y : Y) :
    ∃ (Z : Scheme.{t}) (f : Z ⟶ Y) (z : Z),
      IsOpenImmersion f ∧ ConnectedSpace Z ∧ f z = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have : IsAffine U.toScheme := hU
  have : IsNoetherian U.toScheme := ⟨⟩
  let u : U.toScheme := ⟨y, hy⟩
  let C : U.toScheme.Opens :=
    ⟨connectedComponent u, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent u⟩
  have hC : ConnectedSpace C.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := u))
  exact ⟨C.toScheme, C.ι ≫ U.ι, ⟨u, mem_connectedComponent⟩,
    inferInstance, hC, rfl⟩

/-- Refine a model sieve by a point-indexed cover of nonempty connected charts.
For an empty X the indexing type, and hence this cover, is empty. -/
private theorem finitePerfectAdic_connected_model_cover
    (X : Scheme.{t}) [IsLocallyNoetherian X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ 𝒱 : Cover.{t} etalePrecoverage X, ∀ i : 𝒱.I₀,
      ConnectedSpace (𝒱.X i) ∧ ∃ (_v : 𝒱.X i) (a b : ℤ), a ≤ b ∧
        ∀ n : ℕ, FinitePerfectModelsOn X d φ M n (𝒱.etalePrecoverageToEtale i) a b := by
  classical
  obtain ⟨S, hS, hlocal⟩ := hmodels
  let e : Etale.mk (𝟙 X) ≅ ⊤_ X.Etale :=
    (Etale.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
  have hSe : S.pullback e.hom ∈ X.smallEtaleTopology (Etale.mk (𝟙 X)) :=
    X.smallEtaleTopology.pullback_stable e.hom hS
  have hx (x : X) : ∃ (W : X.Etale) (w : W.left) (a b : ℤ),
      ConnectedSpace W.left ∧ W.hom w = x ∧ a ≤ b ∧
        ∀ n : ℕ, FinitePerfectModelsOn X d φ M n W a b := by
    obtain ⟨V, g, hg, y, hy⟩ := (mem_smallEtaleTopology_iff _).mp hSe x
    obtain ⟨a, b, hab, hmodel⟩ := hlocal V (g ≫ e.hom) hg
    have : IsLocallyNoetherian V.left :=
      LocallyOfFiniteType.isLocallyNoetherian (Y := X) V.hom
    obtain ⟨Z, f, z, hf, hconn, hz⟩ := finitePerfectAdic_connected_neighborhood V.left y
    have := hf
    let W : X.Etale := Etale.mk (f ≫ V.hom)
    let j : W ⟶ V := MorphismProperty.Over.homMk f rfl
    have hghom : (show V.left ⟶ X from g.left) = V.hom := by
      have hg := MorphismProperty.Over.w g
      change g.left ≫ 𝟙 X = V.hom at hg
      exact (Category.comp_id (show V.left ⟶ X from g.left)).symm.trans hg
    refine ⟨W, z, a, b, hconn, ?_, hab, fun n ↦
      finitePerfectAdic_models_pullback X d φ M n a b j (hmodel n)⟩
    change V.hom (f z) = x
    rw [hz, ← hghom]
    exact hy
  choose W w a b hconn hw hab hmodel using hx
  let 𝒱 : Cover.{t} etalePrecoverage X :=
    Cover.mkOfCovers X (fun x ↦ (W x).left) (fun x ↦ (W x).hom)
      (fun x ↦ ⟨x, w x, hw x⟩) (fun x ↦ (W x).prop)
  exact ⟨𝒱, fun x ↦ ⟨hconn x, w x, a x, b x, hab x, hmodel x⟩⟩

/-- Descend the quotient diagram and extract its algebraic stalk levels and reduction maps.

This conclusion contains no local isomorphisms with constant stalk complexes and no
finite-level marking sieves. Those are obtained separately from finite-ring derived
local constancy on each connected chart.

Source: Stacks Project, Tag 09C6, the paragraph constructing normalized algebraic M_n
before taking their limit, with Tags 09AL, 09B1 and 094G.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-stalk-data).

Proof: refine the model sieve by connected open neighborhoods of points of its charts.
Pullback of covering sieves preserves the uniform bounds. Descend each finite quotient
separately, retaining its bounded lisse etale complex, a small perfect algebraic stalk
model, and transport for any supplied constant-model isomorphism. On a connected chart,
finite-ring derived local constancy gives local constant models for two consecutive
levels. Refine the two covers and select a nonempty chart above the chosen point.
Transport both constant models to the actual quotient objects there. Consecutive
quotient scalar balancing identifies their algebraic models after scalar extension.
This gives the required pairwise isomorphisms without descending quotient arrows or
choosing compatible trivializations. Finally compose any supplied stalk trivialization
with the chosen algebraic stalk comparison and apply single-level transport. The empty
base uses the empty point-indexed cover. No inverse limit is used. -/
theorem finitePerfectAdic_etale_stalk_data
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ 𝒱 : Cover.{t} etalePrecoverage X, ∀ i : 𝒱.I₀,
      ∃ E : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))),
        (∀ n : ℕ, DerivedCategory.IsPerfect (E n)) ∧
        (∀ n : ℕ, Nonempty
          ((ConstantScalarRealization.moduleDerivedExtension
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj (E (n + 1)) ≅ E n)) ∧
        Nonempty (FinitePerfectAdicEtaleStalkData X d φ M
          (𝒱.etalePrecoverageToEtale i) E) := by
  classical
  obtain ⟨𝒱, h𝒱⟩ := finitePerfectAdic_connected_model_cover X d φ M hmodels
  refine ⟨𝒱, fun i ↦ ?_⟩
  obtain ⟨hconn, v, a, b, hab, hmodel⟩ := h𝒱 i
  have hlevel (n : ℕ) :
      Nonempty (FinitePerfectAdicEtaleLevelData X d φ M (𝒱.etalePrecoverageToEtale i) v n) :=
    finitePerfectAdic_etale_level_descent X d φ hφ M
      (𝒱.etalePrecoverageToEtale i) v n a b hab (hmodel n)
  let D (n : ℕ) := (hlevel n).some
  refine ⟨fun n ↦ (D n).algebra, fun n ↦ (D n).perfect, ?_, ?_⟩
  · intro n
    exact finitePerfectAdic_stalk_reduction X d φ hφ hcompat M
      (𝒱.etalePrecoverageToEtale i) hconn v n (D (n + 1)) (D n)
  · refine ⟨{ connected := hconn
              point := v
              level := fun n ↦ (D n).level
              bounded := fun n ↦ (D n).bounded
              lisse := fun n ↦ (D n).lisse
              transport := ?_ }⟩
    intro n U e W g
    obtain ⟨e⟩ := e
    let c := constantSheaf U.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
    exact (D n).transport U (D n).algebra
      ⟨e ≪≫ c.mapDerivedCategory.mapIso (D n).stalk.some⟩ W g

end AlgebraicGeometry.Scheme
