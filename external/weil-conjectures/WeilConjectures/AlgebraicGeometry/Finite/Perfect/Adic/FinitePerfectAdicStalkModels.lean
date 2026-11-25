/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy

/-! # Algebraic stalk models before simultaneous trivialization

Source: Stacks Project, Tag 09C6, the normalized algebraic stalk diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Separate finite-level markings by one fixed algebraic tower on an etale chart.
The covering at a level can depend on that level. No compatibility of markings is asserted.
Source: Stacks Tags 09C6 and 09B1
(blueprint: lem-weil-pbc-finite-perfect-adic-stalk-models). -/
def FinitePerfectAdicLevelMarkings (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) : Prop :=
  ∀ n : ℕ, ∃ S : Sieve V, S ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), S g → Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1))).obj (T.level n))))

/-- A normalized algebraic stalk system gives separate local models at all finite levels.
There is no common pro-etale covering and no compatible family of markings in this result.

Source: Stacks Project, Tag 09C6, the paragraph constructing the objects M_n and their
normalized consecutive maps, using Tags 09AL, 09B1 and 094G.
(blueprint: lem-weil-pbc-finite-perfect-adic-stalk-models).

Proof: Refine the cover in HasUniformFinitePerfectModels by connected Noetherian affine
etale charts. Noetherian local connectedness supplies these refinements; omit empty
charts. On each chart descend each finite quotient complex to the etale site by the
finite-ring constructible derived comparison. Its finite locally constant cohomology
and boundedness follow from the given local bounded finite-projective models. Full
faithfulness descends the actual consecutive quotient arrows. Their transposes under
derived extension and exact restriction are invertible, by the balancing isomorphism
for the strict reduction tower and the quotient compatibility of φ. Choose one geometric
point of the nonempty connected chart and apply its exact stalk to this diagram. The
constant-stalk comparison and tensor-pullback comparison identify its transitions with
maps of algebraic quotient complexes, with invertible adjoint transposes. Derived scalar
extension provides the recorded left adjoints, at levels and between consecutive levels.
Each stalk is perfect: locally it is the stalk of the specified bounded finite-projective
constant model. Finite-ring derived local constancy on the connected chart identifies
each etale level locally with that same stalk, independently for each level. Transport
these separate isomorphisms through the finite coefficient comparisons and exact slice
restriction to obtain FinitePerfectAdicLevelMarkings. Composing the refinements gives the
etale cover of X. The empty scheme uses its empty cover. No compatible choice of the
finite-level markings, inverse limit, or perfect complex over A is used here. -/
theorem finitePerfectAdic_stalk_models
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ 𝒱 : Cover.{t} etalePrecoverage X, ∀ i : 𝒱.I₀,
      ∃ T : FinitePerfectAdicAlgebraTower d,
        (∀ n : ℕ, DerivedCategory.IsPerfect (T.level n)) ∧
        FinitePerfectAdicLevelMarkings X d φ M (𝒱.etalePrecoverageToEtale i) T := by
  classical
  obtain ⟨𝒱, h𝒱⟩ := finitePerfectAdic_etale_stalk_data X d φ hφ hcompat M hmodels
  refine ⟨𝒱, ?_⟩
  intro i
  obtain ⟨E, hE, hstep, ⟨D⟩⟩ := h𝒱 i
  let L (n : ℕ) := ConstantScalarRealization.moduleDerivedExtension
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let adj (n : ℕ) : L n ⊣ DerivedCategory.adicLevelRestriction d.ideal n :=
    ConstantScalarRealization.moduleDerivedAdjunction (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let Ls (n : ℕ) := ConstantScalarRealization.moduleDerivedExtension
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let adjs (n : ℕ) : Ls n ⊣ DerivedCategory.adicStepRestriction d.ideal n :=
    ConstantScalarRealization.moduleDerivedAdjunction
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let T : FinitePerfectAdicAlgebraTower d :=
    { level := E
      transition := fun n ↦ (adjs n).homEquiv _ _ (hstep n).some.hom
      extension := L
      adjunction := adj
      stepExtension := Ls
      stepAdjunction := adjs
      normalized := fun n ↦ by
        rw [Equiv.symm_apply_apply]
        infer_instance
      residuePerfect := hE 0 }
  refine ⟨T, hE, ?_⟩
  intro n
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  obtain ⟨𝒰, h𝒰⟩ :=
    (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy
      (𝒱.etalePrecoverageToEtale i).left B (D.level n) (D.bounded n) (D.lisse n)).2.2.2
        D.connected _ ((𝒱.etalePrecoverageToEtale i).left.algClosurePoint D.point)
  let U (j : 𝒰.I₀) : X.Etale := Etale.mk (𝒰.f j ≫ (𝒱.etalePrecoverageToEtale i).hom)
  let f (j : 𝒰.I₀) : U j ⟶ 𝒱.etalePrecoverageToEtale i :=
    MorphismProperty.Over.homMk (𝒰.f j) rfl
  refine ⟨Sieve.ofArrows U f, ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨j, y, hy⟩
  · intro W g hg
    obtain ⟨j, a, _⟩ := (Sieve.mem_ofArrows_iff U f g).mp hg
    exact D.transport n (𝒰.etalePrecoverageToEtale j) (h𝒰 j) W a

end AlgebraicGeometry.Scheme
