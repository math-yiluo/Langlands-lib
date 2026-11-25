/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Flatness for the canonical coefficient-model comparison pullback
Source: Stacks Project, Tag 05VD.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem flat_iso {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    {M N : ConstantCompletion.Mod R} (e : M ≅ N) (hM : SheafOfModules.IsFlat M) :
    SheafOfModules.IsFlat N := by
  let _ := SheafOfModules.monoidalCategory R
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    ((MonoidalCategory.curriedTensor _).flip.mapIso e) hM

private theorem flat_zero {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (M : ConstantCompletion.Mod R) (hM : IsZero M) : SheafOfModules.IsFlat M := by
  let _ := SheafOfModules.monoidalCategory R
  let _ : MonoidalPreadditive (ConstantCompletion.Mod R) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  exact (ObjectProperty.flat_of_isZero hM).2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical comparison inverse image preserves flat module sheaves.
Source: Stacks Project, Tag 05VD, lemma-pullback-flat; blueprint finite-Tor comparison,
paragraph Flatness is preserved (auxiliary; not a blueprint node).

Proof: the continuous inclusion and the canonical constant-section ring map give a
ringed-topos morphism whose module direct image is exactly the specified pushforward.
Apply RingedToposMorphism.exists_kFlatPullback. Its left adjoint is naturally isomorphic
to constructibleComparisonPullback by uniqueness of left adjoints to that direct image.
Place M in degree zero. Its other terms are zero, hence flat, and the bounded-above
flat-complex theorem makes it K-flat. The general pullback theorem gives flat terms
for its image. The degree-zero term is the pullback of M; transport its flatness along
the single-complex term isomorphism and the left-adjoint identification.
This works for any discrete commutative coefficient ring, including the zero ring,
and requires no constructibility or Noetherian hypothesis. -/
theorem constructibleComparisonPullback_flat (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (M : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A))
    (hM : SheafOfModules.IsFlat M) :
    SheafOfModules.IsFlat ((constructibleComparisonPullback.{u, v} X A).obj M) := by
  classical
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let R := ConstantCompletion.constant J A
  let S := ConstantCompletion.constant K A
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const _).obj (CommRingCat.of A))
      ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S)).symm
        (Functor.whiskerLeft F.op (toSheafify K ((Functor.const _).obj (CommRingCat.of A))))
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists F
    (Scheme.smallModelComparisonPullback.{u, v} X)
    (Scheme.smallModelProEtaleComparison.{u, v} X) S R φ
  obtain ⟨G, hG, adjG, hflat, _⟩ := p.exists_kFlatPullback K J S R
  have : G.Additive := hG
  let adjF := SheafOfModules.pullbackPushforwardAdjunction
    (F := F) (constructibleComparisonRingMap X A)
  have adjG' : G ⊣ SheafOfModules.pushforward
      (F := F) (constructibleComparisonRingMap X A) := by
    simpa only [hp, φ, R, S, J, K, F, constructibleComparisonRingMap] using adjG
  let e : G ≅ constructibleComparisonPullback X A := adjG'.leftAdjointUniq adjF
  let _ : HasFiniteLimits (ConstantCompletion.Mod R) :=
    SheafOfModules.Finite.hasFiniteLimits _
  let _ : HasZeroObject (ConstantCompletion.Mod R) :=
    Limits.hasZeroObject_of_hasTerminal_object
  let P : ConstantCompletion.Cx R :=
    (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj M
  have hf : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact flat_iso R (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm hM
    · exact flat_zero R _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn)
  have hk : CochainComplex.IsKFlatTensor (R := R) P :=
    CochainComplex.isKFlat_of_boundedAbove_flat (R := R) P
    ⟨0, fun n hn ↦ HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n (ne_of_gt hn)⟩ hf
  have ht := (hflat P hk hf).2 0
  let es : G.obj (P.X 0) ≅ (constructibleComparisonPullback X A).obj M :=
    G.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M) ≪≫ e.app M
  exact flat_iso S es ht

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Termwise comparison carries K-flat complexes with flat terms to K-flat complexes.
Source: Stacks Project, Tag 0G7E
(auxiliary; not a blueprint node).
Proof: construct the same ringed-topos morphism and identify its supplied pullback
with the canonical module pullback by uniqueness of left adjoints. The general
K-flat pullback theorem gives K-flatness before this identification. Tensor the
complex isomorphism with each acyclic test to transport its vanishing homology. -/
theorem constructibleComparisonComplexPullback_kFlat (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (P : ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A))
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n, SheafOfModules.IsFlat (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((constructibleComparisonComplexPullback X A).obj P) := by
  classical
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let R := ConstantCompletion.constant J A
  let S := ConstantCompletion.constant K A
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const _).obj (CommRingCat.of A))
      ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S)).symm
        (Functor.whiskerLeft F.op (toSheafify K ((Functor.const _).obj (CommRingCat.of A))))
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists F
    (Scheme.smallModelComparisonPullback.{u, v} X)
    (Scheme.smallModelProEtaleComparison.{u, v} X) S R φ
  obtain ⟨G, hG, adjG, hflat, _⟩ := p.exists_kFlatPullback K J S R
  have : G.Additive := hG
  let adjF := SheafOfModules.pullbackPushforwardAdjunction
    (F := F) (constructibleComparisonRingMap X A)
  have adjG' : G ⊣ SheafOfModules.pushforward
      (F := F) (constructibleComparisonRingMap X A) := by
    simpa only [hp, φ, R, S, J, K, F, constructibleComparisonRingMap] using adjG
  let e : G ≅ constructibleComparisonPullback X A := adjG'.leftAdjointUniq adjF
  let _ : (constructibleComparisonPullback X A).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _ adjF.isLeftAdjoint
  let eP := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  let _ := SheafOfModules.monoidalCategory S
  let _ := SheafOfModules.symmetricCategory S
  intro Z hZ i
  exact ((hflat P hP hf).1 Z hZ i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj Z).mapIso eP)

end AlgebraicGeometry.ProEtale
