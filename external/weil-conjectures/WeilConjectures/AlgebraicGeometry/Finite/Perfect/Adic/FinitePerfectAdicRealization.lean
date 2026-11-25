/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Effectivity of uniformly perfect finite quotient systems

Source: Stacks Project, proetale.tex, Tag 09C6; More on Algebra, Tag 09AW
(blueprint: lem-weil-pbc-finite-perfect-adic-realization).

The input consists of finite-level models. The output identifies the derived limit of
the specified quotient tower, without assuming that its original object is complete.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The representative restriction is the exact derived restriction. -/
private theorem finitePerfectRestrictionComparison
    (X : Scheme.{t}) (R : Sheaf (ProEt.topology X) RingCat.{t + 1})
    (U : X.ProEt) (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U K ≅
      (ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} R U).obj K) := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1} R U).1
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1} R U).2.1
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1} R U).2.2
  exact ⟨(F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)⟩

/-- Algebraic reconstruction retains the actual normalized transition maps. -/
private theorem finitePerfectAlgebraicModel
    {A : Type t} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    [HasDerivedCategory.{t} (ModuleCat.{t} A)]
    [∀ n : ℕ, HasDerivedCategory.{t} (ModuleCat.{t} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (v : ∀ n : ℕ, K (n + 1) ⟶ (DerivedCategory.adicStepRestriction I n).obj (K n))
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (B : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (badj : ∀ n : ℕ, B n ⊣ DerivedCategory.adicStepRestriction I n)
    (hbase : ∀ n : ℕ, IsIso (((badj n).homEquiv (K (n + 1)) (K n)).symm (v n)))
    (hperfect : DerivedCategory.IsPerfect (K 0)) :
    ∃ (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      ∃ e : ∀ n : ℕ, (L n).obj (DerivedCategory.Q.obj P) ≅ K n,
        ∀ n : ℕ,
          (adj (n + 1)).unit.app (DerivedCategory.Q.obj P) ≫
              (DerivedCategory.adicLevelRestriction I (n + 1)).map (e (n + 1)).hom ≫
              DerivedCategory.adicTowerTransition I K v n =
            (adj n).unit.app (DerivedCategory.Q.obj P) ≫
              (DerivedCategory.adicLevelRestriction I n).map (e n).hom := by
  classical
  obtain ⟨hprod, _, _⟩ := derivedCategory_countableProducts_core.{0}
    (ModuleCat.{t} A)
  let := hprod
  obtain ⟨C, p, δ, hlim⟩ :=
    (exists_isDerivedLimit_and_iso
      (fun n ↦ (DerivedCategory.adicLevelRestriction I n).obj (K n))
      (DerivedCategory.adicTowerTransition I K v)).1
  obtain ⟨hC, _, hred, hcompat⟩ :=
    DerivedCategory.rlim_perfect_complete I K v L adj B badj hbase hperfect C p δ hlim
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := hC
  let e (n : ℕ) : (L n).obj (DerivedCategory.Q.obj P) ≅ K n :=
    (L n).mapIso i.symm ≪≫ @asIso _ _ _ _
      (DerivedCategory.adicLimitReduction I K L adj C p n) (hred n)
  refine ⟨P, a, b, ha, hb, hP, e, ?_⟩
  intro n
  have hn (k : ℕ) :
      (adj k).unit.app (DerivedCategory.Q.obj P) ≫
          (DerivedCategory.adicLevelRestriction I k).map (e k).hom =
        i.inv ≫ (adj k).unit.app C ≫
          (DerivedCategory.adicLevelRestriction I k).map
            (DerivedCategory.adicLimitReduction I K L adj C p k) := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    rw [Functor.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg (fun z ↦ z ≫ (DerivedCategory.adicLevelRestriction I k).map
        (DerivedCategory.adicLimitReduction I K L adj C p k))
        ((adj k).unit.naturality i.inv).symm
  rw [reassoc_of% hn (n + 1), hn n]
  simpa only [Category.assoc] using congrArg (fun z ↦ i.inv ≫ z) (hcompat n)

/-- A normalized quotient system with uniformly bounded etale local perfect constant
models has a pro-etale local perfect completed realization.

Source: Stacks Project, proetale.tex, lemma-connected-adic-lisse (Tag 09C6), specifically
its algebraic tower and compatible-isomorphism argument; More on Algebra, Tag 09AW;
Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-realization).

Proof:
Refine the input etale cover by connected components of Noetherian affine opens.
Finite-ring derived comparison descends each finite quotient to a bounded etale
complex. Their locally constant cohomology and uniform Tor bounds follow from their
given perfect local models. Full faithfulness lifts the datum's normalized reduction
maps uniquely, retaining all quotient cocycles. Fix a geometric point on each nonempty
connected neighborhood and take the exact stalk of this entire normalized system.
This gives a tower E_n over A/I^(n+1), whose first term is perfect and whose reduction
maps are isomorphisms. Its transitions are the adjoints of those same isomorphisms,
not independent choices of maps. Algebraic perfect inverse-limit reconstruction gives
a bounded finite-projective A-complex P and compatible isomorphisms of its reductions
with E_n. Finite-ring derived local constancy identifies each etale level locally with
its stalk model E_n. The finite locally constant sheaves Isom(constant E_n, L_n) have
nonempty stalks. Compatible finite derived trivialization therefore supplies one
pro-etale cover with compatible trivializations at all levels.
For a finite-projective term of P choose an idempotent on a finite free module. Its
finite quotient sheaves have sectionwise surjective transitions. Recursive lifting
makes 1-shift on their product sectionwise surjective. Its kernel is the same
idempotent summand of the completed coefficient ring. The Roos triangle therefore
identifies the derived limit of this bounded quotient complex with completed scalar
extension of the constant P. Exact slice restriction preserves products, hence the
Roos triangle; it thus carries the original strict quotient tower's derived limit to
this same local limit. Applying the compatible trivializations gives the displayed
isomorphism. Assemble the refinements of the original cover; empty members use empty
covers. No completeness hypothesis on the original M is used in this argument. -/
theorem finitePerfectModels_adic_realization
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A]
    [(koszulConstantFunctor X A).PreservesZeroMorphisms]
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((reconstructionRlim X d).obj ((completedAdicReduction X d).obj M)) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X A P)))) := by
  classical
  obtain ⟨S, hS, hlocal⟩ :=
    finitePerfectAdicTower_extraction X d φ _hφ _hcompat M _hmodels
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨T⟩ := hlocal U f hf
  obtain ⟨P, a, b, ha, hb, hP, e, he⟩ := finitePerfectAlgebraicModel d.ideal
    T.level T.transition T.extension T.adjunction T.stepExtension T.stepAdjunction
    T.normalized T.residuePerfect
  refine ⟨P, a, b, ha, hb, hP, ?_⟩
  obtain ⟨i⟩ := finitePerfectAdicTower_limit X d U
    ((completedAdicReduction X d).obj M) T P a b ha hb hP e he
  let F := finitePerfectAdicConstant X A
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  let c : (finitePerfectAdicDerivedConstant X A).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (finiteModelConstantComplex X A P) :=
    F.mapDerivedCategoryFactors.app P
  let R := ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
    (completedAdicRing X d) U
  obtain ⟨i₁⟩ := finitePerfectRestrictionComparison X (completedAdicRing X d) U
    ((reconstructionRlim X d).obj ((completedAdicReduction X d).obj M))
  obtain ⟨i₂⟩ := finitePerfectRestrictionComparison X (completedAdicRing X d) U
    ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
      (DerivedCategory.Q.obj (finiteModelConstantComplex X A P)))
  exact ⟨i₁ ≪≫ i ≪≫
    R.mapIso ((completedAdicDerivedChange X (completedAdicScalar X d)).mapIso c) ≪≫ i₂.symm⟩

end AlgebraicGeometry.Scheme
