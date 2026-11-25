/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Definitions for coefficient-heart stratification

The existing definitions are factored out so the independent refinement and lisse
restriction lemmas can be imported by their assembly theorem without an import cycle.
Source: blueprint common-stratification, clauses (1)--(3).
(blueprint: lemma-constructible-sheaves).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lisse means pro-etale locally free of finite rank, with ranks allowed to vary on the
cover. Source: blueprint lemma-constructible-sheaves, introductory paragraph
(blueprint: lemma-constructible-sheaves). -/
def IsLisseCoefficientModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
    Mod.IsFree (condensedRingObj Λ (U.X i)) ((CondensedRing.upperStar Λ (U.f i)).obj M)

/-- The underlying ring object of a condensed ring, with its canonical multiplication.
Source: blueprint sk-def-sfb-condensed-ring, first paragraph
(blueprint: lemma-constructible-sheaves). -/
abbrev coefficientHeartRingObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ

/-- All three assertions, with exactness of a pair of arbitrary arrows expressed as equality
of its image and kernel subobjects. This also forces their composite to vanish. Longer
sequences are exact precisely when this condition holds at each term.
Source: blueprint sk-lem-coefficient-heart-common-stratification, clauses (1)--(3)
(blueprint: lemma-constructible-sheaves). -/
def CoefficientHeartStratificationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∀ (n : ℕ) (P : Fin n → X.FiniteLocallyClosedStratification),
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (P j).n,
        R.stratum a ⊆ (P j).stratum b) ∧
      (∀ a : Fin R.n, ConnectedSpace (R.domain a)) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)) ∧
  ((∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
        IsLisseCoefficientModule Λ M →
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel Λ (P.domain a)
          ((CondensedRing.upperStar Λ (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj M))) ∧
  (∀ R : X.FiniteLocallyClosedStratification,
    (∀ a : Fin R.n,
      PreservesFiniteLimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      Nonempty (CondensedRing.upperStar Λ (R.immersion a) ⋙
          Mod.forget (condensedRingObj Λ (R.domain a)) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} (R.immersion a))) ∧
    (∀ (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B),
      (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)) ∧
      (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar Λ (R.immersion a)).map f))) ∧
    ∀ (A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B) (g : B ⟶ C),
      imageSubobject f = kernelSubobject g ↔
        ∀ a : Fin R.n,
          imageSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map f) =
            kernelSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map g))

end AlgebraicGeometry.ProEtale
