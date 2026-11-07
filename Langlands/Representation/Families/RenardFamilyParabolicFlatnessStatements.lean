import Langlands.Representation.Families.RenardFamilyParabolicFunctors
import Langlands.GroupScheme.Reductive.Basic

/-!
# Renard VI.8.2–VI.8.3: induction and Jacquet modules of `(G, B)`-modules

For a rational parabolic `P = MN` of a connected reductive group `G` over a
nonarchimedean local field and a reduced Noetherian finitely generated `ℂ`-algebra `B`,
normalized parabolic induction sends `(M(F), B)`-modules to `B`-flat families and
admissible ones to admissible ones, and the normalized Jacquet module of a
`(G(F), B)`-module is `B`-flat. Compact open subgroups are open subgroups with compact
carrier.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- VI.8.2, before the Lemma: the normalized parabolic induction `i_P^G(E)` of an
`(M(F), B)`-module `(σ, E)` is a flat `B`-module. -/
def InductionFlatStatement.{u', uB', uE'} : Prop :=
  ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
        [Algebra.FiniteType ℂ B] [IsReduced B]
        (E : Type uE') [AddCommGroup E] [Module B E]
        (σ : Representation B (rationalPoints M) E),
        IsSmooth σ → Module.Flat B E →
          Module.Flat B (LeviInduced p l r hp hr hl hmul σ)

/-- VI.8.2 Lemma: normalized parabolic induction sends admissible `(M(F), B)`-modules to
families whose compact-open fixed modules are finitely generated over `B`. -/
def InductionAdmissibleStatement.{u', uB', uE'} : Prop :=
  ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
        [Algebra.FiniteType ℂ B] [IsReduced B]
        (E : Type uE') [AddCommGroup E] [Module B E]
        (σ : Representation B (rationalPoints M) E),
        IsSmooth σ → Module.Flat B E →
          (∀ K : OpenSubgroup (rationalPoints M), IsCompact (K : Set (rationalPoints M)) →
            Module.Finite B (fixedVectors σ K.toSubgroup)) →
            ∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
              Module.Finite B
                (fixedVectors (leviInducedRepresentation p l r hp hr hl hmul σ) K.toSubgroup)

/-- VI.8.3, before the Proposition: the normalized Jacquet module `r_P^G(V)` of a
`(G(F), B)`-module `(ρ, V)` is a flat `B`-module. -/
def JacquetFlatStatement.{u', uB', uV'} : Prop :=
  ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
      ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
        [Algebra.FiniteType ℂ B] [IsReduced B]
        (V : Type uV') [AddCommGroup V] [Module B V]
        (ρ : Representation B (rationalPoints G) V),
        IsSmooth ρ → Module.Flat B V →
          Module.Flat B (Jacquet ρ (pointImage (r ≫ p)))

/-- The three statements above. -/
def ParabolicFlatnessStatements.{u', uB', uE', uV'} : Prop :=
  InductionFlatStatement.{u', uB', uE'} ∧ InductionAdmissibleStatement.{u', uB', uE'} ∧
    JacquetFlatStatement.{u', uB', uV'}

end Langlands.Renard.AlgebraicFamily
