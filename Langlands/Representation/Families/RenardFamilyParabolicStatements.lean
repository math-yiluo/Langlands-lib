import Langlands.Representation.Families.RenardFamilyParabolicFunctors
import Langlands.GroupScheme.Reductive.Basic

/-!
# Renard VI.8.2–VI.8.3: base change commutes with induction; Jacquet modules of finite type

For a rational parabolic `P = MN` of a connected reductive group `G` over a
nonarchimedean local field and a reduced Noetherian finitely generated `ℂ`-algebra `B`,
normalized parabolic induction of families commutes with base change to a `B`-algebra
`C`, and the normalized Jacquet module of a family that is finitely generated over
`B[G(F)]` is finitely generated over `B[M(F)]`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- VI.8.2 Proposition: base change commutes with induction. For a `B`-algebra `C` and an
`(M(F), B)`-module `(σ, E)`, there is a `G(F)`-equivariant `C`-linear isomorphism
`C ⊗_B i_P^G(E) ≃ i_P^G(C ⊗_B E)` sending `c ⊗ f` to the function `g ↦ c ⊗ f(g)`. -/
def InductionBaseChangeStatement.{u', uB', uC', uE'} : Prop :=
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
        (C : Type uC') [CommRing C] [Algebra ℂ C] [IsNoetherianRing C] [IsReduced C]
        [Algebra B C] [IsScalarTower ℂ B C]
        (E : Type uE') [AddCommGroup E] [Module B E]
        (σ : Representation B (rationalPoints M) E),
        IsSmooth σ → Module.Flat B E →
          ∃ e : C ⊗[B] LeviInduced p l r hp hr hl hmul σ ≃ₗ[C]
              LeviInduced p l r hp hr hl hmul (baseChange C σ),
            (∀ (g : rationalPoints G) (x : C ⊗[B] LeviInduced p l r hp hr hl hmul σ),
              e (baseChange C (leviInducedRepresentation p l r hp hr hl hmul σ) g x) =
                leviInducedRepresentation p l r hp hr hl hmul (baseChange C σ) g (e x)) ∧
            ∀ (c : C) (f : LeviInduced p l r hp hr hl hmul σ) (g : rationalPoints G),
              Induction.eval _ _ (e (c ⊗ₜ[B] f)) g = c ⊗ₜ[B] Induction.eval _ _ f g

/-- VI.8.3 Proposition: the normalized Jacquet module `r_P^G` of a `(G(F), B)`-module that
is finitely generated over `B[G(F)]` is finitely generated over `B[M(F)]`. -/
def JacquetFiniteTypeStatement.{u', uB', uV'} : Prop :=
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
      (hmul : IsIso (subgroupMultiplication l r))
      (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
      [Algebra.FiniteType ℂ B] [IsReduced B]
      (V : Type uV') [AddCommGroup V] [Module B V]
      (ρ : Representation B (rationalPoints G) V),
      IsSmooth ρ → Module.Flat B V →
        Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule →
          Module.Finite (MonoidAlgebra B (rationalPoints M))
            (leviJacquetRepresentation p l r hp hr hl hmul ρ).asModule

/-- The VI.8.2 and VI.8.3 Propositions together. -/
def ParabolicStatements.{u', uB', uC', uE', uV'} : Prop :=
  InductionBaseChangeStatement.{u', uB', uC', uE'} ∧ JacquetFiniteTypeStatement.{u', uB', uV'}

end Langlands.Renard.AlgebraicFamily
