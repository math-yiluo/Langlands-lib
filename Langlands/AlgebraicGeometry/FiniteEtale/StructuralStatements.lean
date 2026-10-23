import Langlands.AlgebraicGeometry.FiniteEtale.Statements
import Mathlib.CategoryTheory.Galois.Basic

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Finite limits and finite coproducts for actual finite étale covers, with
preservation by the actual geometric fibre functor. -/
def GeometricFiniteLimitsCoproducts {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  HasTerminal (Cover S) ∧
  HasPullbacks (Cover S) ∧
  HasFiniteCoproducts (Cover S) ∧
  PreservesLimitsOfShape (Discrete PEmpty.{1}) (fiberFunctor s hfin) ∧
  PreservesLimitsOfShape WalkingCospan (fiberFunctor s hfin) ∧
  PreservesFiniteCoproducts (fiberFunctor s hfin)

/-- Monomorphisms exhibit direct summands, and the actual geometric fibre
functor preserves epimorphisms and reflects isomorphisms. -/
def GeometricMonoEpiConservative {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  (∀ {X Y : Cover S} (i : X ⟶ Y) [Mono i],
    ∃ (Z : Cover S) (v : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i v))) ∧
  Functor.PreservesEpimorphisms (fiberFunctor s hfin) ∧
  (fiberFunctor s hfin).ReflectsIsomorphisms

/-- Quotients by finite groups exist in actual finite étale covers and are
preserved by the actual geometric fibre functor. -/
def GeometricFiniteGroupQuotients {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (Cover S) ∧
    PreservesColimitsOfShape (SingleObj G) (fiberFunctor s hfin)

end Langlands.AlgebraicGeometry.FiniteEtale
