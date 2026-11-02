import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

/-!
# Finite length from irreducible inputs

A proposition definition: a functor between actual smooth representation
categories that preserves short exact sequences of finite-length objects, and
sends every irreducible smooth representation to one of finite group-algebra
length, sends every smooth representation of finite group-algebra length to one
of finite group-algebra length. The name refers to induction on the length, not
to parabolic induction. Nothing here proves the assertion.
-/

namespace Langlands.SmoothRep

universe uR uG uV uS uH uW

open CategoryTheory

/-- For every coefficient field `k`, topological group `G`, coefficient ring `S`,
topological group `H` and functor `Φ : SmoothRep k G ⥤ SmoothRep S H`: if `Φ`
sends short exact sequences of finite-length objects to short exact sequences
and sends every irreducible smooth representation to one of finite group-algebra
length, then `Φ` preserves finite group-algebra length. This is a proposition
definition, not its proof. -/
def FiniteLengthInductionStatement : Prop :=
  ∀ (k : Type uR) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (S : Type uS) [CommRing S] (H : Type uH) [Group H] [TopologicalSpace H]
    (Φ : SmoothRep.{uR, uG, uV} k G ⥤ SmoothRep.{uS, uH, uW} S H),
    PreservesFiniteLengthShortExact Φ →
      (∀ A : SmoothRep.{uR, uG, uV} k G, A.IsIrreducible → (Φ.obj A).HasFiniteLength) →
        PreservesFiniteLength Φ

end Langlands.SmoothRep
