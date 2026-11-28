import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiSeparation

/-! # Effective étale descent of a polarized abelian scheme -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open PolarizedFiniteLevel

/-- The overlap isomorphism of a group-scheme Čech datum preserves an actual
polarization if dual pullback identifies the two pulled-back polarizations. -/
def PolarizedEtaleDescentCompatible (P : Prerequisites.{u})
    {B U : Scheme.{u}} {p : U ⟶ B} {A : AbelianScheme U}
    (D : GroupScheme.Descent.Datum p A.toGrp) (W : DualWitness A)
    (lam : A ⟶ W.dual P) : Prop :=
  let left := GroupScheme.Descent.fst p
  let right := GroupScheme.Descent.snd p
  let W₁ := W.pullback P left
  let W₂ := W.pullback P right
  let e := ofGrpIso (A := (baseChange left).obj A) (B := (baseChange right).obj A) D.overlap
  DualWitness.transportMap P e W₁ W₂ (W.pullbackMap P right W₂ lam) =
    W.pullbackMap P left W₁ lam

/-- Over a locally noetherian base, a polarized abelian scheme with a
polarization-preserving Čech datum along a surjective étale morphism
comes from a polarized abelian scheme over the base. The actual pullback
isomorphism identifies the canonical and given Čech data and preserves
the polarization. -/
def PolarizedAbelianSchemeEtaleDescentStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (B U : Scheme.{u}) [IsLocallyNoetherian B]
    (p : U ⟶ B) [Etale p] [Surjective p]
    (A : AbelianScheme U) (D : GroupScheme.Descent.Datum p A.toGrp)
    (W : DualWitness A) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam → PolarizedEtaleDescentCompatible P D W lam →
      ∃ (A₀ : AbelianScheme B) (V : DualWitness A₀) (lam₀ : A₀ ⟶ V.dual P)
        (e : (baseChange p).obj A₀ ≅ A),
        V.IsPolarization P lam₀ ∧
          GroupScheme.Descent.Compatible (GroupScheme.Descent.canonicalDatum p A₀.toGrp)
            D (groupHom e.hom) ∧
          DualWitness.transportMap P e (V.pullback P p) W lam =
            V.pullbackMap P p (V.pullback P p) lam₀

end Langlands.AbelianScheme
