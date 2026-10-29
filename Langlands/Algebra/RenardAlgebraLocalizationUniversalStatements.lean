import Langlands.Algebra.RenardAlgebraActionLocalization

/-!
# The B-linear universal property of the localized algebra action

Statements for the final sentence of Renard A.III.1, example 5
(9 July 2026, printed p. 252 / PDF p. 258): the published compatible action
on the localization of an endomorphism solves the B-linear universal problem.
-/

set_option autoImplicit false

universe u v w x

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization

/-- Unique factorization through the actual canonical intertwiner, among actual linear
intertwiners that also intertwine the localized operator with an invertible compatible
target operator `c`. -/
def UniversalPropertyStatement : Prop :=
  ∀ (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B] [Module k B]
    (V : Type w) [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (W : Type x) [AddCommGroup W] [Module k W]
    (σ : B →ₙₐ[k] Module.End k W) (c : LinearIntertwiner σ σ),
    IsUnit c.toLinearMap →
      ∀ f : LinearIntertwiner ρ σ, (∀ z, f (a z) = c (f z)) →
        ∃! g : LinearIntertwiner (localizedAction a ρ ha) σ,
          (∀ z, g (localizedEnd a z) = c (g z)) ∧
            g.comp (iotaIntertwiner a ρ ha) = f

/-- The source-facing specialization over an arbitrary field, for the published field
constructor with the complete bilinear nonunital algebra interface. -/
def FieldUniversalPropertyStatement : Prop :=
  ∀ (k : Type u) [Field k] (B : Type v) [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B]
    (V : Type w) [AddCommGroup V] [Module k V]
    (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (W : Type x) [AddCommGroup W] [Module k W]
    (σ : B →ₙₐ[k] Module.End k W) (c : LinearIntertwiner σ σ),
    IsUnit c.toLinearMap →
      ∀ f : LinearIntertwiner ρ σ, (∀ z, f (a z) = c (f z)) →
        ∃! g : LinearIntertwiner (fieldLocalizedAction a ρ ha) σ,
          (∀ z, g (localizedEnd a z) = c (g z)) ∧
            g.comp (iotaIntertwiner a ρ ha) = f

/-- The general ring statement together with its field specialization. -/
def UniversalPropertyStatements : Prop :=
  UniversalPropertyStatement.{u, v, w, x} ∧
    FieldUniversalPropertyStatement.{u, v, w, x}

end Langlands.Renard.AlgebraActionLocalization
