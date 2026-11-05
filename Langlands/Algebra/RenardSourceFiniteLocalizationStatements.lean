import Langlands.Algebra.RenardAdditiveScalarFiniteLocalizationStatements
import Langlands.Algebra.RenardAlgebraActionLocalizationCategory
import Langlands.CategoryTheory.RenardFiniteType

/-!
# Renard C.II: the final proposition under each candidate finiteness reading

Renard 2026, Appendix C.II, printed p. 279 / PDF p. 285. The proposition assumes a
commutative Noetherian complex algebra `B`, a `B`-module `L` of finite type, and a
localization `L_a` of finite type. For possibly nonunital `B` these phrases admit
several readings. Each statement below fixes one reading explicitly and keeps the
source conclusions. No reading is declared to be the author's.
-/

set_option autoImplicit false

namespace Langlands.Renard.SourceFiniteLocalization

open CategoryTheory Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism
open Langlands.Renard.AlgebraActionLocalization

universe uB uV

/-- The source conclusions: `a` is eventually stable, and for every positive `n`
with `a ^ n` stable, `ker (a ^ n)` and `im (a ^ n)` are complementary and the actual
localized pair is canonically isomorphic to `(im (a ^ n), a|im (a ^ n))`. -/
def SourceConclusion {B : Type uB} [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ) : Prop :=
  EventuallyStable f.toLinearMap ∧
    ∀ n : ℕ, 0 < n → Stable (f.toLinearMap ^ n) → CompatibleStablePowerImageAt ρ f n

/-- Additive reading: `B`-modules are the actual nonunital modules of
`NonUnitalModuleCat B`, whose subobjects are the stable additive subgroups.
`B` is Noetherian as its own regular object, and the source and its actual
localization are objects of finite type in Renard's categorical sense. -/
def AdditiveReadingStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalCommRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    IsNoetherianObject
      (@NonUnitalModuleCat.of B _ B _
        (NonUnitalModule.ofLinearEndHom (NonUnitalAlgHom.lmul ℂ B))) →
    IsFiniteTypeObject
      (@NonUnitalModuleCat.of B _ V _ (NonUnitalModule.ofLinearEndHom ρ)) →
    IsFiniteTypeObject
      (@NonUnitalModuleCat.of B _ (Localized f.toLinearMap) _
        (NonUnitalModule.ofLinearEndHom
          (localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)))) →
    SourceConclusion ρ f

/-- Compatible reading: `B`-modules are complex vector spaces with a compatible
action, the actual category `ActionModuleCat ℂ B`, whose subobjects are the stable
complex subspaces. The finiteness phrases are Renard's categorical ones there. -/
def CompatibleReadingStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalCommRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    IsNoetherianObject (ActionModuleCat.of (k := ℂ) B (NonUnitalAlgHom.lmul ℂ B)) →
    IsFiniteTypeObject (ActionModuleCat.of (k := ℂ) V ρ) →
    IsFiniteTypeObject
      (ActionModuleCat.of (k := ℂ) (Localized f.toLinearMap)
        (localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v))) →
    SourceConclusion ρ f

/-- Unitization reading: `B` is Noetherian when its actual complex unitization is a
Noetherian ring, and a module is of finite type when it is finitely generated over
that unitization, acting by `(c, b) • v = c • v + ρ b v`. -/
def UnitizationReadingStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalCommRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    IsNoetherianRing (Unitization ℂ B) →
    (letI := CompatibleUnitization.module ρ
     Module.Finite (Unitization ℂ B) V) →
    (letI := CompatibleUnitization.module
      (localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v))
     Module.Finite (Unitization ℂ B) (Localized f.toLinearMap)) →
    SourceConclusion ρ f

/-- The final C.II proposition under the additive, compatible and unitization
readings, in that order. -/
def SourceFiniteLocalizationStatements : Prop :=
  AdditiveReadingStatement.{uB, uV} ∧
    CompatibleReadingStatement.{uB, uV} ∧
    UnitizationReadingStatement.{uB, uV}

end Langlands.Renard.SourceFiniteLocalization
