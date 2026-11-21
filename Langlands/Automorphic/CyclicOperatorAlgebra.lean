import Langlands.Representation.FiniteVectors
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Basic.Complex.Basic

/-! # Restriction of an algebra action to a cyclic subrepresentation -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open FiniteVectors

variable {R V : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V]
  (A : R →ₐ[ℂ] Module.End ℂ V)

local notation "ρ" => AlgHom.toMonoidHom' A
local notation "𝓡" => MonoidAlgebra ℂ R

/-- The actual span of one vector for the represented algebra. -/
def cyclicAlgebraSubrepresentation (v : Representation.asModule ρ) : Subrepresentation ρ :=
  Subrepresentation.ofSubmodule' (𝓡 ∙ v)

local notation "P" => cyclicAlgebraSubrepresentation A
local notation "C" v => (P v).toSubmodule

/-- The distinguished generator in its cyclic subrepresentation. -/
def cyclicAlgebraGenerator (v : Representation.asModule ρ) : C v :=
  ⟨v, Submodule.mem_span_singleton_self v⟩

/-- Restrict the full algebra action to the cyclic subrepresentation. -/
def cyclicAlgebraAction (v : Representation.asModule ρ) : R →ₐ[ℂ] Module.End ℂ (C v) where
  toFun a := (P v).toRepresentation a
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := LinearMap.ext fun _ => Subtype.ext (LinearMap.congr_fun (map_zero A) _)
  map_add' a b := LinearMap.ext fun _ => Subtype.ext (LinearMap.congr_fun (map_add A a b) _)
  commutes' c := LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (A.commutes c) w.val)

/-- Inclusion of the cyclic space preserves the actual operator action. -/
def cyclicAlgebraInclusion (v : Representation.asModule ρ) :
    Representation.IntertwiningMap (AlgHom.toMonoidHom' (cyclicAlgebraAction A v)) ρ where
  toLinearMap := (C v).subtype
  isIntertwining' _ := LinearMap.ext fun _ => rfl

private theorem cyclicAlgebra_smul_eq (r : 𝓡) (v : Representation.asModule ρ) :
    (r • v : Representation.asModule ρ) = A (MonoidAlgebra.lift ℂ R R (MonoidHom.id R) r) v := by
  change Representation.asAlgebraHom ρ r v = _
  induction r using MonoidAlgebra.induction_on with
  | of a => rw [Representation.asAlgebraHom_of, MonoidAlgebra.lift_of]; rfl
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb
  | smul c a ha =>
    simp only [map_smul]
    exact congrArg (c • ·) ha

/-- Every vector in the cyclic space is one algebra operator applied to the generator. -/
theorem exists_cyclicAlgebraAction_generator (v : Representation.asModule ρ) (w : C v) :
    ∃ a : R, cyclicAlgebraAction A v a (cyclicAlgebraGenerator A v) = w := by
  have hw : (w.val : Representation.asModule ρ) ∈ (𝓡 ∙ v) := w.property
  have he : ∃ r : 𝓡, r • v = (w.val : Representation.asModule ρ) :=
    (Submodule.mem_span_singleton (M := Representation.asModule ρ)).mp hw
  obtain ⟨r, hr⟩ := he
  refine ⟨MonoidAlgebra.lift ℂ R R (MonoidHom.id R) r, Subtype.ext ?_⟩
  exact (cyclicAlgebra_smul_eq A r v).symm.trans hr

/-- In particular, the orbit span of the distinguished generator is the full cyclic space. -/
theorem cyclicAlgebraGenerator_orbitSpan (v : Representation.asModule ρ) :
    orbitSpan (AlgHom.toMonoidHom' (cyclicAlgebraAction A v)) (cyclicAlgebraGenerator A v) = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨a, ha⟩ := exists_cyclicAlgebraAction_generator A v w
  exact Submodule.subset_span ⟨a, ha⟩

private def cyclicAlgebraModuleEquiv (v : Representation.asModule ρ) :
    Representation.asModule (AlgHom.toMonoidHom' (cyclicAlgebraAction A v)) ≃ₗ[𝓡] (𝓡 ∙ v) := by
  let i := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (cyclicAlgebraInclusion A v)
  let j := i.codRestrict (𝓡 ∙ v) (fun w => w.property)
  exact LinearEquiv.ofBijective j
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun w => ⟨⟨w.val, w.property⟩, rfl⟩⟩

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ R W)

/-- Transfer a quotient of the cyclic module to the restricted algebra representation. -/
def cyclicAlgebraIntertwiner (v : Representation.asModule ρ) (q : (𝓡 ∙ v) →ₗ[𝓡] τ.asModule) :
    Representation.IntertwiningMap (AlgHom.toMonoidHom' (cyclicAlgebraAction A v)) τ :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
    (q.comp (cyclicAlgebraModuleEquiv A v).toLinearMap)

/-- Surjectivity is retained onto the same target representation. -/
theorem cyclicAlgebraIntertwiner_surjective (v : Representation.asModule ρ)
    (q : (𝓡 ∙ v) →ₗ[𝓡] τ.asModule) (hq : Function.Surjective q) :
    Function.Surjective (cyclicAlgebraIntertwiner A τ v q) :=
  hq.comp (cyclicAlgebraModuleEquiv A v).surjective

end Langlands.Automorphic
