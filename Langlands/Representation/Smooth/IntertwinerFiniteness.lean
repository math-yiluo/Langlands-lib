import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! Finite-dimensional intertwiner spaces and integral central operators. -/

noncomputable section

namespace Langlands

universe uG uV uW uI

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Evaluate an intertwiner on a family of vectors, retaining their stabilizers. -/
def fixedGeneratorEvaluation (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    {ι : Type uI} (v : ι → V) (K : ι → Subgroup G)
    (hv : ∀ i, v i ∈ fixedVectors ρ (K i)) :
    ρ.IntertwiningMap σ →ₗ[ℂ] ∀ i, fixedVectors σ (K i) where
  toFun f i := fixedVectorsMap f (K i) ⟨v i, hv i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Group-algebra generators determine an intertwiner. -/
theorem fixedGeneratorEvaluation_injective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    {ι : Type uI} (v : ι → V) (K : ι → Subgroup G)
    (hv : ∀ i, v i ∈ fixedVectors ρ (K i))
    (hgen : Submodule.span (MonoidAlgebra ℂ G)
      (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤) :
    Function.Injective (fixedGeneratorEvaluation ρ σ v K hv) := by
  intro f g h
  apply (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).injective
  apply LinearMap.ext_on_range hgen
  intro i
  exact congrArg Subtype.val (congrFun h i)

variable [TopologicalSpace G]

/-- A smooth finite-type source and admissible target have a finite-dimensional
space of all algebraic intertwiners. -/
theorem finite_intertwiningMap_of_finiteType
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule)
    (hσ : IsAdmissible σ) : Module.Finite ℂ (ρ.IntertwiningMap σ) := by
  classical
  let := hfin
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  choose K hK using fun i => hρ (v i)
  let (i : Fin m) : Module.Finite ℂ (fixedVectors σ (K i).toSubgroup) := hσ.2 (K i)
  exact Module.Finite.of_injective
    (fixedGeneratorEvaluation ρ σ v (fun i => (K i).toSubgroup) hK)
    (fixedGeneratorEvaluation_injective ρ σ v (fun i => (K i).toSubgroup) hK hv)

omit [TopologicalSpace G] in
/-- Forget group-algebra linearity, preserving the algebra of endomorphisms. -/
def representationEndForget (ρ : Representation ℂ G V) :
    Module.End (MonoidAlgebra ℂ G) ρ.asModule →ₐ[ℂ] Module.End ℂ V where
  toFun f := ((Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ).symm f).toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Every equivariant endomorphism of an admissible finite-type representation
satisfies a monic polynomial over the coefficient field. -/
theorem isIntegral_intertwiner_of_admissible_finiteType
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule)
    (f : ρ.IntertwiningMap ρ) : IsIntegral ℂ f.toLinearMap := by
  let := finite_intertwiningMap_of_finiteType ρ ρ hρ.1 hfin hρ
  let e := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ
  let : Module.Finite ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) :=
    Module.Finite.equiv e
  exact (IsIntegral.of_finite ℂ (e f)).map (representationEndForget ρ)

/-- In particular, every central group element has a global monic annihilator. -/
theorem isIntegral_centralAction_of_admissible_finiteType
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule)
    (z : G) (hz : z ∈ Submonoid.center G) : IsIntegral ℂ (ρ z) :=
  isIntegral_intertwiner_of_admissible_finiteType ρ hρ hfin
    (Representation.IntertwiningMap.centralMul ρ z hz)

end Langlands
