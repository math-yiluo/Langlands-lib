import Langlands.Algebra.NonUnitalSchurStatements
import Langlands.Algebra.NonUnitalSimplicityProof
import Langlands.Algebra.SchurProof

/-!
# Proof of Renard B.II for the original nonunital action

This proves `Langlands.Renard.NonUnitalSchurStatement.{uA, uM}` from
`Langlands.Algebra.NonUnitalSchurStatements`. The published simplicity reductions turn
original additive simplicity into a nonzero action, simplicity of the actual unitized module
`CompatibleUnitization.module ρ` and complex linearity of every additive original
endomorphism. Each such endomorphism therefore lies in the actual centralizer, and the
categorical endomorphism ring is isomorphic to `CompatibleUnitization.centralizer ρ`. The
published unital Schur proofs apply to the unitized module; `endAlgEquiv ρ` carries them back.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Renard

open Langlands.Algebra
open Langlands.Algebra.CompatibleUnitization

universe uA uM

namespace NonUnitalSchur

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [Module ℂ M]

/-! ### Linear maps from the actual action -/

section Maps

variable (ρ : A →ₙₐ[ℂ] Module.End ℂ M)

/-- The complex-linear original orbit map `a ↦ ρ a m`. -/
def orbitMap (m : M) : A →ₗ[ℂ] M where
  toFun a := ρ a m
  map_add' a b := by rw [map_add, LinearMap.add_apply]
  map_smul' c a := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
@[simp] theorem orbitMap_apply (m : M) (a : A) : orbitMap ρ m a = ρ a m := rfl

/-- The complex-linear evaluation map `g ↦ g m` on the actual centralizer. -/
def evaluationMap (m : M) : centralizer ρ →ₗ[ℂ] M where
  toFun g := (g : Module.End ℂ M) m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
@[simp] theorem evaluationMap_apply (m : M) (g : centralizer ρ) :
    evaluationMap ρ m g = (g : Module.End ℂ M) m := rfl

/-- The additive original endomorphism underlying an element of the centralizer. -/
def ofCentralizer (g : centralizer ρ) :
    letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom A M M :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  { toAddMonoidHom := (g : Module.End ℂ M).toAddMonoidHom
    map_smul' a m := (mem_centralizer_iff ρ).1 g.2 a m }

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
@[simp] theorem ofCentralizer_apply (g : centralizer ρ) (m : M) :
    (letI := NonUnitalModule.ofLinearEndHom ρ; ofCentralizer ρ g m) =
      (g : Module.End ℂ M) m := rfl

end Maps

/-! ### Consequences of original additive simplicity -/

section Simple

variable (ρ : A →ₙₐ[ℂ] Module.End ℂ M)
  (hs : letI := NonUnitalModule.ofLinearEndHom ρ;
    Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)

include hs

/-- The original action of an additively simple complex module is nonzero. -/
theorem action_ne_zero : ρ ≠ 0 :=
  complexAdditiveSimpleActionNonzero ρ hs

/-- The actual unitized module of an additively simple original module is simple. -/
theorem unitized_isSimpleModule : letI := module ρ; IsSimpleModule (Unitization ℂ A) M :=
  additiveSimpleUnitization ρ hs

/-- Every additive original endomorphism preserves complex scalars. -/
theorem map_complex_smul :
    letI := NonUnitalModule.ofLinearEndHom ρ
    ∀ (f : NonUnitalModuleHom A M M) (c : ℂ) (m : M), f (c • m) = c • f m :=
  simpleUnitizationIntertwiner ρ (action_ne_zero ρ hs) (unitized_isSimpleModule ρ hs) M ρ

/-- The complex-linear map underlying an additive original endomorphism. -/
def linearMapOf (f : letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom A M M) :
    Module.End ℂ M :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  { toFun := f
    map_add' := f.map_add
    map_smul' := map_complex_smul ρ hs f }

theorem linearMapOf_mem_centralizer
    (f : letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom A M M) :
    linearMapOf ρ hs f ∈ centralizer ρ :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (mem_centralizer_iff ρ).2 fun a m => f.map_smul' a m

/-- The element of the actual centralizer with the same underlying function. -/
def toCentralizer (f : letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom A M M) :
    centralizer ρ :=
  ⟨linearMapOf ρ hs f, linearMapOf_mem_centralizer ρ hs f⟩

@[simp] theorem toCentralizer_apply
    (f : letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom A M M) (m : M) :
    (toCentralizer ρ hs f : Module.End ℂ M) m = (letI := NonUnitalModule.ofLinearEndHom ρ; f m) :=
  rfl

/-- The actual categorical endomorphism ring is the actual centralizer. -/
def endRingEquiv :
    letI := NonUnitalModule.ofLinearEndHom ρ
    End (NonUnitalModuleCat.of A M) ≃+* centralizer ρ :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  { toFun f := toCentralizer ρ hs f
    invFun g := ofCentralizer ρ g
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }

/-- The actual categorical endomorphism ring is the unitized module's endomorphism ring. -/
def unitizedEndRingEquiv :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := module ρ
    End (NonUnitalModuleCat.of A M) ≃+* Module.End (Unitization ℂ A) M :=
  letI := module ρ
  letI := isScalarTower ρ
  letI := smulCommClass' ρ
  (endRingEquiv ρ hs).trans (endAlgEquiv ρ).toRingEquiv

theorem unitizedEndRingEquiv_apply
    (f : letI := NonUnitalModule.ofLinearEndHom ρ; End (NonUnitalModuleCat.of A M)) (m : M) :
    (letI := NonUnitalModule.ofLinearEndHom ρ; letI := module ρ;
      unitizedEndRingEquiv ρ hs f m) =
      (letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalModuleHom.toAddMonoidHom f m) :=
  rfl

end Simple

end NonUnitalSchur

open NonUnitalSchur

/-! ### The nine components -/

section Components

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [Module ℂ M]

/-- **Renard B.II a).** The categorical endomorphism ring of an additively simple original
module is a division ring. -/
theorem nonUnitalSchurEndDivision (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurEndDivisionStatement ρ := by
  intro hs
  let _inst := module ρ
  obtain ⟨hnt, hunit⟩ := schurEndDivision (Unitization ℂ A) M (unitized_isSimpleModule ρ hs)
  let e := unitizedEndRingEquiv ρ hs
  refine ⟨e.surjective.nontrivial, fun f hf => ?_⟩
  exact (MulEquiv.isUnit_map e).1 (hunit (e f) ((map_ne_zero_iff e e.injective).2 hf))

/-- **Renard B.II, kernel/image step.** A nonzero additive original endomorphism of an
additively simple original module is bijective. -/
theorem nonUnitalSchurEndBijective (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurEndBijectiveStatement ρ := by
  intro hs f hf
  let _inst := module ρ
  let e := unitizedEndRingEquiv ρ hs
  exact schurEndBijective (Unitization ℂ A) M (unitized_isSimpleModule ρ hs) (e f)
    ((map_ne_zero_iff e e.injective).2 hf)

/-- Every additive original endomorphism is a unique element of the actual centralizer. -/
theorem nonUnitalSchurEndComparison (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurEndComparisonStatement ρ := by
  intro hs f
  exact ⟨toCentralizer ρ hs f, fun _ => rfl, fun g hg => Subtype.ext (LinearMap.ext hg)⟩

/-- **Renard B.II, cyclic map.** The original orbit map at a nonzero vector is surjective. -/
theorem nonUnitalSchurCyclicMapSurjective (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurCyclicMapSurjectiveStatement ρ := fun hs =>
  simpleUnitizationOrbit ρ (action_ne_zero ρ hs) (unitized_isSimpleModule ρ hs)

/-- **Renard B.II, evaluation.** Evaluation of the actual centralizer at a nonzero vector is
injective. -/
theorem nonUnitalSchurEvaluationInjective (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurEvaluationInjectiveStatement ρ := by
  intro hs m hm g₁ g₂ h
  let _inst := module ρ
  let _inst₂ := isScalarTower ρ
  let _inst₃ := smulCommClass' ρ
  exact (endAlgEquiv ρ).injective
    (schurEvaluationInjective (Unitization ℂ A) M (unitized_isSimpleModule ρ hs) m hm h)

/-- **Renard B.II, final sentence, first step.** Countable dimension of the original algebra
bounds the dimension of an additively simple original module. -/
theorem nonUnitalSchurModuleRankCountable (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurModuleRankCountableStatement ρ := by
  intro hs hA
  have := hs.1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have h := LinearMap.lift_rank_le_of_surjective (orbitMap ρ m)
    (nonUnitalSchurCyclicMapSurjective ρ hs m hm)
  rw [← Cardinal.lift_le_aleph0.{uM, uA}]
  exact h.trans (Cardinal.lift_le_aleph0.2 hA)

/-- **Renard B.II, proof of b).** Countable dimension of the module bounds the dimension of
the actual centralizer. -/
theorem nonUnitalSchurEndRankCountable (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurEndRankCountableStatement ρ := by
  intro hs hM
  have := hs.1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact (LinearMap.rank_le_of_injective (evaluationMap ρ m)
    (nonUnitalSchurEvaluationInjective ρ hs m hm)).trans hM

/-- Bijectivity of the centralizer's scalar map makes every additive original endomorphism
multiplication by a unique complex scalar. -/
theorem NonUnitalSchur.existsUnique_smul_of_bijective (ρ : A →ₙₐ[ℂ] Module.End ℂ M)
    (hs : letI := NonUnitalModule.ofLinearEndHom ρ;
      Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)
    (hb : Function.Bijective (algebraMap ℂ (centralizer ρ))) :
    letI := NonUnitalModule.ofLinearEndHom ρ
    ∀ f : NonUnitalModuleHom A M M, ∃! z : ℂ, ∀ m : M, f m = z • m := by
  let _inst := NonUnitalModule.ofLinearEndHom ρ
  intro f
  obtain ⟨z, hz⟩ := hb.2 (toCentralizer ρ hs f)
  have hrep : ∀ w : ℂ, (∀ m : M, f m = w • m) →
      algebraMap ℂ (centralizer ρ) w = toCentralizer ρ hs f :=
    fun w hw => Subtype.ext (LinearMap.ext fun m => (hw m).symm)
  refine ⟨z, fun m => ?_, fun w hw => hb.1 ((hrep w hw).trans hz.symm)⟩
  rw [← toCentralizer_apply ρ hs f m, ← hz]
  rfl

/-- Bijectivity of the centralizer's actual scalar map under module countability. -/
theorem NonUnitalSchur.algebraMap_bijective (ρ : A →ₙₐ[ℂ] Module.End ℂ M)
    (hs : letI := NonUnitalModule.ofLinearEndHom ρ;
      Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)
    (hM : Module.rank ℂ M ≤ Cardinal.aleph0) :
    Function.Bijective (algebraMap ℂ (centralizer ρ)) := by
  let _inst := module ρ
  let _inst₂ := isScalarTower ρ
  let _inst₃ := smulCommClass' ρ
  have h := schurScalarOfModuleRankCountable (Unitization ℂ A) M
    (unitized_isSimpleModule ρ hs) hM
  have heq : ⇑(algebraMap ℂ (centralizer ρ)) =
      ⇑(endAlgEquiv ρ).symm ∘ ⇑(algebraMap ℂ (Module.End (Unitization ℂ A) M)) :=
    funext fun c => ((endAlgEquiv ρ).symm.commutes c).symm
  rw [heq]
  exact (endAlgEquiv ρ).symm.bijective.comp h

/-- **Renard B.II b).** Under module countability, the centralizer's actual scalar map is
bijective and every additive original endomorphism is a unique complex scalar. -/
theorem nonUnitalSchurScalarOfModuleRankCountable (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurScalarOfModuleRankCountableStatement ρ := by
  intro hs hM
  have hb := NonUnitalSchur.algebraMap_bijective ρ hs hM
  exact ⟨hb, NonUnitalSchur.existsUnique_smul_of_bijective ρ hs hb⟩

/-- **Renard B.II b), final sentence.** Countable dimension of the original algebra suffices. -/
theorem nonUnitalSchurScalarOfAlgebraRankCountable (ρ : A →ₙₐ[ℂ] Module.End ℂ M) :
    NonUnitalSchurScalarOfAlgebraRankCountableStatement ρ := fun hs hA =>
  nonUnitalSchurScalarOfModuleRankCountable ρ hs (nonUnitalSchurModuleRankCountable ρ hs hA)

end Components

/-! ### The aggregate -/

/-- **Renard B.II for the original nonunital action**, with all nine components. -/
theorem nonUnitalSchur : NonUnitalSchurStatement.{uA, uM} := fun ρ =>
  ⟨nonUnitalSchurEndDivision ρ, nonUnitalSchurEndBijective ρ, nonUnitalSchurEndComparison ρ,
    nonUnitalSchurCyclicMapSurjective ρ, nonUnitalSchurEvaluationInjective ρ,
    nonUnitalSchurModuleRankCountable ρ, nonUnitalSchurEndRankCountable ρ,
    nonUnitalSchurScalarOfModuleRankCountable ρ, nonUnitalSchurScalarOfAlgebraRankCountable ρ⟩

end Langlands.Renard
