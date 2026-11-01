import Langlands.Algebra.NonUnitalModuleDualMapExactnessProof
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Concrete bridges for the actual left-to-right nondegenerate dual functor. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open CategoryTheory

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)

/-- The actual functor preserves the inherited pointwise addition of intertwiners. -/
theorem leftToRight_additive : (leftToRightFunctor.{uA, uM} hA).Additive := by
  constructor
  intro X Y f g
  apply ObjectProperty.hom_ext
  exact pullback_add hA Y.unop.property X.unop.property f.unop.hom g.unop.hom

local instance : (leftToRightFunctor.{uA, uM} hA).Additive := leftToRight_additive hA

omit [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
include hA in
/-- The categorical concrete criterion gives exactness of the original functions. -/
theorem original_functionExact_of_exact
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) (hS : S.Exact) :
    Function.Exact S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom := by
  intro y
  constructor
  · exact (NondegenerateModuleExactnessConcrete.exact_iff hA S).1 hS y
  · rintro ⟨x, rfl⟩
    exact congrArg (fun k => k.hom.toAddMonoidHom x) S.zero

/-- Every middle-exact complex reverses under the actual left-to-right dual. -/
theorem leftToRight_exact
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) (hS : S.Exact) :
    (S.op.map (leftToRightFunctor hA)).Exact := by
  apply (NondegenerateModuleExactnessConcrete.exact_iff hA.op _).2
  let _ := fullAction hA S.X₁.property
  let _ := fullAction hA S.X₂.property
  let _ := fullAction hA S.X₃.property
  have h := pullback_exact hA S.X₁.property S.X₂.property S.X₃.property
    S.f.hom S.g.hom (original_functionExact_of_exact hA S hS)
  intro y hy
  exact (h y).1 hy

/-- An original epimorphism reverses to a monomorphism. -/
theorem leftToRight_mono_of_epi
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) (hf : Epi f) :
    Mono ((leftToRightFunctor hA).map f.op) := by
  apply (NondegenerateModuleExactnessConcrete.mono_iff hA.op _).2
  let _ := fullAction hA M.property
  let _ := fullAction hA N.property
  exact pullback_injective_of_surjective hA M.property N.property f.hom
    ((NondegenerateModuleExactnessConcrete.epi_iff hA f).1 hf)

/-- An original monomorphism reverses to an epimorphism. -/
theorem leftToRight_epi_of_mono
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) (hf : Mono f) :
    Epi ((leftToRightFunctor hA).map f.op) := by
  apply (NondegenerateModuleExactnessConcrete.epi_iff hA.op _).2
  let _ := fullAction hA M.property
  let _ := fullAction hA N.property
  exact pullback_surjective_of_injective hA M.property N.property f.hom
    ((NondegenerateModuleExactnessConcrete.mono_iff hA f).1 hf)

/-- Every short exact complex reverses under the actual left-to-right dual. -/
theorem leftToRight_shortExact
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) (hS : S.ShortExact) :
    (S.op.map (leftToRightFunctor hA)).ShortExact where
  exact := leftToRight_exact hA S hS.exact
  mono_f := leftToRight_mono_of_epi hA S.g hS.epi_g
  epi_g := leftToRight_epi_of_mono hA S.f hS.mono_f

/-- Both of Renard's one-sided sequence conditions hold on the opposite category. -/
theorem leftToRight_sequenceExact :
    let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
    let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
    Langlands.Renard.ContravariantSequenceExact (leftToRightFunctor.{uA, uM} hA) := by
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  constructor
  · intro S hS
    refine ⟨?_, ?_⟩
    · exact leftToRight_exact hA S.unop hS.1.unop
    · let _ := hS.2
      exact leftToRight_mono_of_epi hA S.f.unop inferInstance
  · intro S hS
    refine ⟨?_, ?_⟩
    · exact leftToRight_exact hA S.unop hS.1.unop
    · let _ := hS.2
      exact leftToRight_epi_of_mono hA S.g.unop inferInstance

end Langlands.Algebra.NonUnitalModuleDual
