import Langlands.Algebra.NonUnitalModuleDualLeftExactnessProof

/-! Right-to-left categorical bridges for the actual nondegenerate dual functor. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open CategoryTheory

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (hA : IsIdempotented A)

/-- The actual right-to-left functor preserves the inherited pointwise Hom addition. -/
theorem rightToLeft_additive : (rightToLeftFunctor.{uA, uM} hA).Additive := by
  constructor
  intro X Y f g
  apply ObjectProperty.hom_ext
  change fromDoubleOppositeMap
    (pullback hA.op Y.unop.property X.unop.property (f.unop.hom + g.unop.hom)) =
      fromDoubleOppositeMap (pullback hA.op Y.unop.property X.unop.property f.unop.hom) +
      fromDoubleOppositeMap (pullback hA.op Y.unop.property X.unop.property g.unop.hom)
  erw [pullback_add, fromDoubleOppositeMap_add]

local instance : (rightToLeftFunctor.{uA, uM} hA).Additive := rightToLeft_additive hA

/-- An epi of original right modules becomes a mono of the actual transported left duals. -/
theorem rightToLeft_mono_of_epi
    {M N : RightNondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) (hf : Epi f) :
    Mono ((rightToLeftFunctor hA).map f.op) := by
  apply (NondegenerateModuleExactnessConcrete.mono_iff hA _).2
  exact pullback_injective_of_surjective hA.op M.property N.property f.hom
    ((NondegenerateModuleExactnessConcrete.epi_iff hA.op f).1 hf)

/-- A mono of original right modules becomes an epi of the actual transported left duals. -/
theorem rightToLeft_epi_of_mono
    {M N : RightNondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) (hf : Mono f) :
    Epi ((rightToLeftFunctor hA).map f.op) := by
  apply (NondegenerateModuleExactnessConcrete.epi_iff hA _).2
  exact pullback_surjective_of_injective hA.op M.property N.property f.hom
    ((NondegenerateModuleExactnessConcrete.mono_iff hA.op f).1 hf)

/-- Every middle-exact right-module complex reverses under the actual right dual functor. -/
theorem rightToLeft_exact
    (S : ShortComplex (RightNondegenerateModuleCat.{uA, uM} A)) (hS : S.Exact) :
    (S.op.map (rightToLeftFunctor hA)).Exact := by
  have hd := pullback_exact hA.op S.X₁.property S.X₂.property S.X₃.property
    S.f.hom S.g.hom (original_functionExact_of_exact hA.op S hS)
  apply (NondegenerateModuleExactnessConcrete.exact_iff hA _).2
  intro φ hφ
  exact (hd φ).1 hφ

/-- Every short exact right-module complex reverses under the actual right dual functor. -/
theorem rightToLeft_shortExact
    (S : ShortComplex (RightNondegenerateModuleCat.{uA, uM} A)) (hS : S.ShortExact) :
    (S.op.map (rightToLeftFunctor hA)).ShortExact where
  exact := rightToLeft_exact hA S hS.exact
  mono_f := rightToLeft_mono_of_epi hA S.g hS.epi_g
  epi_g := rightToLeft_epi_of_mono hA S.f hS.mono_f

/-- Both one-sided Renard conditions hold for the actual right-to-left functor. -/
theorem rightToLeft_sequenceExact :
    let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
    let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
    Langlands.Renard.ContravariantSequenceExact (rightToLeftFunctor.{uA, uM} hA) := by
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  constructor
  · intro S hS
    refine ⟨?_, ?_⟩
    · exact rightToLeft_exact hA S.unop hS.1.unop
    · let _ := hS.2
      exact rightToLeft_mono_of_epi hA S.f.unop inferInstance
  · intro S hS
    refine ⟨?_, ?_⟩
    · exact rightToLeft_exact hA S.unop hS.1.unop
    · let _ := hS.2
      exact rightToLeft_epi_of_mono hA S.g.unop inferInstance

end Langlands.Algebra.NonUnitalModuleDual
