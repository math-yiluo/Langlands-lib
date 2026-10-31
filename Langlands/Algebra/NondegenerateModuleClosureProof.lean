import Langlands.Algebra.NondegenerateModuleClosureStatements
import Langlands.Algebra.NonUnitalModuleProducts
import Langlands.Algebra.NonUnitalModuleSubobject

/-!
# Closure of nondegenerate original modules

Renard I.1.2 supplies subobject and quotient closure. Zero containment and
finite-product closure are derived explicitly for the actual full subcategory.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory CategoryTheory.Limits ZeroObject

universe uA uM

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A]

/-- An ambient zero object has a trivial carrier and is nondegenerate. -/
theorem isNondegenerate_of_isZero (Z : NonUnitalModuleCat.{uA, uM} A)
    (hZ : IsZero Z) : IsNondegenerate A Z := by
  intro z
  have hz : z = 0 :=
    congrArg (fun f : Z ⟶ Z => f.toAddMonoidHom z) (hZ.eq_of_src (𝟙 Z) 0)
  exact ⟨⟨0, IsIdempotentElem.zero⟩, by rw [hz, smul_zero]⟩

/-- The original nondegenerate object property contains an ambient zero object. -/
theorem nondegenerateProperty_containsZero :
    (nondegenerateProperty.{uA, uM} A).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isNondegenerate_of_isZero 0 (isZero_zero _)⟩

/-- Restrict the same fixing idempotent along an injective original map. -/
theorem nondegenerateProperty_isClosedUnderSubobjects :
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    intro x
    obtain ⟨e, he⟩ := hY (f.toAddMonoidHom x)
    refine ⟨e, (mono_iff_injective f).1 inferInstance ?_⟩
    exact (f.map_smul (e : A) x).trans he

/-- Lift a vector through the unchanged surjective original additive map. -/
theorem nondegenerateProperty_isClosedUnderQuotients :
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    have hs : Function.Surjective f.toAddMonoidHom := by
      have hf : Epi ((IntegerUnitization.equivalence A).functor.map f) := inferInstance
      exact (ModuleCat.epi_iff_surjective _).1 hf
    intro y
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨e, he⟩ := hX x
    exact ⟨e, (f.map_smul (e : A) x).symm.trans (congrArg f.toAddMonoidHom he)⟩

/-- One common finite upper bound fixes every coordinate simultaneously. -/
theorem isNondegenerate_concreteProduct (hA : IsIdempotented A)
    {I : Type} [Finite I] (M : I → NonUnitalModuleCat.{uA, uM} A)
    (hM : ∀ i, IsNondegenerate A (M i)) :
    IsNondegenerate A (concreteProduct M) := by
  classical
  intro m
  choose e he using fun i => hM i (m i)
  obtain ⟨f, hf⟩ := hA.finite_family_upper_bound e
  exact ⟨f, funext fun i => Idempotent.smul_eq_of_le (hf i) (he i)⟩

/-- Every limiting finite fan embeds by its original legs into the
coordinatewise product, whose vectors have a common fixing idempotent. -/
theorem nondegenerateProperty_isClosedUnderFiniteProducts (hA : IsIdempotented A) :
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape I _ := by
    let := nondegenerateProperty_isClosedUnderSubobjects.{uA, uM} (A := A)
    refine ⟨?_⟩
    rintro X ⟨p⟩
    let M : I → NonUnitalModuleCat.{uA, uM} A := fun i => p.diag.obj ⟨i⟩
    let f : X ⟶ concreteProduct M := concreteProductLift M (fun i => p.π.app ⟨i⟩)
    have hf : Mono f := by
      refine ⟨fun g h w => ?_⟩
      apply p.isLimit.hom_ext
      intro j
      have hw := congrArg (fun k => k ≫ concreteProductπ M j.as) w
      simpa only [f, Category.assoc, concreteProductLift_π] using hw
    exact (nondegenerateProperty A).prop_of_mono f
      (isNondegenerate_concreteProduct hA M (fun i => p.prop_diag_obj ⟨i⟩))

end NonUnitalModuleCat

/-- The entire closed proposition, without extra assumptions. -/
theorem nondegenerateModuleClosureStatement :
    NondegenerateModuleClosureStatement.{uA, uM} := by
  intro A _ hA
  exact ⟨NonUnitalModuleCat.nondegenerateProperty_containsZero,
    NonUnitalModuleCat.nondegenerateProperty_isClosedUnderSubobjects,
    NonUnitalModuleCat.nondegenerateProperty_isClosedUnderQuotients,
    NonUnitalModuleCat.nondegenerateProperty_isClosedUnderFiniteProducts hA⟩

example : NondegenerateModuleClosureStatement.{uA, uM} :=
  @nondegenerateModuleClosureStatement.{uA, uM}

example : NondegenerateModuleClosureStatement.{0, 1} :=
  nondegenerateModuleClosureStatement.{0, 1}

example : NondegenerateModuleClosureStatement.{1, 0} :=
  nondegenerateModuleClosureStatement.{1, 0}

end Langlands.Algebra
