import Langlands.GroupScheme.Rational.SmoothPTorsionPrimitiveGenerators
import Langlands.GroupScheme.Rational.PointedLaurentCoordinates
import Langlands.GroupScheme.HopfPrimitiveQuotient

/-! # Finite primitive generators in corepresented coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Primitive elements of the coordinate Hopf algebra are additive coordinate
functions on every algebra-valued point of the coordinate cogroup. -/
theorem isPrimitiveFunction_of_isPrimitiveElem {a : hopfAlgebra G}
    (ha : Bialgebra.IsPrimitiveElem k a) :
    Corepresented.IsPrimitiveFunction (corepresentation G) a := by
  intro B x y
  change (x * y).unop.hom a = x.unop.hom a + y.unop.hom a
  exact HopfPrimitive.mul_unop_hom_apply (hopfAlgebra G) ha x y

/-- The primitive-function submodule contains every canonical primitive element. -/
theorem mem_primitiveFunctions_of_isPrimitiveElem {a : hopfAlgebra G}
    (ha : Bialgebra.IsPrimitiveElem k a) :
    a ∈ Corepresented.primitiveFunctions (corepresentation G) :=
  (Corepresented.mem_primitiveFunctions_iff (corepresentation G)).2
    (isPrimitiveFunction_of_isPrimitiveElem G ha)

variable [Smooth G.X.hom] [IsCommMonObj G.X]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Smooth commutative groups killed by the characteristic prime have finite
primitive algebra generators in the corepresented primitive-function submodule. -/
theorem exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent
    (hG : HasUniformPowerExponent G p) :
    ∃ T : Finset (Corepresented.primitiveFunctions (corepresentation G)),
      Algebra.adjoin k (Subtype.val ''
        (T : Set (Corepresented.primitiveFunctions (corepresentation G)))) = ⊤ := by
  classical
  obtain ⟨T, hT⟩ := exists_finite_primitive_generators_of_smooth_uniformExponent G p hG
  let f : {a : hopfAlgebra G // Bialgebra.IsPrimitiveElem k a} →
      Corepresented.primitiveFunctions (corepresentation G) :=
    fun a => ⟨a.val, mem_primitiveFunctions_of_isPrimitiveElem G a.property⟩
  refine ⟨T.image f, ?_⟩
  have himage : (Subtype.val '' ((T.image f : Finset _) : Set
        (Corepresented.primitiveFunctions (corepresentation G)))) =
      Subtype.val '' (T : Set {a : hopfAlgebra G // Bialgebra.IsPrimitiveElem k a}) := by
    ext a
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨f c, ⟨c, hc, rfl⟩, rfl⟩
  rw [himage]
  exact hT

/-- A chosen finite primitive generating set for the coordinate group functor. -/
def finiteCorepresentedPrimitiveGeneratorsOfSmoothUniformExponent
    (hG : HasUniformPowerExponent G p) :
    {T : Finset (Corepresented.primitiveFunctions (corepresentation G)) //
      Algebra.adjoin k (Subtype.val ''
        (T : Set (Corepresented.primitiveFunctions (corepresentation G)))) = ⊤} :=
  ⟨(exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent G p hG).choose,
    (exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent G p hG).choose_spec⟩

end Langlands.GroupScheme.AffineCoordinates
