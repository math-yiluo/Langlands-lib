import Langlands.Cohomology.Continuous.InnerConjugation

/-!
# The continuous degree-two inner-conjugation prism

For a compact topological group `G`, a topological representation `A` and `t : G`, this module
sends a homogeneous continuous two-cochain `f` to the homogeneous continuous one-cochain
`(x, y) ↦ f(x, x t, y t) - f(x, y, y t)`. Local compactness of `G` (from compactness, since
topological groups are R₁) is used to uncurry the nested continuous maps. No Hausdorff
hypothesis is needed.
-/

universe u v w

namespace Langlands.Continuous

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : TopRep.{max v w} k G)

/-- The nested continuous map `x ↦ y ↦ F x (x * t) (y * t) - F x y (y * t)` attached to a
nested continuous map `F` of three variables. It is built by uncurrying `F` to a continuous map
on `(G × G) × G`, substituting, and currying back. Uncurrying uses local compactness of `G`. -/
def innerConjugationPrismMap (t : G) (F : C(G, C(G, C(G, A)))) : C(G, C(G, A)) :=
  ContinuousMap.curry
    (F.uncurry.uncurry.comp ⟨fun p : G × G => ((p.1, p.1 * t), p.2 * t), by fun_prop⟩ -
      F.uncurry.uncurry.comp ⟨fun p : G × G => ((p.1, p.2), p.2 * t), by fun_prop⟩)

@[simp]
theorem innerConjugationPrismMap_apply (t : G) (F : C(G, C(G, C(G, A)))) (x y : G) :
    innerConjugationPrismMap A t F x y = F x (x * t) (y * t) - F x y (y * t) := rfl

/-- The prism map sends a homogeneous (diagonally invariant) degree-two cochain to a
diagonally invariant nested map of two variables. -/
theorem innerConjugationPrismMap_mem_invariants (t : G)
    (f : (TopRep.homogeneousCochains A).X 2) :
    innerConjugationPrismMap A t f.1 ∈ (TopRep.resolutionX A 2).ρ.invariants := by
  intro g
  have hf : ∀ x y z : G, A.ρ g (f.1 (g⁻¹ * x) (g⁻¹ * y) (g⁻¹ * z)) = f.1 x y z :=
    fun x y z => congrArg (fun F : TopRep.resolutionX A 3 => F x y z) (f.property g)
  ext x y
  change A.ρ g (innerConjugationPrismMap A t f.1 (g⁻¹ * x) (g⁻¹ * y)) =
    innerConjugationPrismMap A t f.1 x y
  rw [innerConjugationPrismMap_apply, innerConjugationPrismMap_apply, map_sub, mul_assoc,
    mul_assoc, hf, hf]

/-- The degree-two inner-conjugation prism: the homogeneous continuous one-cochain
`(x, y) ↦ f(x, x t, y t) - f(x, y, y t)` attached to a homogeneous continuous two-cochain `f`. -/
def innerConjugationPrism (t : G) (f : (TopRep.homogeneousCochains A).X 2) :
    (TopRep.homogeneousCochains A).X 1 :=
  ⟨innerConjugationPrismMap A t f.1, innerConjugationPrismMap_mem_invariants A t f⟩

theorem innerConjugationPrism_coe (t : G) (f : (TopRep.homogeneousCochains A).X 2) :
    (innerConjugationPrism A t f).1 = innerConjugationPrismMap A t f.1 := rfl

/-- The pointwise formula for the degree-two inner-conjugation prism. -/
theorem innerConjugationPrism_apply (t : G) (f : (TopRep.homogeneousCochains A).X 2)
    (x y : G) :
    (innerConjugationPrism A t f).1 x y = f.1 x (x * t) (y * t) - f.1 x y (y * t) := rfl

end Langlands.Continuous
