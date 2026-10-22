import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Degeneration of the hyperext spectral sequence

For an object `K` of the derived category of an abelian category and an
object `W`, the edge map sends a morphism `K ⟶ W⟦n⟧` to the morphism it
induces on cohomology in degree `-n`. The proposition below asserts that the
edge map is bijective when `K` has bounded-above cohomology and `W` has no
higher `Ext` from any cohomology object of `K`. This is the degeneration of
the spectral sequence `Ext^p(H^{-q} K, W) ⇒ Hom(K, W⟦p + q⟧)`. Bijectivity
is a conclusion; it is not supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HyperextDegeneration

/-- The edge map `Hom(K, W⟦n⟧) → Hom(H^{-n} K, W)`: apply the cohomology
functor in degree `-n`, using the shift compatibilities of the cohomology
functors, and identify the cohomology in degree zero of the single complex
`W` with `W`. -/
def edgeMap [HasDerivedCategory.{w} C] (K : DerivedCategory C) (W : C) (n : ℤ) :
    ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n →
      ((DerivedCategory.homologyFunctor C (-n)).obj K ⟶ W) :=
  fun f => (DerivedCategory.homologyFunctor C 0).shiftMap f (-n) 0 (by lia) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app W

end HyperextDegeneration

variable (C) in
/-- Let `K` be an object of the derived category whose cohomology vanishes in
all degrees above some `b`, and let `W` be an object such that
`Ext^i(H^k K, W)` is zero for every degree `k` and every `i > 0`. Then for
every `n` the edge map `Hom(K, W⟦n⟧) → Hom(H^{-n} K, W)` is bijective. -/
def HyperextDegenerationStatement [HasDerivedCategory.{w} C] [HasExt.{w'} C] : Prop :=
  ∀ (K : DerivedCategory C) (b : ℤ),
    (∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) →
    ∀ W : C,
      (∀ (k : ℤ) (i : ℕ), 0 < i →
        Subsingleton (Abelian.Ext.{w'} ((DerivedCategory.homologyFunctor C k).obj K) W i)) →
      ∀ n : ℤ, Function.Bijective (HyperextDegeneration.edgeMap K W n)

end Langlands.Cohomology
