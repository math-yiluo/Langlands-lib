import Langlands.Cohomology.ExtProjectiveResolution
import Langlands.Cohomology.HyperextAbutmentFiltration
import Langlands.Cohomology.SmoothHyperextSecondPage
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# The degeneration isomorphism of the hyperext spectral sequence

Let `C` be an abelian category, `K` an object of its derived category whose cohomology vanishes
above some degree `b`, and `W` an object of `C` placed in degree `0` as `W₀`. Assume that
`Ext^i(H^k K, W)` vanishes for every `k` and every `i > 0`. Worker 3's proposition
`HyperextDegenerationStatement` asserts that the edge map
`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` is then bijective.

Taking that proposition as a hypothesis `h`, this module packages the edge map as an additive
isomorphism `degenerationAddEquiv h K b hK W hW n`. This is the abstract form of the isomorphism
(5.2) of Harris 1999. Further variants discharge the `Ext` hypothesis:

* `degenerationAddEquivOfInjective`, when `W` is injective (`subsingleton_ext_of_injective`, from
  Mathlib's `Abelian.Ext.subsingleton_of_injective`);
* `degenerationAddEquivOfProjective`, when every cohomology object of `K` is projective (the
  Library's `ExtProjectiveResolution.subsingleton_ext_homology_of_projective`);
* `smoothDegenerationAddEquiv`, for smooth representations, when the smooth Ext groups
  `SmoothExt.ext R G (H^k K) i` evaluated at `W` vanish for `i > 0`
  (`subsingleton_ext_of_smoothExt`, through the Library's comparison
  `ExtRightDerived.smoothExtAddEquiv` of Mathlib's `Ext` with smooth Ext).

This module does not prove `HyperextDegenerationStatement`. Every isomorphism here takes it as
the explicit hypothesis `h`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w' w v u

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

open DerivedCategory

/-- If `W` is injective, `Ext^i(H^k K, W)` vanishes for every `k` and every `i > 0`: the `Ext`
hypothesis of `HyperextDegenerationStatement` holds for `K` and `W`. -/
lemma subsingleton_ext_of_injective (K : DerivedCategory C) (W : C) [Injective W] :
    ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i) := by
  intro k i hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by lia⟩
  exact Abelian.Ext.subsingleton_of_injective _ W m

/-- Given `HyperextDegenerationStatement` (`h`), the edge map
`Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` as an additive isomorphism, for `K` with cohomology vanishing
above `b` (`hK`) and `W` with `Ext^i(H^k K, W) = 0` for `i > 0` (`hW`). -/
def degenerationAddEquiv (h : HyperextDegenerationStatement.{w, w'} C) (K : DerivedCategory C)
    (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n ≃+ ((homologyFunctor C (-n)).obj K ⟶ W) :=
  AddEquiv.ofBijective (edgeMapAddMonoidHom K W n) (h K b hK W hW n)

@[simp]
lemma degenerationAddEquiv_apply (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (W : C) (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    degenerationAddEquiv h K b hK W hW n f = HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- The inverse of `degenerationAddEquiv` is a section of the edge map. -/
@[simp]
lemma edgeMap_degenerationAddEquiv_symm_apply (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (W : C) (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    HyperextDegeneration.edgeMap K W n ((degenerationAddEquiv h K b hK W hW n).symm g) = g :=
  (degenerationAddEquiv h K b hK W hW n).apply_symm_apply g

/-- `degenerationAddEquiv` for an injective object `W`. -/
def degenerationAddEquivOfInjective (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (W : C) [Injective W] (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n ≃+ ((homologyFunctor C (-n)).obj K ⟶ W) :=
  degenerationAddEquiv h K b hK W (subsingleton_ext_of_injective K W) n

/-- `degenerationAddEquiv` when every cohomology object of `K` is projective. -/
def degenerationAddEquivOfProjective (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (hP : ∀ k : ℤ, Projective ((homologyFunctor C k).obj K)) (W : C) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n ≃+ ((homologyFunctor C (-n)).obj K ⟶ W) :=
  degenerationAddEquiv h K b hK W
    (ExtProjectiveResolution.subsingleton_ext_homology_of_projective K hP W) n

end General

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]
  [HasExt.{w'} (SmoothRep.{u, u, u} R G)]

open DerivedCategory

/-- For smooth representations, vanishing of the smooth Ext groups `SmoothExt.ext R G (H^k K) i`
at `W` for `i > 0` gives the `Ext` hypothesis of `HyperextDegenerationStatement`, for any
instance `HasExt.{w'}`. -/
lemma subsingleton_ext_of_smoothExt (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) :
    ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor _ k).obj K) W i) := fun k i hi =>
  have := hW k i hi
  (ExtRightDerived.smoothExtAddEquiv R G ((homologyFunctor _ k).obj K) W i).symm.injective
    |>.subsingleton

/-- `degenerationAddEquiv` for smooth representations, with the `Ext` hypothesis stated with the
smooth Ext groups: `Hom(K, W₀⟦n⟧) ≃+ Hom_G(H^{-n} K, W)`. -/
def smoothDegenerationAddEquiv
    (h : HyperextDegenerationStatement.{w, w'} (SmoothRep.{u, u, u} R G))
    (K : DerivedCategory (SmoothRep.{u, u, u} R G)) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) (W : SmoothRep.{u, u, u} R G)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ) :
    ShiftedHom K ((singleFunctor _ 0).obj W) n ≃+ ((homologyFunctor _ (-n)).obj K ⟶ W) :=
  degenerationAddEquiv h K b hK W (subsingleton_ext_of_smoothExt R G K W hW) n

end Smooth

end HyperextAbutment

end Langlands.Cohomology
