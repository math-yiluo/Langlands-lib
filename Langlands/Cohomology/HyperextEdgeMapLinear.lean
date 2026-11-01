import Langlands.Cohomology.HyperextAbutmentFiltration
import Langlands.Representation.Category.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear

/-!
# Linearity of the cohomology functors and of the hyperext edge map

Let `R` be a ring and `C` an `R`-linear abelian category. Mathlib makes the derived category
of `C` an `R`-linear category, with `R`-linear localization, shift and single functors, but it
does not record that the cohomology functors are `R`-linear. This module supplies:

* `R`-linearity of the functors `HomologicalComplex.shortComplexFunctor'`,
  `HomologicalComplex.shortComplexFunctor` and `HomologicalComplex.homologyFunctor` on
  homological complexes (instances), and of the cohomology functors
  `DerivedCategory.homologyFunctor C n` on the derived category (instance
  `homologyFunctor_linear`, deduced from the factorization through the localization functor
  `DerivedCategory.Q`);
* `R`-linearity of the edge map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` of
  `HyperextDegenerationStatement` (`edgeMap_smul`, `edgeMapLinearMap`), where `W₀` is `W`
  placed in degree `0`;
* the degeneration isomorphism as an `R`-linear equivalence (`degenerationLinearEquiv`), taking
  Worker 3's proposition `HyperextDegenerationStatement` as the explicit hypothesis `h`; this
  module does not prove it;
* the edge map for smooth representations as an `R`-linear map (`smoothEdgeMapLinearMap`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w w' v u t uι

section Complexes

variable (R : Type t) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type uι} (c : ComplexShape ι)

/-- The functor sending a homological complex `K` to the short complex
`K.X i ⟶ K.X j ⟶ K.X k` is `R`-linear. -/
instance shortComplexFunctor'_linear (i j k : ι) :
    (HomologicalComplex.shortComplexFunctor' C c i j k).Linear R where
  map_smul f r := by
    ext <;> rfl

/-- The functor sending a homological complex to its short complex at `i` is `R`-linear. -/
instance shortComplexFunctor_linear (i : ι) :
    (HomologicalComplex.shortComplexFunctor C c i).Linear R :=
  inferInstanceAs ((HomologicalComplex.shortComplexFunctor' C c _ i _).Linear R)

/-- The homology functor of homological complexes in degree `i` is `R`-linear. -/
instance homologicalComplexHomologyFunctor_linear [CategoryWithHomology C] (i : ι) :
    (HomologicalComplex.homologyFunctor C c i).Linear R :=
  Functor.linear_of_iso _ (HomologicalComplex.homologyFunctorIso C c i).symm

end Complexes

section Derived

variable (R : Type t) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

open DerivedCategory

/-- The cohomology functor `H^n : DerivedCategory C ⥤ C` is `R`-linear. -/
instance homologyFunctor_linear (n : ℤ) : (homologyFunctor C n).Linear R := by
  let : Localization.Lifting Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n) :=
    ⟨homologyFunctorFactors C n⟩
  exact (Localization.functor_linear_iff Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n)).1
      inferInstance

variable {R C}

/-- The edge map commutes with multiplication by scalars of `R`. -/
lemma edgeMap_smul (K : DerivedCategory C) (W : C) (n : ℤ) (r : R)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap K W n (r • f) = r • HyperextDegeneration.edgeMap K W n f := by
  have : ((homologyFunctor C 0).shift (-n)).Linear R :=
    inferInstanceAs ((homologyFunctor C (-n)).Linear R)
  simp only [HyperextDegeneration.edgeMap, Functor.shiftMap, Functor.map_smul]
  exact (congrArg (· ≫ _) (Linear.smul_comp _ _ _ _ _ _)).trans (Linear.smul_comp _ _ _ _ _ _)

variable (R) in
/-- The edge map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` as an `R`-linear map. -/
def edgeMapLinearMap (K : DerivedCategory C) (W : C) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n →ₗ[R] ((homologyFunctor C (-n)).obj K ⟶ W) where
  toFun := HyperextDegeneration.edgeMap K W n
  map_add' := (edgeMapAddMonoidHom K W n).map_add
  map_smul' r f := edgeMap_smul K W n r f

@[simp]
lemma edgeMapLinearMap_apply (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    edgeMapLinearMap R K W n f = HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- The underlying additive map of `edgeMapLinearMap` is `edgeMapAddMonoidHom`. -/
lemma edgeMapLinearMap_toAddMonoidHom (K : DerivedCategory C) (W : C) (n : ℤ) :
    (edgeMapLinearMap R K W n).toAddMonoidHom = edgeMapAddMonoidHom K W n :=
  rfl

variable [HasExt.{w'} C]

variable (R) in
/-- Given `h : HyperextDegenerationStatement`, the edge map is an `R`-linear equivalence
`Hom(K, W₀⟦n⟧) ≃ₗ[R] Hom(H^{-n} K, W)` when the cohomology of `K` vanishes above `b` and
`Ext^i(H^k K, W)` vanishes for all `k` and all `i > 0`. -/
def degenerationLinearEquiv (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (W : C) (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n ≃ₗ[R] ((homologyFunctor C (-n)).obj K ⟶ W) :=
  LinearEquiv.ofBijective (edgeMapLinearMap R K W n) (h K b hK W hW n)

@[simp]
lemma degenerationLinearEquiv_apply (h : HyperextDegenerationStatement.{w, w'} C)
    (K : DerivedCategory C) (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    (W : C) (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    degenerationLinearEquiv R h K b hK W hW n f = HyperextDegeneration.edgeMap K W n f :=
  rfl

end Derived

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]

open DerivedCategory

/-- For smooth representations of `G` over the commutative ring `R`, the edge map
`Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` as an `R`-linear map, using the Library's `R`-linear
structure on `SmoothRep R G`. -/
def smoothEdgeMapLinearMap (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) (n : ℤ) :
    ShiftedHom K ((singleFunctor _ 0).obj W) n →ₗ[R] ((homologyFunctor _ (-n)).obj K ⟶ W) :=
  edgeMapLinearMap R K W n

@[simp]
lemma smoothEdgeMapLinearMap_apply (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) (n : ℤ) (f : ShiftedHom K ((singleFunctor _ 0).obj W) n) :
    smoothEdgeMapLinearMap R G K W n f = HyperextDegeneration.edgeMap K W n f :=
  rfl

end Smooth

end HyperextAbutment

end Langlands.Cohomology
