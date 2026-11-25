/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
public import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverLocalLifting
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentation
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Bounded-below derived evaluation by weakly contractible hypercovers

Source: Stacks Project, proetale.tex, Tag 09A2, lemma-compute-cohomology;
sites-cohomology.tex, Tag 0946, lemma-w-contractible
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

theorem map_eq_of_boundedBelow_homotopy
    {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
    (H : CochainComplex C ℤ ⥤ D)
    (hH : ∀ (K L : CochainComplex.Plus C) (f : K ⟶ L),
      QuasiIso f.hom → IsIso (H.map f.hom))
    (K L : CochainComplex.Plus C) (f g : K.obj ⟶ L.obj) (h : Homotopy f g) :
    H.map f = H.map g := by
  classical
  obtain ⟨n, hn⟩ := K.property
  have := hn
  have hcyl : CochainComplex.IsStrictlyGE K.obj.cylinder (n - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    apply HomologicalComplex.homotopyCofiber.isZero_X
      (biprod.lift (𝟙 K.obj) (-𝟙 K.obj)) q
    · exact IsZero.of_iso (by
        rw [biprod_isZero_iff]
        exact ⟨K.obj.isZero_of_isStrictlyGE n q (by omega),
          K.obj.isZero_of_isStrictlyGE n q (by omega)⟩)
        (HomologicalComplex.biprodXIso K.obj K.obj q)
    · intro r hr
      exact K.obj.isZero_of_isStrictlyGE n r (by
        change q + 1 = r at hr
        omega)
  let P : CochainComplex.Plus C := ⟨K.obj.cylinder, n - 1, hcyl⟩
  let p : P ⟶ K := ⟨HomologicalComplex.cylinder.π K.obj⟩
  have hp : QuasiIso p.hom :=
    (HomologicalComplex.cylinder.homotopyEquiv K.obj (fun q ↦ ⟨q - 1, by simp⟩)).quasiIso_hom
  have := hH P K p hp
  have hi : H.map (HomologicalComplex.cylinder.ι₀ K.obj) =
      H.map (HomologicalComplex.cylinder.ι₁ K.obj) := by
    apply (cancel_mono (H.map p.hom)).mp
    simp only [← H.map_comp]
    change H.map (HomologicalComplex.cylinder.ι₀ K.obj ≫
      HomologicalComplex.cylinder.π K.obj) =
      H.map (HomologicalComplex.cylinder.ι₁ K.obj ≫ HomologicalComplex.cylinder.π K.obj)
    simp only [HomologicalComplex.cylinder.ι₀_π, HomologicalComplex.cylinder.ι₁_π]
  calc
    H.map f = H.map (HomologicalComplex.cylinder.ι₀ K.obj) ≫
        H.map (HomologicalComplex.cylinder.desc f g h) := by
      rw [← H.map_comp, HomologicalComplex.cylinder.ι₀_desc]
    _ = H.map (HomologicalComplex.cylinder.ι₁ K.obj) ≫
        H.map (HomologicalComplex.cylinder.desc f g h) := by rw [hi]
    _ = H.map g := by rw [← H.map_comp, HomologicalComplex.cylinder.ι₁_desc]

end AlgebraicGeometry.Scheme.ProEt
