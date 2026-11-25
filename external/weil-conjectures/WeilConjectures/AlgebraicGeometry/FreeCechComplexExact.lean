/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible
import WeilConjectures.AlgebraicGeometry.FreeCechComplexDecomposition

/-!
# Exactness of the free Čech complex on the small étale site

Source: Stacks Project, sites-cohomology.tex, Lemma 03F5
(blueprint: lem-weil-pbc-free-cech-complex-exact).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The chain complex `K_• = 𝒪_{𝒰,•}` of presheaves of `𝒪`-modules of the family
`𝒰 = {f i : U i ⟶ U₀}` of `X_ét` is exact in positive degrees, evaluated at every object `W`.
Here `K_•` is the alternating face map complex of the Čech nerve of the family
`i ↦ Over.mk (f i)` in `Over U₀` (`FormalCoproduct.cech`, the construction under the recorded
`cechComplexFunctor`; finite products in `Over U₀` are the fibre products
`U i₀ ×_{U₀} ⋯ ×_{U₀} U iₚ`, faces are the projections deleting a factor), sent to presheaves
of `𝒪`-modules by `V ↦ 𝒪_V = PresheafOfModules.free 𝒪 (yoneda V)` on summands and direct
sums on formal coproducts. Degree `p + 1` with `p : ℕ` runs over all positive degrees.
Source: Stacks Project, sites-cohomology.tex, Lemma 03F5, with Lemmas 03AS and 03AT.
(blueprint: lem-weil-pbc-free-cech-complex-exact)

Proof: (1) Evaluate at `W`: `K_p(W)` is the free `𝒪(W)`-module on the disjoint union over
`(i₀,…,iₚ)` of `Mor(W, U i₀ ×_{U₀} ⋯ ×_{U₀} U iₚ)`. (2) Group the basis by the common
composite `φ : W ⟶ U₀`; projections preserve `φ`, and by the universal property of the fibre
product the part over `φ` is `S_φ^{p+1}` with `S_φ = ∐ᵢ {g : W ⟶ U i | g ≫ f i = φ}`, faces
deleting a coordinate. (3) Free modules turn disjoint unions into direct sums compatibly with
the differentials, and homology commutes with direct sums. (4) An empty `S_φ` contributes zero;
for a nonempty `S_φ`, prepending a fixed `s ∈ S_φ` is a contracting homotopy of the augmented
complex (lem-weil-pbc-power-set-complex-contractible), so its positive homology vanishes. -/
theorem freeCechComplex_exact (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) (p : ℕ) :
    (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)))).ExactAt (p + 1) := by
  classical
  apply (freeCechComplex_exact_iff_fibres X ι U₀ U f O W p).2
  intro φ
  let S := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
  have h := Algebra.powerSetComplex_contractible (O.obj (op W)) S
  by_cases hS : Nonempty S
  · exact (h.2.2.2.1 hS).1 p
  · have : IsEmpty S := not_nonempty_iff.mp hS
    have : Subsingleton (Algebra.powerSetComplexObject (O.obj (op W)) S (p + 1)) :=
      h.2.2.1 inferInstance (p + 1)
    exact Subsingleton.elim _ _

end AlgebraicGeometry
