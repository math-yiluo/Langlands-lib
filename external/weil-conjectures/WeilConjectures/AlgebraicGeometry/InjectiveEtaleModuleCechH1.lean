/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.InjectiveEtaleConstantRingModule
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Degree-one Čech acyclicity of injective étale module sheaves

Source: Stacks Project, Cohomology on Sites, Lemma 03FC, used in Lemma 03FD.
(blueprint: lem-weil-pbc-injective-etale-module-cech-h1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The underlying abelian presheaf of an injective module sheaf has vanishing Čech H¹
on every étale covering, including coverings with an infinite index set.

Source: Stacks Project, Cohomology on Sites, Lemma 03FC
(lemma-injective-module-trivial-cech), proof, and Lemma 03FD, second paragraph.
(blueprint: lem-weil-pbc-injective-etale-module-cech-h1)

Proof: Let O be the constant ring sheaf associated to Λ. Extend the constant Λ-action
on J to O locally and glue; this identifies sheaves valued in Λ-modules with sheaves
of O-modules, preserving injectivity and the underlying abelian sheaf. Sheafification
of module presheaves is exact and left adjoint to inclusion, so J is injective among
module presheaves (03FB). For the covering V → U, form the free O-module presheaf
chain complex K on its iterated fibre products, with alternating deletion maps.
Evaluated at W, partition its basis by the composite W → U. In each summand the basis
in degree p consists of (p+1)-tuples of lifts of that composite to the covering. If
there are no lifts all terms are zero; otherwise adjoining a chosen lift contracts
the complex in positive degree (03F5). Thus K is exact in positive degree. Yoneda
identifies Hom(K_p, J) with the product of sections on the corresponding fibre
products. Under this identification precomposition by deletion is restriction, so
the Hom complex is the Čech complex, including its differential. Exactness of Hom
into the injective module presheaf makes its positive cohomology zero (03FC).
Forgetting scalars changes neither sections nor restrictions (03FD). The resulting
complex is the stated `cechComplexFunctor` complex in the slice Over U, and its
first homology object is therefore zero. No injectivity as an abelian sheaf is used. -/
theorem isZero_cech_H_one_of_injective_module_sheaf
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (U : Y.Etale) {I : Type (u + 1)} (V : I → Y.Etale) (f : ∀ i : I, V i ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U) :
    IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙ ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj)).homology 1) := by
  classical
  let K := Y.smallEtaleTopology.toPrecoverage
  have htop : K.toGrothendieck = Y.smallEtaleTopology := by
    apply le_antisymm
    · exact Y.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro W R hR
      have h : R.arrows ∈ K W :=
        (Y.smallEtaleTopology.arrows_mem_toPrecoverage_iff R).2 hR
      simpa using K.generate_mem_toGrothendieck h
  have hc : Presieve.ofArrows V f ∈ K U := hcover
  obtain ⟨S⟩ := SiteCechComplex.exists_of_covering K hc
  obtain ⟨R, M, hM, ⟨e⟩⟩ := exists_injective_etale_ring_module Y Λ J
  have : HasSheafify K.toGrothendieck AddCommGrpCat.{u + 1} := by
    rw [htop]
    infer_instance
  have : K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
    rw [htop]
    infer_instance
  have vanish : ∀ (R : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (M : SheafOfModules.{u + 1} R), Injective M →
        IsZero ((S.cohomologyFunctor 1).obj M.val.presheaf) := by
    rw [← htop]
    intro R M hM
    have : Injective M := hM
    have : Injective M.val := injective_module_sheaf_injective_presheaf R M
    let q : ℕ := 0
    change IsZero ((S.complex M.val.presheaf).homology (q + 1))
    apply HomologicalComplex.ExactAt.isZero_homology
    apply (HomologicalComplex.exactAt_iff' (S.complex M.val.presheaf)
      q (q + 1) (q + 2) (by simp) (by simp)).2
    rw [ShortComplex.ab_exact_iff]
    intro c hc
    change (CochainComplex.of.d (S.cochains M.val.presheaf)
      (S.differential M.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
    rw [CochainComplex.of_d] at hc
    obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
      R.obj M.val V f S q c hc
    refine ⟨b, ?_⟩
    change (CochainComplex.of.d (S.cochains M.val.presheaf)
      (S.differential M.val.presheaf) q (q + 1)) b = c
    rw [CochainComplex.of_d]
    exact hb
  have hz := vanish R M hM
  have hz' : IsZero ((S.cohomologyFunctor 1).obj
      (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :=
    hz.of_iso ((S.cohomologyFunctor 1).mapIso e.symm)
  obtain ⟨c⟩ := S.mathlib_complex_iso_exists V f
    (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  exact hz'.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 1).mapIso c.symm)


end AlgebraicGeometry.Scheme
