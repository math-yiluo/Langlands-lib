/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison

/-!
# Abelian cohomology of injective etale module sheaves

Source: Stacks Project, Cohomology on Sites, Lemma 03FD, second paragraph of the proof
(blueprint: lem-weil-pbc-injective-module-abelian-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An injective sheaf of modules over the constant commutative ring sheaf has vanishing
positive-degree cohomology on every object of the small etale site, computed in abelian
sheaves. No injectivity of the underlying abelian sheaf is assumed. `ULift` only places
coefficients in the universe of the sheaf values.

Source: Stacks Project, Lemma 03FD, second paragraph of the proof
(blueprint: lem-weil-pbc-injective-module-abelian-acyclic).

Proof (the node's five steps). Fix an object U and any covering of U. Write O for the
constant ring sheaf and K for the chain complex of free presheaves of O-modules of this
covering. Yoneda identifies Hom(O_V, G) with G(V), by evaluation at the generator indexed
by the identity of V. Thus Hom(K, G) is naturally the Cech cochain complex of G, including
its alternating restriction differential (def-weil-presheaf-modules-sheafification,
def-weil-pbc-cech-complex, lem-weil-pbc-free-cech-complex-exact; Step 1).
The free complex K has zero positive homology, objectwise, by
lem-weil-pbc-free-cech-complex-exact (Step 2). An injective module sheaf I is injective as
a presheaf of modules by lem-weil-pbc-injective-module-injective-presheaf. Exactness of
Hom(-, I) then shows that Hom(K, I), hence the Cech complex of I, has zero positive
cohomology (Step 3). Forgetting the module action leaves the section groups and
restriction maps unchanged, so the underlying abelian sheaf has the identical Cech
complex (situation-conventions and def-weil-pbc-cech-complex; Step 4).
Apply lem-weil-pbc-cech-vanishing-criterion with all objects and all coverings. Fibre
products exist by def-weil-pbc-etale-site, and every cover refines itself. The preceding
Cech vanishing supplies the third hypothesis, giving zero higher right derived
functors of abelian-sheaf evaluation at every U (Step 5). -/
theorem isZero_rightDerived_etale_toSheaf_of_injective
    (X : Scheme.{u}) (R : Type u) [CommRing R]
    (I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))) [Injective I]
    (U : X.Etale) (q : ℕ) (hq : 0 < q) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op U)).rightDerived q).obj ((SheafOfModules.toSheaf _).obj I)) := by
  have htop : X.smallEtaleTopology.toPrecoverage.toGrothendieck =
      X.smallEtaleTopology := by
    apply le_antisymm
    · exact X.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let J := X.smallEtaleTopology.toPrecoverage
  let O := (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1, u} R))
  have hcech (U : X.Etale) (T : Type (u + 1)) (V : T → X.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨e⟩ := nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso e.symm)
  exact isZero_rightDerived_etale_of_cech_vanishing X Set.univ
    (fun U _ V f ↦ Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech U (Set.mem_univ _) q hq

end AlgebraicGeometry.Scheme
