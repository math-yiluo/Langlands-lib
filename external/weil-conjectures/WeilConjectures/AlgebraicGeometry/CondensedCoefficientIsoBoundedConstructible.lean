/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Bounded constructibility under an isomorphism of coefficient rings

Source: latest blueprint, lem-fd-base-change.proof.md, coefficient-invariant
use of compact-support base change
(blueprint: lem-fd-coefficient-iso-bounded-constructible).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem boundedConstructible_comap_iso_forward
    {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hK : boundedConstructible R K) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) := by
  obtain ⟨⟨a, b, hbound⟩, hcons⟩ := (mem_boundedConstructible_iff R K).1 hK
  refine (mem_boundedConstructible_iff S _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact ((Mod.comap φ).map_isZero (hbound i hi)).of_iso
      (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso i).app K).symm
  · exact _root_.constructible_of_iso
      (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K)
      (_root_.constructible_comap φ (hcons n))

/-- Restriction along an isomorphism of sheaf coefficient rings preserves and
reflects bounded constructibility in the ordinary unbounded derived category.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
lem-fd-base-change.proof.md, the coefficient-invariant compact-support argument
(blueprint: lem-fd-coefficient-iso-bounded-constructible).

Proof: The restriction functor is exact and hence commutes with cohomology.
It preserves zero objects and takes finite presentations to finite presentations:
restrict the presentation matrix and identify each restricted regular module
with the regular module of the new ring. The same pro-etale covers and finite
stratification prove constructibility. Thus it preserves a cohomology bound and
constructibility of each cohomology sheaf. Apply this also to the inverse ring
isomorphism; the composition of the two restriction functors is canonically the
identity, and bounded constructibility is invariant under isomorphism. -/
theorem boundedConstructible_comap_iso_iff
    {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible R K := by
  constructor
  · intro h
    have h' := boundedConstructible_comap_iso_forward (inv φ) _ h
    let e : (Mod.comap φ).mapDerivedCategory ⋙ (Mod.comap (inv φ)).mapDerivedCategory ≅
        𝟭 _ :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          ((Mod.comapComp (inv φ) φ).symm ≪≫
            Mod.comapCongr (IsIso.inv_hom_id φ) ≪≫ Mod.comapId R) ≪≫
        Functor.mapDerivedCategoryIdIso _
    exact (boundedConstructible R).prop_of_iso (e.app K) h'
  · exact boundedConstructible_comap_iso_forward φ K

end AlgebraicGeometry.ProEtale
