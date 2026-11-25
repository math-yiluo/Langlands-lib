/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Descent of duality and Tor bounds along a pro-etale cover

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart,
the global comparison and local Tor bounds in integral-heart-dualizable.
(blueprint: lem-integral-heart-local-duality-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Local dualizability of a degree-zero module gives invertibility of its global
canonical tensor--Hom comparison; local Tor bounds descend on the same cover.

Source: Stacks Project, Tags 08JJ, 08J9 and 0G7E; integral-heart-dualizable,
proof steps 3, 4, 6 and 7.
(blueprint: lem-integral-heart-local-duality-descent)

Proof: each member of the pro-etale cover is weakly etale, so its inverse image is
exact slice restriction. Exact restriction commutes with cohomology, derived tensor,
and derived internal Hom, with the canonical evaluation maps. Consequently the
restriction of the global tensor--Hom comparison is its local comparison. For a
local dualizable object that comparison is invertible, by the closed monoidal
duality criterion. Its cohomology maps are thus isomorphisms on every chart.
Cover-local detection of isomorphisms of sheaves and the unbounded derived
cohomology criterion make the global comparison invertible. For any module sheaf G,
restrict K tensor G[0]. Tensor compatibility identifies this with the local derived
tensor against the restricted G. The assumed local Tor bound gives vanishing
outside [a,b]; exactness and cover-local detection of zero sheaves give the same
vanishing globally. This quantifies over every G, without a finiteness condition.
Only isomorphisms and cohomology vanishing are detected locally. -/
theorem integralHeart_local_duality_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (a b : ℤ)
    (hlocal : ∀ i : 𝒰.I₀,
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (𝒰.f i)).obj M)) ∧
      DerivedCategory.torAmplitudeIn _ a b ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (𝒰.f i)).obj M))) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom
      ((DerivedCategory.singleFunctor _ 0).obj M)
      ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    DerivedCategory.torAmplitudeIn _ a b ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have hd : IsDualizable K := by
    apply (condensed_dualizable_iff_proetale_cover R X 𝒰 K).mpr
    intro i
    exact (hlocal i).1.of_iso
      (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategorySingleFunctor 0).app M).symm
  obtain ⟨hdual⟩ := hd
  obtain ⟨br⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let := br
  let := BraidedCategory.exactPairing_swap K Kᘁ
  have hc : IsIso (MonoidalClosed.ihomUnitTensorToIhom K K) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K K
  refine ⟨hc, ?_⟩
  intro G
  let L := K ⊗ (DerivedCategory.singleFunctor _ 0).obj G
  have hv (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    have hs : IsZero ((DerivedCategory.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ q).obj L)) := by
      apply (condensed_cover_restriction_conservative R X 𝒰).2
      intro i
      let F := CondensedRing.upperStar Λ (𝒰.f i)
      obtain ⟨braid⟩ := (condensed_derivedPullback_exact_symmetricMonoidal R (𝒰.f i)).2
      let := braid
      let e : F.mapDerivedCategory.obj L ≅
          (DerivedCategory.singleFunctor _ 0).obj (F.obj M) ⊗
          (DerivedCategory.singleFunctor _ 0).obj (F.obj G) :=
        (Functor.Monoidal.μIso F.mapDerivedCategory _ _).symm ≪≫
          tensorIso ((F.mapDerivedCategorySingleFunctor 0).app M)
            ((F.mapDerivedCategorySingleFunctor 0).app G)
      have hb := (DerivedCategory.homologyConcentratedIn a b).prop_of_iso e.symm
        ((hlocal i).2 (F.obj G))
      have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (F.mapDerivedCategory.obj L)) := by
        rcases hq with hq | hq
        · exact (DerivedCategory.isGE_iff _ _).mp hb.1 q hq
        · exact (DerivedCategory.isLE_iff _ _).mp hb.2 q hq
      exact ((DerivedCategory.singleFunctor _ 0).map_isZero
        (hz.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app L))).of_iso
        ((F.mapDerivedCategorySingleFunctor 0).app _)
    exact IsZero.of_full_of_faithful_of_isZero
      (DerivedCategory.singleFunctor _ 0) _ hs
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun q hq ↦ hv q (Or.inl hq)),
    (DerivedCategory.isLE_iff _ _).mpr (fun q hq ↦ hv q (Or.inr hq))⟩

end AlgebraicGeometry.ProEtale
