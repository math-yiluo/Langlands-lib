/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenComplementPullbackVanishing

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

private instance underlyingAbelian_additive (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add := by intros; rfl

private theorem shortExact_underlying_abelian (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) :
    (S.map (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).ShortExact := by
  let T := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : Limits.PreservesFiniteLimits (T ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (Limits.PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  have : Limits.PreservesFiniteLimits T :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves T (sheafToPresheaf _ _)
  have := hS.mono_f
  have := hS.epi_g
  have hg : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 inferInstance
  have : Sheaf.IsLocallySurjective (T.map S.g) := ⟨fun s ↦ hg.imageSieve_mem s⟩
  exact
    { exact := hS.exact.map_of_mono_of_preservesKernel T hS.mono_f inferInstance
      mono_f := Functor.map_mono T S.f
      epi_g := Sheaf.epi_of_isLocallySurjective (T.map S.g) }

/-- The degree-two pullback component of dense-open cohomology comparison.
Source: Stacks Project, Tag 0GJA, remark (d). (blueprint: lem-pbc-s2-dense-open-cohomology-pullback)
-/
theorem dense_open_high_cohomology_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    ∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a],
      Function.Bijective
        (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map ε) 2) := by
  dsimp
  intro W a ha
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let i := I.subschemeι
  have hi : Set.range i.base = (U : Set X)ᶜ := by
    change Set.range I.subschemeι = _
    rw [I.range_subschemeι]
    simp [I]
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    simpa using hi
  let S := openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι i
    (disjoint_range_of_range_eq_compl U.ι i hij) F
  have hS : S.ShortExact :=
    shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι i F hij
  let T := S.map (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  have hT : T.ShortExact := shortExact_underlying_abelian Λ hS
  let R := T.map ((a)^*[AddCommGrpCat.{u + 1}])
  have hR : R.ShortExact := hT.map_of_exact _
  have hv := dense_open_complement_pullback_vanishing Λ f U hU i hi
    (((i)^*[ModuleCat.{u + 1} Λ]).obj F) a
  have : Subsingleton (Sheaf.H R.X₃ 1) := hv 1 (by decide)
  have : Subsingleton (Sheaf.H R.X₃ 2) := hv 2 (by decide)
  change Function.Bijective (Sheaf.H.map R.f 2)
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    obtain ⟨y, hy⟩ := (Sheaf.H.exact_δSucc_map hR 1 x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  · intro y
    exact (Sheaf.H.exact_map_map hR 2 y).mp (Subsingleton.elim _ _)

end AlgebraicGeometry.IsCurve
