/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.PerfectNoetherianCohomology
import WeilConjectures.AlgebraicGeometry.PerfectRelativeFiniteTor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Perfect direct image along a proper perfect morphism

Source: literature/stacks-project/more-morphisms.tex, Lemma 37.61.13, Tag 0B6G
(blueprint: lem-pc-proper-perfect-direct-image-perfect).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Derived direct image along a proper perfect morphism over a Noetherian base
preserves perfect objects. Perfectness of the morphism is expressed by the equivalent
stalkwise finite Tor criterion of Stacks Lemma 37.61.11.
Source: Stacks Project, More on Morphisms, Lemma 37.61.13, Tag 0B6G.
Proof: (1) Properness (def-weil-proper-morphism) gives finite type, a Noetherian source,
and proper supports for the coherent cohomology of P. Locally P has a bounded strictly
perfect representative (lemma-coherent-base-change-invertible-sheaves--1), so its cohomology is
coherent. A finite open cover of the quasi-compact source makes the cohomological bounds uniform.
The finite Tor dimension of the source local rings implies that these local representatives
have finite Tor dimension over the inverse image of the target structure sheaf; local
bounds become uniform by quasi-compactness.
(2) Apply lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect (Stacks Tag 08EV)
with S = Y and E = P: the target is Noetherian, f is locally of finite type, P is bounded
coherent, its supports are proper, and its relative Tor dimension is finite. The
criterion concludes that Rf_*P is perfect on Y.
(blueprint: lem-pc-proper-perfect-direct-image-perfect). -/
theorem proper_perfect_directImage_perfect
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [IsNoetherian Y] (f : X ⟶ Y) [IsProper f] (hperfect : HasStalkwiseFiniteTorDimension f)
    (P : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P) :
    Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj P) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨hbounded, hcoherent⟩ := Scheme.perfect_bounded_coherent_cohomology X P hP
  have hsupport : ∀ i : ℤ, Scheme.Modules.HasSupportProperOver f
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P) := by
    intro i
    let F : X.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P
    obtain ⟨hq, ht⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp (hcoherent i)
    have : F.IsQuasicoherent := hq
    have : F.IsFiniteType := ht
    let Z : TopologicalSpace.Closeds X :=
      ⟨{x : X | ¬ Subsingleton (F.presheaf.stalk x)},
        (Scheme.Modules.finite_type_module_support_closed X F).2.2.2⟩
    refine ⟨Z, rfl, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)
    infer_instance
  exact Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    f P hbounded hcoherent hsupport (Scheme.perfect_hasFiniteTorDimensionOver f hperfect P hP)

end AlgebraicGeometry
