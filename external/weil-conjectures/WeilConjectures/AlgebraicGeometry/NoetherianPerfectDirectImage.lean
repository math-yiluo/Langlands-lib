/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.PerfectTensorBoundedCoherent
import WeilConjectures.AlgebraicGeometry.BoundedComplexTensorProperSupportBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.PerfectTensorFiniteRelativeTor

/-! # Perfect direct image over a Noetherian base

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.2, Tag 0DJQ
(blueprint: lem-pc-noetherian-perfect-direct-image).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Over a Noetherian base, the derived direct image of a perfect object tensored with a
bounded complex of finitely presented, relatively flat modules with proper support is perfect.
Source: Stacks Project, Lemma 36.27.2, Tag 0DJQ, specialized to a finitely presented morphism.

Proof:
1. Finite presentation implies locally finite type
(lemma-coherent-base-change-invertible-sheaves--1,
   lemma-coherent-base-change-invertible-sheaves--1), so X is locally Noetherian
   (lemma-coherent-base-change-invertible-sheaves--1, Tag 01T6). The finitely presented terms of G
   are therefore coherent (lemma-coherent-base-change-invertible-sheaves--1). Their finitely many
   nonzero supports have a closed union Z proper over S, hence compact. Cover Z by finitely many
   opens on which E has strictly perfect representatives
   (lemma-coherent-base-change-invertible-sheaves--1). Tensoring these with G gives bounded
   complexes of coherent modules: their terms are summands of finite sums of terms of G. Outside Z
   the tensor vanishes. Thus E tensor^L G has bounded coherent cohomology, using Tag 01Y0.
2. The cohomology supports are closed subsets of Z, hence proper over S
   (lemma-coherent-base-change-invertible-sheaves--1), since closed immersions and composites
   of proper morphisms are proper.
3. The local tensor representatives consist of modules flat over the inverse image of O_S.
   The finite cover gives uniform bounds [a,b]. Tag 08CI gives Tor amplitude [a,b] on
   each open, and vanishing outside this range is local (Tag 08CG). Thus the tensor has
   finite Tor dimension over the inverse image of O_S, also being zero outside Z.
4. Apply lemma-coherent-base-change-invertible-sheaves--1 (Tag 08EV) to the
   tensor object: bounded coherence, proper cohomology supports and finite relative Tor
   dimension give a perfect derived direct image (lemma-coherent-base-change-invertible-sheaves--1).
(blueprint: lemma-coherent-base-change-invertible-sheaves--1). -/
theorem noetherian_perfect_directImage
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (G.X n) f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ DerivedCategory.Q.obj G)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hGcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (G.X n) := by
    intro n
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X (G.X n)).2
      ⟨inferInstance, inferInstance⟩
  obtain ⟨hbounded, hcoherent⟩ :=
    Scheme.perfect_tensor_bounded_coherent E hE G hGb hGcoherent
  apply Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    f (E ⊗ DerivedCategory.Q.obj G) hbounded hcoherent
  · obtain ⟨Z, hZ, hsupport⟩ :=
      Scheme.boundedComplex_tensor_proper_support_bound f E G hGb hGproper
    intro i
    let H : X.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
        (E ⊗ DerivedCategory.Q.obj G)
    have hH : RingedSpace.IsCoherent X.toRingedSpace H := hcoherent i
    have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X H).1 hH
    have : H.IsQuasicoherent := hq.1
    have : H.IsFiniteType := hq.2
    let Y : TopologicalSpace.Closeds X :=
      ⟨{x : X | ¬ Subsingleton (H.presheaf.stalk x)},
        (Scheme.Modules.finite_type_module_support_closed X H).2.2.2⟩
    exact ⟨Y, rfl,
      (Scheme.closed_subset_proper_over_base_properties f Z).2.2.1 Y (hsupport i) hZ⟩
  · exact Scheme.perfect_tensor_hasFiniteTorDimensionOver f E hE G hGb hGflat

end AlgebraicGeometry
