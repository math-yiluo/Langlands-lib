import Langlands.Representation.Exponents.LeviCuspidalEmbeddingDescent
import Langlands.Representation.Exponents.LeviParabolicExtensionProof
import Langlands.Representation.Exponents.LeviParabolicTransitivityProof
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.Representation.Aubert.General.JacquetFiniteGeneration
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Renard VI.2.1 for actual represented parabolics

Renard VI.2.1, Corollary and proof (printed p.139 / PDF p.145): an irreducible smooth
representation `π` of `G(F)` has a parabolic `P = MU` whose Jacquet module `r_P^G(π)` is
nonzero and supercuspidal, and `π` embeds into the induction of an irreducible
supercuspidal quotient of `r_P^G(π)`.

The proof assembles published steps: a parabolic with minimal all-test range among those
with nonzero Jacquet module, supercuspidality of its Jacquet module by parabolic extension
and transitivity, finite generation of the Jacquet module through compactness of
`P(F)\G(F)`, and the final quotient and Frobenius-reciprocity step.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finite generation over the group algebra passes to the composite of a representation
with a surjective group homomorphism. -/
theorem module_finite_comp_of_surjective {H H' V : Type*} [Group H] [Group H']
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (φ : H' →* H)
    (hφ : Function.Surjective φ) (hfin : Module.Finite (MonoidAlgebra ℂ H) ρ.asModule) :
    Module.Finite (MonoidAlgebra ℂ H') (Representation.asModule (ρ.comp φ)) := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  let s' : Finset (Representation.asModule (ρ.comp φ)) := s
  let N := Submodule.span (MonoidAlgebra ℂ H') (s' : Set (Representation.asModule (ρ.comp φ)))
  let S := Subrepresentation.ofSubmodule' N
  -- The same subspace is stable under `H`, since every element of `H` comes from `H'`.
  let S' : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨g', rfl⟩ := hφ g
        exact S.apply_mem_toSubmodule g' hx }
  have hle : Submodule.span (MonoidAlgebra ℂ H) (s : Set ρ.asModule) ≤ S'.asSubmodule := by
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ N
    exact Submodule.subset_span hx
  refine ⟨⟨s', ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro x
  have hx : (show ρ.asModule from x) ∈ S'.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
  exact hx

/-- Renard VI.1.3 for one actual parabolic datum: the normalized Levi-valued Jacquet module
of a smooth representation of `G(F)` that is finitely generated over `ℂ[G(F)]` is finitely
generated over `ℂ[M(F)]`. Compactness of `P(F)\G(F)` comes from the published dynamic
description of parabolics and dynamic quotient compactness. -/
theorem leviJacquetFunctor_obj_finite :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p l hp hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
          Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule →
            Module.Finite (MonoidAlgebra ℂ (rationalPoints M))
              ((leviJacquetFunctor.{u, v} p l r hp hr hl hmul).obj π).representation.asModule := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hfg
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
      BruhatTits.dynamicParabolicQuotientCompact hG p hp
  have h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hfin := JacquetFiniteGeneration.finite_of_compactQuotient h
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) π hfg
  exact module_finite_comp_of_surjective _ (leviPointsEquiv p l hp hl).toMonoidHom
    (leviPointsEquiv p l hp hl).surjective hfin

/-- Renard VI.2.1, Corollary and proof, for actual represented parabolics: every
irreducible smooth representation `π` of `G(F)` has an actual parabolic datum `P = MU`
whose normalized Jacquet module `J` is nonzero and supercuspidal, together with an
irreducible supercuspidal quotient `ρ` of `J` and an injective intertwiner
`π → i_P^G ρ`. -/
theorem leviCuspidalEmbedding : LeviCuspidalEmbeddingStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hπ
  have : π.representation.IsIrreducible := hπ
  have hπnt : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
  have hfg : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule :=
    inferInstance
  -- A parabolic datum with nonzero Jacquet module and minimal all-test range.
  obtain ⟨⟨P, M, U, p, l, r, hp, hl, hr, hmul⟩, hJ, hmin⟩ :=
    exists_minimal_nontrivial_leviJacquet.{u, v} k G hG π hπnt
  refine ⟨P, M, U, p, l, r, hp, hl, hr, hmul, ?_⟩
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  -- Supercuspidality by minimality, parabolic extension and transitivity.
  have hcusp := leviJacquet_supercuspidal_of_minimal.{u, v} leviParabolicExtension
    leviParabolicTransitivity k G hG π P M U p l r hp hl hr hmul
    (fun P₁ M₁ U₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ hlt =>
      hmin ⟨P₁, M₁, U₁, p₁, l₁, r₁, hp₁, hl₁, hr₁, hmul₁⟩ hlt)
  -- Finite generation of the Jacquet module.
  have hfin := leviJacquetFunctor_obj_finite.{u, v} k G hG P M U p l r hp hl hr hmul π hfg
  exact ⟨hJ, hcusp, (cuspidalEmbedding_of_finite_supercuspidal.{u, v} k G hG π hπ
    P M U p l r hp hl hr hmul hJ hfin hcusp)⟩

end Langlands.Aubert.General.RepresentedParabolic
