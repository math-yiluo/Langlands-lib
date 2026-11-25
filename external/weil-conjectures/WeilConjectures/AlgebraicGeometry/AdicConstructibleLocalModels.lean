/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicImmersionLiftingInput
import WeilConjectures.AlgebraicGeometry.AdicResidueLissePerfectLift
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-! # Perfect local models from an adic constructible residue

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Intersect the witnessing stratifications for a finite family of cohomology sheaves. -/
private theorem finite_cohomology_stratification (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (hC : ∀ q : ℤ, IsConstructibleSheaf (C.homology q)) (t : Finset ℤ) :
    ∃ s : Stratification X, ∀ q ∈ t, ∀ α : Fin s.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} R) (s.immersion α)).obj (C.homology q)) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨Stratification.trivial X, by simp⟩
  | @insert q t hqt ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨r, hr⟩ := (hC q).exists_stratification
    refine ⟨s.inter r, ?_⟩
    intro j hj α
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (s.inter_refines_right r).isFiniteLocallyConstantSheaf_upperStar
        (C.homology j) hr α
    · exact (s.inter_refines_left r).isFiniteLocallyConstantSheaf_upperStar
        (C.homology j) (hs j hj) α

/-- Only the finite interval of nonzero cohomology requires refinement. -/
private theorem bounded_cohomology_stratification (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (a b : ℤ) (hbounded : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q))
    (hC : ∀ q : ℤ, IsConstructibleSheaf (C.homology q)) :
    ∃ s : Stratification X, ∀ (α : Fin s.n) (q : ℤ),
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} R) (s.immersion α)).obj (C.homology q)) := by
  classical
  obtain ⟨s, hs⟩ := finite_cohomology_stratification X R C hC (Finset.Icc a b)
  refine ⟨s, ?_⟩
  intro α q
  by_cases hq : q ∈ Finset.Icc a b
  · exact hs q hq α
  · have hout : q < a ∨ b < q := by simpa only [Finset.mem_Icc, not_and_or,
      not_le] using hq
    exact IsFiniteLocallyConstantSheaf.of_isZero
      ((Etale.upperStar (ModuleCat.{u + 1} R) (s.immersion α)).map_isZero (hbounded q hout))

/-- An immersed stratum of a Noetherian scheme is Noetherian. -/
private theorem noetherian_stratum {X : Scheme.{u}} [IsNoetherian X]
    (s : Stratification X) (α : Fin s.n) : IsNoetherian (s.domain α) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (s.immersion α)
  have : TopologicalSpace.NoetherianSpace (s.domain α) :=
    (s.immersion α).isEmbedding.isInducing.noetherianSpace
  exact { }

/-- A complete object with bounded constructible etale residue admits finite stratified
perfect local models.
Source: Bhatt--Scholze, Proposition 6.6.11, forward implication, and Lemma 6.6.8
(auxiliary; not a blueprint node).

Proof: Only finitely many residue cohomology sheaves are nonzero. Intersect their finite
constructible stratifications using the actual scheme fibre products. Pullback of the
chosen local trivializations makes every cohomology sheaf locally constant of finite
type on each refined stratum; zero cohomology imposes no extra refinement. Each stratum
is Noetherian, since its immersion is locally a quotient of a Noetherian affine chart
and its underlying subspace is quasi-compact. Transport the original ringed-module
complex to the equivalent small pro-etale site. Restriction of the completion unit to
immersions and slices preserves completeness, and comparison-pullback identifies the
residue with the pullback of the restricted etale complex. Over the residue field tensor
is exact, so the same bounded interval is a Tor interval after restriction. Apply
adicResidueLissePerfectLift on each stratum. Transport its covering sieve and its local
isomorphisms back through the small-site equivalence. Its bounded finite-projective
complex is perfect by the definition of IsPerfectRingComplex, witnessed by itself.
Composition of inverse images and their finite-projection coefficient comparisons gives
exactly sfbLocalRestriction and sfbCompletedModel. Assemble the finitely many strata.
For empty X the empty cover supplies the same assertion. -/
theorem adicConstructible_localModels (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbAdicConstructible X I K) :
    ∃ s : Stratification X,
      (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
      ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
        V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
          ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
            ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
              P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
              Nonempty
                (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
                  sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                    (sfbCompletedModel X I P)) := by
  classical
  obtain ⟨hcomplete, C, ⟨a, b, hab, hbounded⟩, hconstructible, hres, _htor⟩ := hK
  obtain ⟨s, hs⟩ := bounded_cohomology_stratification X (A ⧸ I ^ (0 + 1)) C a b
    hbounded hconstructible
  refine ⟨s, s.isConstructible_stratum, ?_⟩
  intro α
  have := noetherian_stratum s α
  obtain ⟨M, C', hM, hC', hlisse, htor, hres', hslice⟩ :=
    sfbAdicImmersion_liftingInput X (s.domain α) (s.immersion α) A I hI.1 K
      hcomplete C a b hab hbounded (hs α) hres
  obtain ⟨V, hV, hmodels⟩ := adicResidueLissePerfectLift.{u, 0} (s.domain α) I M hM C'
    ⟨a, b, hC'⟩ hlisse a b hab htor hres'
  let up : (s.domain α).ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} (s.domain α) :=
    AsSmall.up
  have : up.IsDenseSubsite (ProEt.topology (s.domain α))
      (coefficientProEtaleModelTopology.{u, 0} (s.domain α)) :=
    inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := (s.domain α).ProEt)).functor.IsDenseSubsite
        (ProEt.topology (s.domain α))
        ((AsSmall.equiv.{u, u + 1, u + 1} (C := (s.domain α).ProEt)).inverse.inducedTopology
          (ProEt.topology (s.domain α))))
  have : up.IsCocontinuous (ProEt.topology (s.domain α))
      (coefficientProEtaleModelTopology.{u, 0} (s.domain α)) := by
    infer_instance
  refine ⟨V.functorPullback up, up.cover_lift _ _ hV, ?_⟩
  intro U f hf
  obtain ⟨P, c, d, hc, hd, hP, ⟨eP⟩⟩ := hmodels (up.obj U) (up.map f) hf
  obtain ⟨eU, ⟨eK⟩, hconstant⟩ := hslice U
  obtain ⟨econstant⟩ := hconstant P
  exact ⟨P, c, d, hc, hd, fun q ↦ ⟨(hP q).2, (hP q).1⟩,
    ⟨eK ≪≫ eU.functor.mapIso eP ≪≫ econstant⟩⟩

end AlgebraicGeometry.Scheme
