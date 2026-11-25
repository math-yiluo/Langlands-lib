/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.SfbNormalizedLocalRestrictionIso

/-! # Gluing completeness from local isomorphisms to complete objects

Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10; Proposition 6.6.11,
reverse implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private def finiteStrata {X : Scheme.{u}} (s : Stratification X) :
    FiniteLocallyClosedStratification X where
  n := s.n
  stratum := s.stratum
  isLocallyClosed_stratum := s.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
  domain := s.domain
  immersion := s.immersion
  isImmersion := s.isImmersion
  range_immersion := s.range_immersion

private theorem normalizedComplete_iso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O T : Sheaf J CommRingCat.{u + 1}} (q : O ⟶ T)
    {K L : ConstantCompletion.D O} (e : K ≅ L)
    (hL : ConstantCompletion.IsComplete q L) : ConstantCompletion.IsComplete q K := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod O)
  let := fun U : C ↦ HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  intro U f hf
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  exact (((ringedDerivedRestriction O U ⋙ H).mapIso e).isZero_iff).mpr (hL U f hf)

/-- Completeness is detected by local isomorphisms to complete objects on a finite
stratification. The comparison objects may vary with the covering arrow. They need
not be perfect, bounded or constructible.

Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10; Proposition 6.6.11,
reverse implication; Stacks proetale.tex Tags 099L and 099M.
(auxiliary; not a blueprint node).

Proof: choose a finite generating list for I by Noetherianity. Forget constructibility
in s to obtain its finite locally closed stratification, retaining exactly its scheme
domains and immersion maps. Transport V and its covering proof along AsSmall.up; the
induced topology and the site equivalence identify the transported covering arrows with
the original ones. The constant-sheaf and limit comparisons identify the transported
completed rings and first projections with those in adicStratumCompletionUnit_detection.
For each stratum immersion choose the algebraic inverse-image data supplied by its
geometric adjunction. Uniqueness of the module inverse-image adjunction and scalar
extension identifies the restriction in that theorem with sfbLocalRestriction after
transport to the equivalent slice site. This identification is natural in the derived
object, since both exact functors factor termwise localization. A complete L remains
complete on this stratum and slice by adicStratumCompletionUnit. Transport its local
isomorphism with K through the exact coefficient and site equivalences. Local internal
Hom preserves isomorphisms in its second argument, so the restricted K is complete as
well. Finally apply the reverse implication of adicStratumCompletionUnit_detection to
these restrictions. The global coefficient comparison identifies its conclusion with
IsSfbAdicComplete X I K. The same argument treats empty strata and the empty scheme:
the conservativity theorem uses the empty-cover sheaf axiom and requires no point. -/
theorem sfbAdicComplete_of_stratum_local_iso (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (s : Stratification X)
    (V : ∀ α : Fin s.n, Sieve (⊤_ (s.domain α).ProEt))
    (hV : ∀ α : Fin s.n,
      V α ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt))
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hlocal : ∀ (α : Fin s.n) (U : (s.domain α).ProEt)
      (f : U ⟶ ⊤_ (s.domain α).ProEt), V α f →
      ∃ L : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
        IsSfbAdicComplete X I L ∧
          Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
            sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U L)) :
    IsSfbAdicComplete X I K := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing I)
  let t := finiteStrata s
  let W (α : Fin t.n) := (V α).functorPushforward
    (AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α))
  have hW (α : Fin t.n) : W α ∈ proEtaleModelTopology (t.domain α)
      ((AsSmall.up : (t.domain α).ProEt ⥤ proEtaleSiteModel (t.domain α)).obj
        (⊤_ (t.domain α).ProEt)) := by
    let e := AsSmall.equiv.{u, u + 1, u + 1} (C := (s.domain α).ProEt)
    have : e.functor.IsDenseSubsite (ProEt.topology (s.domain α))
        (proEtaleModelTopology (s.domain α)) :=
      inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
        (C := (s.domain α).ProEt)).functor.IsDenseSubsite
          (ProEt.topology (s.domain α))
          ((AsSmall.equiv.{u, u + 1, u + 1}
            (C := (s.domain α).ProEt)).inverse.inducedTopology
              (ProEt.topology (s.domain α))))
    exact (e.functor.functorPushforward_mem_iff (ProEt.topology (s.domain α))
      (proEtaleModelTopology (s.domain α))).mpr (hV α)
  have hF (α : Fin t.n) :
      Nonempty (ConstantCompletion.InverseImageData
        (SfbAdicRestriction.inverse (t.immersion α))) := by
    let := t.isImmersion α
    exact ConstantCompletion.inverseImageData_exists _ _
      (SfbAdicRestriction.adjunction (t.immersion α))
  let F (α : Fin t.n) := (hF α).some
  apply (SfbCompletionNormalization.complete_iff X I K).mpr
  apply (SfbAdicRestriction.adicStratumCompletionUnit_detection X A I r a ha
    t W hW F (SfbCompletionNormalization.object X I K)).mpr
  intro α U f hf
  have hdown : V α ((AsSmall.down : proEtaleSiteModel (s.domain α) ⥤
      (s.domain α).ProEt).map f) := by
    have h := (Sieve.mem_functorPushforward_functor (e :=
      AsSmall.equiv.{u, u + 1, u + 1} (C := (s.domain α).ProEt))).mp hf
    have heq : (AsSmall.down.map f) ≫
        (AsSmall.equiv.{u, u + 1, u + 1} (C := (s.domain α).ProEt)).unitInv.app
          (⊤_ (s.domain α).ProEt) = AsSmall.down.map f := terminal.hom_ext _ _
    exact heq ▸ h
  obtain ⟨L, hL, e⟩ := hlocal α (AsSmall.down.obj U) (AsSmall.down.map f) hdown
  obtain ⟨en⟩ := sfbNormalizedLocalRestriction_iso (s.immersion α) A I (F α)
    (AsSmall.down.obj U) K L e
  have hnL := (SfbCompletionNormalization.complete_iff X I L).mp hL
  have hpres := SfbAdicRestriction.adicStratumCompletionUnit X A I r a ha
  have hi := (hpres.1 (s.domain α) (s.immersion α) (F α)).2.2.2.2 _ hnL
  have hs := (hpres.2 (s.domain α) (s.immersion α) U).2.2.2.2 _ hi
  exact normalizedComplete_iso _ en hs

end AlgebraicGeometry.Scheme
