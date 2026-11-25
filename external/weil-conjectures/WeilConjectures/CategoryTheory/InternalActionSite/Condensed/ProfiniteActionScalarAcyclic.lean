/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionTwistedTransport
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedScalarInvariants

/-!
# Scalar restriction sends K-injective actions to invariant-acyclic complexes

Source: paragraph (3) of the direct-image stability proof (blueprint:
def-sfb-condensed-derived-invariants); Stacks, Cohomology on Sites, Tag 0D6E.

Let `a : A ⟶ A'` be a map of condensed rings. For a K-injective complex `I` of internal
`A'`-actions and a quasi-isomorphism `j : σ(I) ⟶ J` from its scalar restriction to a
K-injective complex of internal `A`-actions, the map of invariants `V(j)` is a
quasi-isomorphism. Through the twisted ringed site, scalar restriction is the direct image of
an identity-site ringed-topos morphism, and invariants is the direct image along the projection
to the small profinite site; this is the composition clause of Stacks 0D6E.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar

open ActionSite InternalActionSite

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A A' : Ring.{u}} {a : A ⟶ A'}

/-- Any scalar restriction of actions is isomorphic to the canonical one. -/
noncomputable def ScalarAction.isoComap (σ : ScalarAction a G) :
    σ.functor ≅ scalarActionFunctor a G :=
  NatIso.ofComponents
    (fun N ↦ ⟨⟨σ.underlying.hom.app N, σ.action N⟩, ⟨σ.underlying.inv.app N, fun S g x ↦ by
        apply Function.LeftInverse.injective (σ.underlying_hom_inv_apply N S)
        rw [σ.action]
        erw [σ.underlying_inv_hom_apply, σ.underlying_inv_hom_apply]
        rfl⟩, Subtype.ext (σ.underlying.hom_inv_id_app N),
      Subtype.ext (σ.underlying.inv_hom_id_app N)⟩)
    (fun φ ↦ Subtype.ext (σ.underlying.hom.naturality φ))

variable (G) in
/-- The fixed-point direct image on twisted modules, transported from invariants. -/
noncomputable abbrev twistedInvariants (V : Invariants A G) :
    SheafOfModules.{u + 1} (twistedRingOf G A) ⥤ SheafOfModules.{u + 1} (siteRing A) :=
  (twistedEquivalence G A).inverse ⋙ V.functor ⋙ (moduleSiteEquivalence A).functor

/-- The transported invariants are right adjoint to pullback along the projection. -/
noncomputable def twistedInvariantsAdjunction (V : Invariants A G) :
    projectionPullback G A ⊣ twistedInvariants G V :=
  (((moduleSiteEquivalence A).symm.toAdjunction.comp V.adjunction).comp
    (twistedEquivalence G A).toAdjunction).ofNatIsoLeft
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleSiteEquivalence A).inverse trivialTwistedNatIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleSiteEquivalence A).counitIso _ ≪≫
      Functor.leftUnitor _)

/-- Scalar restriction of internal actions sends K-injective complexes to complexes acyclic
for invariants: for every quasi-isomorphism `j : σ(I) ⟶ J` with `I` and `J` K-injective,
`V(j)` is a quasi-isomorphism. -/
theorem scalarAction_quasiIso_invariants_map [ActionAbelian A G] [ActionAbelian A' G]
    (σ : ScalarAction a G) (V : Invariants A G)
    (I : CochainComplex (Equivariant A' G) ℤ) [I.IsKInjective]
    (J : CochainComplex (Equivariant A G) ℤ) [J.IsKInjective]
    (j : (σ.functor.mapHomologicalComplex _).obj I ⟶ J) [QuasiIso j] :
    QuasiIso ((V.functor.mapHomologicalComplex _).map j) := by
  have : (moduleSiteEquivalence A).functor.Additive :=
    inferInstanceAs (toSiteModule A).Additive
  have : (twistedEquivalence G A).inverse.Additive :=
    (twistedEquivalence G A).inverse_additive
  have h := restrictScalars_kInjectiveImageAcyclic (groupPresheaf G) modelPrecoverage
    modelPrecoverage_isSiteForCoverings (ringSheaf A) (ringSheaf A') (twistedRingMap G a)
    (twistedInvariants G V) (twistedInvariantsAdjunction V)
  refine Functor.KInjectiveImageAcyclic.of_equivalence (twistedEquivalence G A')
    (twistedEquivalence G A) (moduleSiteEquivalence A)
    (Functor.isoWhiskerRight σ.isoComap _ ≪≫ scalarTwistedNatIso a)
    ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (twistedEquivalence G A).unitIso _ ≪≫ Functor.associator _ _ _)
    h I J j

end CategoryTheory.CondensedBar
