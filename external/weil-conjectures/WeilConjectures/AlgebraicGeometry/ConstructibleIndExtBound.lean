/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.ConstructibleIndExtBoundOfContinuity
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityAlgCl
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityFinite

/-!
# Extending a specified constructible Ext bound to ind-constructible sheaves

Source: blueprint latest, sec-six-functors-basics/sk-cor-ind-heart-ii/_section.md,
vanishing clause, used by the one-cohomology case of lemma-reduction-finitely-many-degrees.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The specified bound extends to ind-constructible targets on a Noetherian scheme,
for either of the canonical field coefficient sheaves.

Source: blueprint `corollary-ind-heart-b`, vanishing clause.
(blueprint: lem-finite-window-ind-ext-bound-noetherian)
Proof: the existing Noetherian continuity theorem makes the shifted Hom functor
preserve each filtered module colimit. Every element of the colimit of abelian
groups has a representative at a stage. This supplies the factorization condition
in `constructibleInd_extBound_of_continuity`, which kills each representative by
the specified bound. This is a special case, not a proof for arbitrary schemes. -/
theorem constructibleInd_extBound_noetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X),
      IsConstantModelConstructible (coefficientHeartRingObj R) X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (coefficientHeartRingObj R) X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
  apply constructibleInd_extBound_of_continuity (coefficientHeartRingObj R) X C hC
    ?_ d hbound B hB r hr
  intro M hM I _ _ F c hc n f
  let G := DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M))
  have : IsIso (colimit.post F G) :=
    constructible_sheaf_ext_continuity ℓ E R hR X M hM
      F (colimit.cocone F) (colimit.isColimit F) n
  have : PreservesColimit F G := preservesColimit_of_isIso_post G F
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (F ⋙ G)
    (isColimitOfPreserves G hc) f
  exact ⟨i, g, hg.symm⟩

/-- A specified bound against constructible sheaves also bounds Ext into an
ind-constructible sheaf. The coefficient equality includes the multiplication,
via bundled monoid objects. This is the sheaf input to bounded-complex devissage.

Source: blueprint latest, corollary-ind-heart-b, vanishing clause, and
sk-lem-finite-window-bounded.proof.md, one-cohomology case
(blueprint: lem-finite-window-ind-ext-bound).

Proof: choose a small filtered constructible presentation B = colim B_i.
The filtered-colimit Ext comparison of lemma-continuity-ext-out-constructible-complex--1,
clause (1), identifies Ext^r(C,B) with colim Ext^r(C,B_i). Every stage group is
zero by the supplied bound since d < r. A colimit of zero abelian groups is
zero; transporting along the comparison gives the claim. This uses only
sheaves, viewed as complexes in degree zero, so the common lower bound is zero.
The source states this for arbitrary X. The existing theorem
`constructible_sheaf_ext_continuity` has additional Noetherian and compactness
hypotheses, so the arbitrary-scheme geometric input is isolated in the two
coefficient-specific declarations `continuousMap_ext_continuity` and
`padicAlgCl_ext_continuity`. The conditional algebraic step is proved in
`constructibleInd_extBound_of_continuity`, and `constructibleInd_extBound_noetherian`
proves the canonical-coefficient Noetherian special case. Full filtered-colimit
continuity in degree zero cannot be assumed on a non-quasi-compact scheme. -/
theorem constructibleInd_extBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (X : Scheme.{u})
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (_hC : IsConstantModelConstructible Λ X C)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
  rcases _hΛ with hΛ | hΛ
  · have hΛ' : Λ = Profinite.continuousMapRingObj E := congrArg Mon.X hΛ
    subst Λ
    exact constructibleInd_extBound_of_continuity _ X C _hC
      (continuousMap_ext_continuity ℓ E X) d hbound B hB r hr
  · have hΛ' : Λ = Profinite.padicAlgClRingObj ℓ := congrArg Mon.X hΛ
    subst Λ
    exact constructibleInd_extBound_of_continuity _ X C _hC
      (padicAlgCl_ext_continuity ℓ X (fun F ↦ continuousMap_ext_continuity ℓ F X))
      d hbound B hB r hr

end AlgebraicGeometry.ProEtale
