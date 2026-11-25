/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleUnderlyingSetsOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets

/-!
# Finite direct image of constructible module sheaves with finite stalks

Source: Stacks Project, Tag 095R, and the module refinement argument in the
normalization exact-sequence blueprint, unit `proposition-proper-base-change-projective-line`.
(blueprint: lem-weil-pbc-finite-pushforward-finite-stalk-module)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite direct image preserves constructibility for module sheaves with finite stalks.

Source: Stacks Project, Tag 095R, together with the module refinement argument in
`sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`.
(blueprint: lem-weil-pbc-finite-pushforward-finite-stalk-module)

Proof: The source is Noetherian since it is finite over the Noetherian target.
On every stratum of a module constructible stratification, discard empty members of
an etale trivializing cover. The constant module on a remaining member is identified
with a geometric stalk and is therefore finite as a set. Each stratum is quasi-compact,
so finitely many such members suffice. There are finitely many strata; hence a finite
list of finite modules trivializes the source sheaf. The intersection I of their
annihilators kills the sheaf: this is checked on the strata and then on geometric
stalks. The ring Lambda/I embeds in the finite product of endomorphism rings of these
finite modules, so it is finite. If the source is empty take I = Lambda.
Forget to abelian groups and then sets; inverse image commutes with these forgetful
functors, and the finite module trivializations give finite constructible set strata.
The finite morphism is finitely presented over the Noetherian target, so apply the
finite abelian direct-image theorem of Tag 095R. Direct image commutes with
forgetting, and I still kills its sections, since direct image is precomposition.
On each resulting finite-set constant stratum, refine the etale cover so that addition,
zero and the scalar operations of the finite ring Lambda/I are constant. There are
only finitely many input tuples and operations, so a finite common refinement exists.
The original algebraic identities persist on the refinement. Thus the trivializations
are isomorphisms with constant finite Lambda/I-modules, also finitely generated as
Lambda-modules. Their geometric stalks are finite, so this is precisely
IsFiniteLocallyConstantSheaf on each stratum and gives IsConstructibleSheaf.
The zero sheaf and empty source/target are covered by the same argument. No hypothesis
that Lambda itself is Noetherian is used. -/
theorem isConstructibleSheaf_lowerStar_of_finite_stalks
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsFinite f]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType f
  let I : Ideal Λ := ⨅ U : Y.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U)
  have hI : Finite (Λ ⧸ I) :=
    finite_quotient_section_annihilator_of_finite_stalks Λ F hF hfin
  have hsets := isConstructibleEtaleSheafOfSets_of_finite_module_stalks Λ F hF hfin
  let E := (sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  have hpush := isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian f E hsets
  refine isConstructibleSheaf_of_finite_coefficient_underlying_sets Λ _ ?_ I hI ?_
  · exact hpush
  · intro U r hr m
    exact Module.mem_annihilator.mp
      (Ideal.mem_iInf.mp hr ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)) m

end AlgebraicGeometry.Scheme
