/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedPullbackExact
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.ConstantScalarAlgebraicPullback

/-! # Ordinary flat sheaves under coefficient-sized inverse image

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme

/-- Exact coefficient-sized inverse image preserves ordinary flat module sheaves.

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat;
Tag 03CY identifies modules over a constant ring with fixed-scalar module sheaves.
(auxiliary; not a blueprint node).

Proof: present fixed-scalar sheaves on each coefficient-sized site as modules over
its constant A-ring by the normalized constant-scalar monoidal equivalence. This
preserves and reflects flatness, since tensor by the corresponding object is
conjugate by exact equivalences. The given sheaf inverse image is the module
inverse image of the geometric morphism whose set inverse image is base change
followed by sheafification. Its structural ring comparison is the canonical
isomorphism from inverse image of the constant A-ring to the constant A-ring.
For a finite relation in the inverse-image module, left exactness and the
local-generation property of inverse image lift its finitely many coefficients
and sections locally to the source site. Left exactness also lifts the equality
asserting that the relation vanishes. Apply the source flat module's local
finite-relation criterion, and pull its covering family and factorization back.
The result is a local factorization of the original relation on the target site.
The local equational criterion proves target flatness. The structural ring map
is an isomorphism, so its final scalar extension also preserves flatness. Transport
back to fixed scalars. This uses no bounded complexes or derived tensors, and
allows the zero ring, the zero sheaf and empty schemes. -/
theorem coefficientFixedPullback_preservesFlat
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    (coefficientProEtaleFixedModulePullback.{u, v} f A).PreservesFlat := by
  let J := coefficientProEtaleModelTopology.{u, v} X
  let K := coefficientProEtaleModelTopology.{u, v} Y
  let F := coefficientProEtaleModelBaseChange.{u, v} f
  have : PreservesFiniteLimits F := AlgebraicGeometry.ProEtale.model_preserves f
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let L := sheafPullback F (Type (max v (u + 1))) J K
  let R := F.sheafPushforwardContinuous (Type (max v (u + 1))) J K
  let adj : L ⊣ R := sheafAdjunctionContinuous F (Type (max v (u + 1))) J K
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  obtain ⟨I, ⟨e⟩⟩ := exists_constantScalarAlgebraicPullback J K F A
  constructor
  intro M hM
  let S := restriction J A
  let N := S.inv.obj M
  have hN : SheafOfModules.IsFlatOnSite.{max v (u + 1), max v (u + 1),
      max v (u + 1), max v (u + 1)} (R := ring J A) N := by
    apply (CategoryTheory.ConstantScalarRestriction.flat_iff J A N).mpr
    have h := ObjectProperty.prop_of_iso ObjectProperty.flat
      (S.asEquivalence.counitIso.app M).symm hM
    exact h.2
  have hI := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{max v (u + 1),
    max v (u + 1), max v (u + 1), max v (u + 1), max v (u + 1), max v (u + 1)}
    L R adj I N hN
  have hright := (CategoryTheory.ConstantScalarRestriction.flat_iff K A (I.modules.obj N)).mp hI
  have hflat : ObjectProperty.flat ((restriction K A).obj (I.modules.obj N)) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm hright, hright⟩
  let q := e.app N ≪≫
    (coefficientProEtaleFixedModulePullback.{u, v} f A).mapIso
      (S.asEquivalence.counitIso.app M)
  exact ObjectProperty.prop_of_iso ObjectProperty.flat q hflat

end AlgebraicGeometry.Scheme
