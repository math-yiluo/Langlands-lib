/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u u₁ v₁ w₁ r₁

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

-- Universe-transport helpers follow PushedResolutionPositiveHomologyZero.
private theorem locallyInjective_zero_ulift_iff
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w₁}) :
    Presheaf.IsLocallyInjective J
        (0 : P ⋙ AddCommGrpCat.uliftFunctor.{r₁, w₁} ⟶
          P ⋙ AddCommGrpCat.uliftFunctor.{r₁, w₁}) ↔
      Presheaf.IsLocallyInjective J (0 : P ⟶ P) := by
  constructor
  · intro h
    constructor
    intro V x y _
    have hS := h.equalizerSieve_mem (X := V) (ULift.up x) (ULift.up y) (by simp)
    convert hS using 1
    ext U f
    change P.map f.op x = P.map f.op y ↔
      ULift.up (P.map f.op x) = ULift.up (P.map f.op y)
    exact ULift.up_inj.symm
  · intro h
    constructor
    intro V x y _
    have hS := h.equalizerSieve_mem (X := V) x.down y.down (by simp)
    convert hS using 1
    ext U f
    change ULift.up (P.map f.op x.down) = ULift.up (P.map f.op y.down) ↔
      P.map f.op x.down = P.map f.op y.down
    exact ULift.up_inj

private theorem locallyInjective_zero_of_iso
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w₁}} (e : P ≅ Q)
    (h : Presheaf.IsLocallyInjective J (0 : P ⟶ P)) :
    Presheaf.IsLocallyInjective J (0 : Q ⟶ Q) := by
  have : Presheaf.IsLocallyInjective J (e.inv ≫ (0 : P ⟶ P) ≫ e.hom) :=
    inferInstance
  simpa using this

/-- Vanishing of positive etale object cohomology on affine opens implies vanishing
of the corresponding derived direct image along the inclusion of opens.
Source: Stacks Project, Cohomology on Sites, Tags 072W and 0733(1).
https://stacks.math.columbia.edu/tag/072W
(blueprint: lem-sc-etale-positive-direct-image-object-acyclic)

Proof: Choose an injective resolution I of F. The free-abelian representable
adjunction and the injective-resolution computation of Ext identify the object
cohomology presheaf with the objectwise homology of I. Precompose by i.op;
the equality hi identifies i(U) with the canonical etale open object.
Every open admits an affine open cover, so the hypothesis makes every section
of this homology presheaf locally zero. Its zero endomorphism is locally
injective, and hence sheafifies to a monomorphism. Since sheafification is
additive, that monomorphism is zero, so the sheafification is a zero object.
Exact sheafification commutes with homology; its counit identifies the
sheafification of the presheaf complex underlying i_*I with i_*I itself.
Thus the degree n+1 homology of i_*I is zero. The resolution comparison
identifies it with R^(n+1)i_*F. If the Ext and section-complex universes differ,
compare them after ULift; equality of restrictions and zero-object status
are reflected by ULift. The empty open uses its empty covering, and n+1
is positive even when n=0. Only this fixed degree is required. -/
theorem positiveDirectImageOfObjectAcyclic
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (hF : ∀ U : X.Opens, IsAffineOpen U → IsZero
      (Sheaf.H' F (n + 1) (Scheme.Etale.mk U.ι))) :
    IsZero ((((i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).rightDerived
      (n + 1)).obj F)) := by
  classical
  let J := Opens.grothendieckTopology X.carrier
  let P := i.op ⋙ F.cohomologyPresheaf (n + 1)
  have hobj (U : X.Opens) : i.obj U = Scheme.Etale.mk U.ι := by
    have h : (i.obj U).toComma = (Scheme.Etale.mk U.ι).toComma :=
      congrArg (fun f : X.Opens ⥤ Over X ↦ f.obj U) hi
    apply MorphismProperty.Comma.ext
    · exact congrArg Comma.left h
    · exact congrArg Comma.right h
    · exact congr_arg_heq Comma.hom h
  have hP : Presheaf.IsLocallyInjective J (0 : P ⟶ P) := by
    constructor
    intro V x y _ z hz
    obtain ⟨U, hU, hzU, hUV⟩ := exists_isAffineOpen_mem_and_subset hz
    refine ⟨U, homOfLE hUV, ?_, hzU⟩
    change P.map (homOfLE hUV).op x = P.map (homOfLE hUV).op y
    have hzero : IsZero (P.obj (op U)) := by
      change IsZero (Sheaf.H' F (n + 1) (i.obj U))
      rw [hobj U]
      exact hF U hU
    exact (AddCommGrpCat.isZero_iff_subsingleton.mp hzero).elim _ _
  let I := injectiveResolution F
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u} J X.smallEtaleTopology
  let K := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := ((sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).obj K
  let M := ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let W := (Functor.whiskeringLeft X.Opensᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u}).obj i.op
  let eW : i.op ⋙ M.homology (n + 1) ≅ L.homology (n + 1) :=
    ((M.sc (n + 1)).mapHomologyIso W).symm
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution X.smallEtaleTopology F I (n + 1)
  let e' := Functor.isoWhiskerLeft i.op e
  have hP' := (locallyInjective_zero_ulift_iff.{u, u, u, u + 1} J P).2 hP
  have hQ := locallyInjective_zero_of_iso J e' hP'
  have hM := (locallyInjective_zero_ulift_iff.{u, u, u, u + 1}
    J (i.op ⋙ M.homology (n + 1))).1 hQ
  have hL := locallyInjective_zero_of_iso J eW hM
  let a := presheafToSheaf J AddCommGrpCat.{u}
  have : a.Additive := Functor.additive_of_preserves_binary_products _
  have : Sheaf.IsLocallyInjective (a.map (0 : L.homology (n + 1) ⟶ L.homology (n + 1))) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).2 hL
  have : Mono (a.map (0 : L.homology (n + 1) ⟶ L.homology (n + 1))) :=
    Sheaf.mono_of_isLocallyInjective _
  have hZ : IsZero (a.obj (L.homology (n + 1))) :=
    IsZero.of_mono_eq_zero (a.map (0 : L.homology (n + 1) ⟶ L.homology (n + 1)))
      (a.map_zero _ _)
  let eK : (a.mapHomologicalComplex (.up ℕ)).obj L ≅ K :=
    (Functor.mapHomologicalComplexCompIso
      (sheafificationNatIso J AddCommGrpCat.{u}).symm (.up ℕ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).app K
  let eH := ((L.sc (n + 1)).mapHomologyIso a).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) (n + 1)).mapIso eK
  have hK : IsZero (K.homology (n + 1)) := hZ.of_iso eH.symm
  exact hK.of_iso (I.isoRightDerivedObj T (n + 1))

end AlgebraicGeometry.Scheme.Modules
