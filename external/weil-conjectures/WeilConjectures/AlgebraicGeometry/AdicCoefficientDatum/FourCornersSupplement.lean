/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CompletedTowerPullback
public import WeilConjectures.AlgebraicGeometry.FourCorners

/-!
# The four finite-coefficient corners

Source: blueprint, proper base change, four corners; Stacks Project Tags 07A7 and 099M
(blueprint: def-weil-pbc-four-corners).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- Its universal left derived functor, including quotient-coefficient actions.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtension :
    DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory (proEtaleRingModules T S) :=
  reductionDerivedChange T a

/-- The universal derived counit comparing scalar extension with ordinary tensor.
Source: Stacks 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtensionCounit := reductionDerivedCounit T a

/-- The selected ordinary functor has the recorded tensor objects.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners).
Proof: this is the object-identification clause of the recorded derived-change-of-rings
existence theorem, specialized to its selected ordinary functor. -/
theorem proEtaleRingExtension_obj (M : proEtaleRingModules T R) :
    (proEtaleRingExtension a).obj M = SheafOfModules.changeOfRings a M := by
  exact (reductionChangeExistence T a).choose_spec.choose M

/-- Reuse the published universal-counit normalized derived scalar adjunction.
Source: Stacks 06YY, 0DVC (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtensionAdjunction :
    proEtaleRingDerivedExtension a ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory :=
  pbcDerivedScalarAdjunction a

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

/-- Reduction followed by finite pullback, in the inverse direction of chi, is the mate
of the canonical restriction/pullback identification. Its tensor-unit normalization fixes
the ordinary balancing map on K-flat representatives.
Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleReductionPullbackInv :
    proEtaleRingDerivedPullback f RV RU cR ⋙ proEtaleRingDerivedExtension aU ⟶
      proEtaleRingDerivedExtension aV ⋙ proEtaleRingDerivedPullback f SV SU cS :=
  (mateEquiv (proEtaleRingDerivedExtensionAdjunction aV)
    (proEtaleRingDerivedExtensionAdjunction aU)).symm
      (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified reduction/pullback mate is invertible in the quotient-coefficient
category itself. Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners).
Proof: choose a flat-term K-flat representative Q. Pullback preserves K-flatness and
flat terms, including for the identity-topos scalar-extension map. Hence all four derived
operations are computed by ordinary tensors on these representatives. The normalized
scalar and pullback adjunctions identify this mate with the balancing map
(u*Q) tensor SU → u_n*(Q tensor SV). Compatibility of the coefficient square makes this
SU-linear. Its inverse is the ordinary tensor reassociation. Both maps commute with
restriction and differentials, and localization preserves their inverse identities. -/
theorem proEtaleReductionPullbackInv_isIso :
    IsIso (proEtaleReductionPullbackInv f RV SV RU SU aV aU cR cS comm) := by
  -- The other mate is the published invertible direct-image comparison.
  -- Taking both mates is conjugation between composite adjunctions.
  let av := proEtaleRingDerivedExtensionAdjunction aV
  let au := proEtaleRingDerivedExtensionAdjunction aU
  let ar := proEtaleRingDerivedAdjunction f RV RU cR
  let az := proEtaleRingDerivedAdjunction f SV SU cS
  let b := proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm
  let d := proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm
  let α := TwoSquare.mk _ _ _ _ b.inv
  have hmate : mateEquiv az ar α = d.hom := by
    apply NatTrans.ext
    funext N
    have h := (proEtaleRingSheafChangeAdjunction
      f RV SV RU SU aV aU cR cS comm).2.2
      ((proEtaleRingDerivedDirectImage f SV SU cS).obj N) N (az.counit.app N)
    have hid : az.homEquiv _ _ (az.counit.app N) = 𝟙 _ := by
      rw [← az.homEquiv_symm_id N]
      exact (az.homEquiv _ _).apply_symm_apply _
    change ar.homEquiv _ _ (b.inv.app _ ≫
      (proEtaleRingRestrictScalars aU).mapDerivedCategory.map (az.counit.app N)) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
          (az.homEquiv _ _ (az.counit.app N)) ≫ d.hom.app N at h
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [← h]
    simp only [α, mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.comp_obj,
      Functor.comp_map, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
      Category.id_comp, Adjunction.homEquiv_unit, Functor.map_comp]
    erw [Category.comp_id]
  let γ := (mateEquiv av au).symm α
  have hm : mateEquiv av au γ = α := (mateEquiv av au).apply_symm_apply α
  have hc : IsIso (conjugateEquiv (av.comp az) (ar.comp au) γ) := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ, hm, hmate]
    infer_instance
  exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) γ

/-- The coefficient-reduction comparison chi, in the displayed direction of the node.
Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleReductionPullbackIso :
    proEtaleRingDerivedExtension aV ⋙ proEtaleRingDerivedPullback f SV SU cS ≅
      proEtaleRingDerivedPullback f RV RU cR ⋙ proEtaleRingDerivedExtension aU :=
  (@asIso _ _ _ _ (proEtaleReductionPullbackInv f RV SV RU SU aV aU cR cS comm)
    (proEtaleReductionPullbackInv_isIso f RV SV RU SU aV aU cR cS comm)).symm

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Every level of the quotient ring tower is finite, including the zero quotient ring.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners).
Proof: level n is A/I^(n+1). The finite-quotient clause of the adic datum
gives its finiteness, including when the quotient is the zero ring. -/
theorem AdicCoefficientDatum.ringTower_finite (n : ℕᵒᵖ) : Finite (d.ringTower.obj n) := by
  change Finite (A ⧸ d.ideal ^ (n.unop + 1))
  infer_instance

attribute [instance] AdicCoefficientDatum.ringTower_finite

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed coefficient structure map is the actual limit lift of its projections.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.integralRingMap {U V : Scheme.{u}} (f : U ⟶ V) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V) ⟶
      d.completedRing U :=
  limit.lift (reductionCoefficientSystem U d)
    { pt := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V)
      π := { app n := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (d.projection V n.unop) ≫ (d.finiteRingIso f n.unop).hom
             naturality _ _ a := (Category.id_comp _).trans
               (d.integralRingComponent_naturality f a).symm } }

private noncomputable def fourCornersConstantTowerIso (T : Scheme.{u}) :
    proEtaleCoefficientTower T d.ringTower ≅ adicLisseRingSystem T d.ideal := by
  let t : proEtaleCoefficientTower T d.ringTower ⟶ adicLisseRingSystem T d.ideal :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [proEtaleCoefficientTower, Functor.comp_map, AdicCoefficientDatum.ringTower,
        adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id,
        Category.id_comp]
      rfl)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified limit structure map is invertible by the profinite coefficient theorem.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: the published constant-system comparison identifies both coefficient limits
with the limits of finite constant quotients. Under these isomorphisms the displayed
limit lift has the projections of proEtaleProfiniteComparison, hence equals that map.
The profinite inverse-image theorem makes it invertible. No preservation of arbitrary
infinite limits is assumed. -/
theorem AdicCoefficientDatum.integralRingMap_isIso {U V : Scheme.{u}} (f : U ⟶ V) :
    IsIso (d.integralRingMap f) := by
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let e (T : Scheme.{u}) := HasLimit.isoOfNatIso
    (fourCornersConstantTowerIso d T ≪≫ pbcConstantSystemComparison T d)
  have : IsIso (proEtaleProfiniteComparison f d.ringTower) :=
    (proEtale_profinite_coefficient_inverse_image d.ringTower).2.1 U V f
  have he : d.integralRingMap f =
      L.map (e V).inv ≫ proEtaleProfiniteComparison f d.ringTower ≫ (e U).hom := by
    apply limit.hom_ext
    intro n
    dsimp only [e]
    simp only [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc _ _ ((fourCornersConstantTowerIso d U ≪≫
      pbcConstantSystemComparison U d).hom.app n)]
    rw [(proEtale_profinite_coefficient_inverse_image d.ringTower).2.2.1 U V f n]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc]
    rw [HasLimit.isoOfNatIso_inv_π]
    dsimp [AdicCoefficientDatum.integralRingMap, AdicCoefficientDatum.finiteRingIso,
      fourCornersConstantTowerIso]
    simp only [L, pbcConstantSystemComparison, AdicCoefficientDatum.projection,
      completedReductionProjection, reductionCoefficientSystem, limit.lift_π,
      NatIso.isIso_inv_app, Functor.comp_obj, NatTrans.ofOpSequence_app, op_unop,
      IsIso.inv_id, Functor.map_comp, Category.id_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The canonical profinite coefficient comparison in the published function presentation.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.integralRingIso {U V : Scheme.{u}} (f : U ⟶ V) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V) ≅
      d.completedRing U :=
  @asIso _ _ _ _ (d.integralRingMap f) (d.integralRingMap_isIso f)

/-- The projection compatibility is exactly the projection clause of the canonical
profinite comparison. Source: blueprint four corners; Stacks Tag 098T
(blueprint: def-weil-pbc-four-corners).
Proof: specialize the projection identity of profinite-coefficient-inverse-image to the
quotient tower and its index n. The homs of asIso are the original comparisons. -/
theorem AdicCoefficientDatum.projection_comm {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    (d.integralRingIso f).hom ≫ d.projection U n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V n) ≫
        (d.finiteRingIso f n).hom := by
  exact limit.lift_π _ (op n)

/-- Ordinary integral derived pullback, without completion.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.pull {U V : Scheme.{u}} (f : U ⟶ V) :=
  proEtaleRingDerivedPullback f (d.completedRing V) (d.completedRing U) (d.integralRingIso f)

/-- Ordinary integral derived direct image in all modules.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.push {U V : Scheme.{u}} (f : U ⟶ V) :=
  proEtaleRingDerivedDirectImage f (d.completedRing V) (d.completedRing U) (d.integralRingIso f)

/-- Finite-coefficient derived pullback with its quotient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finitePull {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :=
  proEtaleRingDerivedPullback f (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso f n)

/-- Finite-coefficient derived direct image with its quotient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finitePush {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :=
  proEtaleRingDerivedDirectImage f (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso f n)

/-- The canonical chi comparison with its original quotient coefficients retained.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.chi {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    d.reduction V n ⋙ d.finitePull f n ≅ d.pull f ⋙ d.reduction U n :=
  proEtaleReductionPullbackIso f (d.completedRing V) (d.finiteRing V n)
    (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
    (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n)

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fourCornersFinite_comp {U V W : Scheme.{u}}
    (h : U ⟶ V) (k : V ⟶ W) (n : ℕ) :
    d.finiteRingIso (h ≫ k) n = proEtaleRingCompositeCoefficients h k
      (d.finiteRing W n) (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso k n) (d.finiteRingIso h n) := by
  apply Iso.ext
  dsimp only [AdicCoefficientDatum.finiteRingIso, proEtaleRingCompositeCoefficients,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom]
  rw [(proEtale_profinite_coefficient_inverse_image d.ringTower).2.2.2.2.2.2.2.2.2.1
    U V W h k (op n)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ((proEtaleRingInverseImageComp h k).hom.naturality
    (pbcLevelConstantComparison W d n).inv)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fourCornersIntegral_comp {U V W : Scheme.{u}}
    (h : U ⟶ V) (k : V ⟶ W) :
    d.integralRingIso (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (d.completedRing W) (d.completedRing V) (d.completedRing U)
      (d.integralRingIso k) (d.integralRingIso h) := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  change (d.integralRingIso (h ≫ k)).hom ≫ d.projection U n.unop =
    (proEtaleRingInverseImageComp h k).hom.app (d.completedRing W) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (d.integralRingIso k).hom ≫
      (d.integralRingIso h).hom ≫ d.projection U n.unop
  rw [d.projection_comm, d.projection_comm]
  rw [← Functor.map_comp_assoc, d.projection_comm]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% ((proEtaleRingInverseImageComp h k).hom.naturality
    (d.projection W n.unop))]
  rw [fourCornersFinite_comp d h k n.unop]
  rfl

include sq in
/-- Commutativity of integral coefficients around the square follows from the composite
coherence of the profinite comparison. Source: blueprint four corners; Stacks Tag 098T
(blueprint: def-weil-pbc-four-corners).
Proof: apply the composite-coherence clause to both paths and identify the composite
scheme morphisms using sq.w. Both maps are the canonical comparison for that morphism;
their inverse maps agree because both are isomorphisms. -/
theorem AdicCoefficientDatum.integral_coherent :
    HEq (proEtaleRingCompositeCoefficients g' f (d.completedRing Y) (d.completedRing X)
      (d.completedRing X') (d.integralRingIso f) (d.integralRingIso g'))
    (proEtaleRingCompositeCoefficients f' g (d.completedRing Y) (d.completedRing Y')
      (d.completedRing X') (d.integralRingIso g) (d.integralRingIso f')) := by
  rw [← fourCornersIntegral_comp d g' f, ← fourCornersIntegral_comp d f' g]
  exact congr_arg_heq (fun q : X' ⟶ Y ↦ d.integralRingIso q) sq.w

include sq in
/-- The same composition identity for each finite coefficient level.
Source: blueprint four corners; Stacks Tag 098T (blueprint: def-weil-pbc-four-corners).
Proof: apply the finite-level composite-coherence clause of the profinite comparison
along both paths of sq; identify the scheme composites by sq.w. -/
theorem AdicCoefficientDatum.finite_coherent (n : ℕ) :
    HEq (proEtaleRingCompositeCoefficients g' f (d.finiteRing Y n) (d.finiteRing X n)
      (d.finiteRing X' n) (d.finiteRingIso f n) (d.finiteRingIso g' n))
    (proEtaleRingCompositeCoefficients f' g (d.finiteRing Y n) (d.finiteRing Y' n)
      (d.finiteRing X' n) (d.finiteRingIso g n) (d.finiteRingIso f' n)) := by
  rw [← fourCornersFinite_comp d g' f n, ← fourCornersFinite_comp d f' g n]
  exact congr_arg_heq (fun q : X' ⟶ Y ↦ d.finiteRingIso q n) sq.w

/-- The canonical ambient exchange with integral completed coefficients.
Source: blueprint four corners; Stacks Tag 07A7 (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.integralExchange :=
  proEtaleAmbientRingedExchange sq (d.completedRing X) (d.completedRing Y)
    (d.completedRing X') (d.completedRing Y') (d.integralRingIso f) (d.integralRingIso g)
    (d.integralRingIso g') (d.integralRingIso f') (d.integral_coherent sq)

/-- The same canonical ambient exchange with the actual finite quotient coefficients.
Source: blueprint four corners; Stacks Tag 07A7 (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finiteExchange (n : ℕ) :=
  proEtaleAmbientRingedExchange sq (d.finiteRing X n) (d.finiteRing Y n)
    (d.finiteRing X' n) (d.finiteRing Y' n) (d.finiteRingIso f n) (d.finiteRingIso g n)
    (d.finiteRingIso g' n) (d.finiteRingIso f' n) (d.finite_coherent sq n)

/-- Four corners at one positive finite level. Index n denotes the paper's n+1.
These use ordinary pullback of K, including when no completeness condition is needed to
form the objects. Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.fourCorners (K : d.derived X) (n : ℕ) :
    Fin 4 → DerivedCategory (proEtaleRingModules Y' (d.finiteRing Y' n)) :=
  ![(d.finitePull g n).obj ((d.reduction Y n).obj ((d.push f).obj K)),
    (d.finitePull g n).obj ((d.finitePush f n).obj ((d.reduction X n).obj K)),
    (d.reduction Y' n).obj ((d.push f').obj ((d.pull g').obj K)),
    (d.finitePush f' n).obj ((d.finitePull g' n).obj ((d.reduction X n).obj K))]

/-- The comparison delta is chi inverse at K, with quotient coefficients intact.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.delta (K : d.derived X) (n : ℕ) :
    (d.reduction X' n).obj ((d.pull g').obj K) ≅
      (d.finitePull g' n).obj ((d.reduction X n).obj K) :=
  (d.chi g' n).symm.app K

end AlgebraicGeometry.Scheme
