/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.Algebra.Homology.SmoothPurity.KernelShiftedConeBoundary
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

/-!
# Relative section cones and supported cohomology

The structures below package equations, rather than choosing comparison maps from an
existence theorem. Their kernel and right-derived normalizations fix the identifications.
Object squares express both restriction to an etale neighbourhood and enlargement of
support, on the site of the original scheme, without changing sites by an implicit bridge.

## References

* Stacks Project, Cohomology on Sites, cohomology with support
* Stacks, cohomology with support
* Stacks Tag 09XP
* Stacks, support restriction
* Stacks Tag 0G71
* Stacks Tag 0G78
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry
namespace Etale
namespace RelativeCone

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)

/-- Evaluation on the given site. -/
noncomputable abbrev evaluationFunctor (V : C) : Sheaf J AddCommGrpCat.{u + 1} ⥤
    AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op V)

/-- Restriction on sections. -/
noncomputable def restriction {V W : C} (f : W ⟶ V) :
    evaluationFunctor J V ⟶ evaluationFunctor J W :=
  Functor.whiskerLeft (sheafToPresheaf J _) ((evaluation _ _).map f.op)

/-- A section complex, extended by zero. This specializes to `relativeSections`. -/
noncomputable abbrev sections (V : C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I).extend
    ComplexShape.embeddingUpNat

/-- Restriction between the extended section complexes. -/
noncomputable def restrictionComplex {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    sections J V I ⟶ sections J W I :=
  extendMap ((NatTrans.mapHomologicalComplex (restriction J f) _).app I)
    ComplexShape.embeddingUpNat

/-- The signed relative cone, on either site and over any object of that site. -/
noncomputable abbrev fiber {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (CochainComplex.mappingCone (restrictionComplex J f I))⟦(-1 : ℤ)⟧

/-- The supported-section complex, using the dependency's single support functor. -/
noncomputable abbrev supported {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
    (.up ℕ)).obj I).extend ComplexShape.embeddingUpNat

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- The canonical computation isomorphism, including the extension-by-zero transport. -/
noncomputable def computation (G : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [G.Additive] {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (q : ℕ) :
    (G.rightDerived q).obj F ≅
      ((((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat).homology (q : ℤ)) :=
  I.isoRightDerivedObj G q ≪≫
    (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (by rfl)).symm

/-- Forgetting support before deriving it. -/
noncomputable def forgetSupport {V W : C} (f : W ⟶ V) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f ⟶ evaluationFunctor J V where
  app F := kernel.ι (F.obj.map f.op)
  naturality α := by simp [Sheaf.supportedSectionsFunctor, evaluationFunctor]

/-- The map of supported-section functors belonging to an actual object square. -/
noncomputable def supportRestriction {V W V' W' : C} (f : W ⟶ V) (f' : W' ⟶ V')
    (v : V' ⟶ V) (w : W' ⟶ W) (h : f' ≫ v = w ≫ f) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f ⟶
      Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f' where
  app F := kernel.map _ _ (F.obj.map v.op) (F.obj.map w.op)
    (by simpa only [← Functor.map_comp, ← op_comp] using
      (congrArg (fun g ↦ F.obj.map g.op) h).symm)
  naturality F F' α := by
    apply equalizer.hom_ext
    dsimp [Sheaf.supportedSectionsFunctor]
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    rw [← α.hom.naturality]

/-- A coefficient-resolution map evaluated on an object. -/
noncomputable def coefficientMap (V : C)
    {I I' : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ} (φ : I ⟶ I') :
    sections J V I ⟶ sections J V I' :=
  extendMap (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).map φ)
    ComplexShape.embeddingUpNat

end RelativeCone

namespace RelativeCone

/-- The first cone projection; the etale specialization is `relativeForgetComplex`. -/
noncomputable def projection {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r : A ⟶ B) :
    (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ ⟶ A :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (CochainComplex.mappingCone.fst r)) ≫
    (shiftFunctorAdd _ (1 : ℤ) (-1 : ℤ)).inv.app _ ≫
    (shiftFunctorZero _ ℤ).hom.app _

/-- The shifted cone inclusion, corresponding to `(0,-b)` in the signed model. -/
noncomputable def boundary {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r : A ⟶ B) :
    B⟦(-1 : ℤ)⟧ ⟶ (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)

/-- Commutation with the two arrows of the relative triangle. -/
def TriangleSquare {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) : Prop :=
  relativeFiberMap r r' a b h ≫ projection r' = projection r ≫ a ∧
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map b ≫ boundary r' =
    boundary r ≫ relativeFiberMap r r' a b h

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- Canonically normalized realization for a support pair and a supplied resolution.
The boundary field compares with the connecting map of the kernel short exact sequence;
the forget field compares with `R^q` of the actual kernel inclusion, rather than an
unconstrained map. -/
structure Realization {V W : C} (f : W ⟶ V)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) where
  kernelIso : supported J f I.cocomplex ≅ kernel (restrictionComplex J f I.cocomplex)
  kernel_components : ∀ n : ℕ,
    kernelIso.hom.f (n : ℤ) ≫ (kernel.ι (restrictionComplex J f I.cocomplex)).f n =
      ((((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).hom ≫
        kernel.ι ((I.cocomplex.X n).obj.map f.op) ≫
        ((((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
          ComplexShape.embeddingUpNat (by rfl)).inv
  κ : kernel (restrictionComplex J f I.cocomplex) ⟶ fiber J f I.cocomplex
  κ_quasiIso : HomologicalComplex.quasiIso AddCommGrpCat.{u + 1} (.up ℤ) κ
  κ_components : ∀ n : ℤ,
    κ.f n ≫ ((CochainComplex.mappingCone (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (restrictionComplex J f I.cocomplex) (n - 1) = 0 ∧
    κ.f n ≫ ((CochainComplex.mappingCone (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (restrictionComplex J f I.cocomplex)
        (n - 1) n (by change n - 1 + 1 = n; omega) =
      (kernel.ι (restrictionComplex J f I.cocomplex)).f n
  exact : (ShortComplex.mk (kernel.ι (restrictionComplex J f I.cocomplex))
    (restrictionComplex J f I.cocomplex) (kernel.condition _)).ShortExact
  e : ∀ q : ℕ, (fiber J f I.cocomplex).homology q ≅
    ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).obj F
  normalization : ∀ q : ℕ,
    homologyMap kernelIso.hom (q : ℤ) ≫ homologyMap κ (q : ℤ) ≫ (e q).hom =
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv
  forget : ∀ q : ℕ,
    (e q).hom ≫ (NatTrans.rightDerived (forgetSupport J f) q).app F =
      homologyMap (projection (restrictionComplex J f I.cocomplex)) (q : ℤ) ≫
        (computation J (evaluationFunctor J V) I q).inv
  localization : ∀ q : ℕ,
    homologyMap (boundary (restrictionComplex J f I.cocomplex)) (q : ℤ) ≫ (e q).hom =
      (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q : ℤ)
        ((q : ℤ) - 1) (by omega)).hom.app (sections J W I.cocomplex) ≫
      exact.δ ((q : ℤ) - 1) (q : ℤ) (by change (q : ℤ) - 1 + 1 = q; omega) ≫
      homologyMap kernelIso.inv (q : ℤ) ≫
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv

/-- A compatible family of realizations on one site. Object squares include the pullback
square of an etale neighbourhood and the square `W' ⊆ W` with identity on the ambient
object. Coefficient lifts are arbitrary lifts of the given coefficient morphism, so the
identity-coefficient case states independence of the resolution and of its comparison map. -/
structure System (P : ∀ {V W : C}, (W ⟶ V) → Prop) where
  realization : ∀ {V W : C} (f : W ⟶ V), P f →
    ∀ {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F), Realization J f I
  coefficients : ∀ {V W : C} (f : W ⟶ V) (hf : P f)
    {F F' : Sheaf J AddCommGrpCat.{u + 1}} (α : F ⟶ F')
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (φ : I.cocomplex ⟶ I'.cocomplex) (_hφ : I.ι.f 0 ≫ φ.f 0 = α ≫ I'.ι.f 0)
    (h : coefficientMap J V φ ≫ restrictionComplex J f I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ coefficientMap J W φ) (q : ℕ),
    homologyMap (relativeFiberMap _ _ (coefficientMap J V φ) (coefficientMap J W φ) h)
      (q : ℤ) ≫ ((realization f hf I').e q).hom =
    ((realization f hf I).e q).hom ≫
      ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).map α ∧
    TriangleSquare _ _ (coefficientMap J V φ) (coefficientMap J W φ) h
  objects : ∀ {V W V' W' : C} (f : W ⟶ V) (f' : W' ⟶ V') (hf : P f) (hf' : P f')
    (v : V' ⟶ V) (w : W' ⟶ W) (hs : f' ≫ v = w ≫ f)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (h : restrictionComplex J v I.cocomplex ≫ restrictionComplex J f' I.cocomplex =
      restrictionComplex J f I.cocomplex ≫ restrictionComplex J w I.cocomplex) (q : ℕ),
    homologyMap (relativeFiberMap _ _ (restrictionComplex J v I.cocomplex)
      (restrictionComplex J w I.cocomplex) h) (q : ℤ) ≫
      ((realization f' hf' I).e q).hom =
    ((realization f hf I).e q).hom ≫
      (NatTrans.rightDerived (supportRestriction J f f' v w hs) q).app F ∧
    TriangleSquare _ _ (restrictionComplex J v I.cocomplex)
      (restrictionComplex J w I.cocomplex) h

end RelativeCone

namespace RelativeCone

/-- The termwise pullback of the chosen etale resolution. -/
noncomputable abbrev pulledResolution (T : Scheme.{u})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :=
  ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
    (.up ℕ)).obj I

private noncomputable def supportedInclusion
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supported J f I ⟶ sections J V I :=
  extendMap ((NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I)
    ComplexShape.embeddingUpNat

private lemma supportedInclusion_condition
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supportedInclusion J f I ≫ restrictionComplex J f I = 0 := by
  rw [supportedInclusion, restrictionComplex, ← extendMap_comp]
  have h : (NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I ≫
      (NatTrans.mapHomologicalComplex (restriction J f) _).app I = 0 := by
    ext n : 1
    exact kernel.condition ((I.X n).obj.map f.op)
  rw [h]
  exact (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).map_zero _ _

set_option backward.isDefEq.respectTransparency false in
@[irreducible]
private noncomputable def supportedInclusion_isKernel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    IsLimit (KernelFork.ofι (supportedInclusion J f I)
      (supportedInclusion_condition J f I)) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  refine (KernelFork.isLimitMapConeEquiv _ (eval _ _ n)).symm ?_
  cases n with
  | ofNat n =>
    let S := ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I
    let A := ((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I
    let B := ((evaluationFunctor J W).mapHomologicalComplex (.up ℕ)).obj I
    let s := S.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    let a := A.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    let b := B.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    have hi : (supportedInclusion J f I).f n =
        s.hom ≫ kernel.ι ((I.X n).obj.map f.op) ≫ a.inv := by
      exact extendMap_f _ _ (by rfl)
    have hr : (restrictionComplex J f I).f n =
        a.hom ≫ (I.X n).obj.map f.op ≫ b.inv := by
      exact extendMap_f _ _ (by rfl)
    have hm : Mono ((supportedInclusion J f I).f n) := by
      rw [hi]
      infer_instance
    refine KernelFork.IsLimit.ofι' ((supportedInclusion J f I).f n)
      (show (supportedInclusion J f I).f n ≫ (restrictionComplex J f I).f n = 0 from
        congr_hom (supportedInclusion_condition J f I) n) ?_
    intro D k hk
    change k ≫ (restrictionComplex J f I).f n = 0 at hk
    have hk' : (k ≫ a.hom) ≫ (I.X n).obj.map f.op = 0 := by
      apply (cancel_mono b.inv).1
      rw [hr] at hk
      simpa only [Category.assoc, zero_comp] using hk
    refine ⟨kernel.lift _ (k ≫ a.hom) hk' ≫ s.inv, ?_⟩
    rw [hi]
    simp
  | negSucc n =>
    refine KernelFork.IsLimit.ofι ((supportedInclusion J f I).f (Int.negSucc n))
      (show (supportedInclusion J f I).f (Int.negSucc n) ≫
        (restrictionComplex J f I).f (Int.negSucc n) = 0 from
        congr_hom (supportedInclusion_condition J f I) (Int.negSucc n))
      (fun _ _ ↦ 0) ?_ ?_
    · intro D g hg
      exact (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I
        |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
          (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_tgt _ _
    · intro D g hg m hm
      exact (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I
        |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
          (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
private lemma restrictionComplex_epi
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (n : ℤ) :
    Epi ((restrictionComplex J f I.cocomplex).f n) := by
  cases n with
  | ofNat n =>
    have : Epi ((I.cocomplex.X n).obj.map f.op) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (injective_sheaf_mono_restriction.{u + 1, u, u + 1} J _ f)
    have h := extendMap_f
      ((NatTrans.mapHomologicalComplex (restriction J f) _).app I.cocomplex)
      ComplexShape.embeddingUpNat (show
        ComplexShape.embeddingUpNat.f n = Int.ofNat n from rfl)
    dsimp only [restrictionComplex]
    rw [h]
    change Epi (_ ≫ (I.cocomplex.X n).obj.map f.op ≫ _)
    infer_instance
  | negSucc n =>
    exact (HomologicalComplex.isZero_extend_X
      (((evaluationFunctor J W).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
      ComplexShape.embeddingUpNat (Int.negSucc n)
      (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).epi _

@[irreducible]
private noncomputable def supportKernelIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supported J f I ≅ kernel (restrictionComplex J f I) := by
  let e := (supportedInclusion_isKernel J f I).conePointUniqueUpToIso
    (kernelIsKernel (restrictionComplex J f I))
  exact e

private lemma supportKernelIso_ι
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    (supportKernelIso J f I).hom ≫ kernel.ι (restrictionComplex J f I) =
      supportedInclusion J f I := by
  unfold supportKernelIso
  exact (supportedInclusion_isKernel J f I).conePointUniqueUpToIso_hom_comp
    (kernelIsKernel (restrictionComplex J f I)) WalkingParallelPair.zero

set_option backward.isDefEq.respectTransparency false in
private lemma projection_f {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (p : ℤ) :
    (projection r).f p =
      ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) := by
  simp [projection, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.shiftFunctorAdd_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.mappingCone.fst,
    CochainComplex.HomComplex.Cochain.rightShift_v]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_fst {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (p : ℤ) :
    (relativeFiberMap r r' a b h).f p ≫
      ((CochainComplex.mappingCone r').shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r' (p - 1) p (by change p - 1 + 1 = p; omega) =
    ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) ≫ a.f p := by
  change (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1) ≫
        (𝟙 _ ≫ homotopyCofiber.fstX r' (p - 1) p _) =
      (𝟙 _ ≫ homotopyCofiber.fstX r (p - 1) p _) ≫ a.f p
  simp only [Category.id_comp]
  apply homotopyCofiber.ext_from_X r p (p - 1) (by change p - 1 + 1 = p; omega)
  all_goals simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
    homotopyCofiber.inrCompHomotopy_hom, sub_add_cancel]

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_snd {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (p : ℤ) :
    (relativeFiberMap r r' a b h).f p ≫
      ((CochainComplex.mappingCone r').shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.sndX r' (p - 1) =
    ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.sndX r (p - 1) ≫ b.f (p - 1) := by
  change (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1) ≫
        (𝟙 _ ≫ homotopyCofiber.sndX r' (p - 1)) =
      (𝟙 _ ≫ homotopyCofiber.sndX r (p - 1)) ≫ b.f (p - 1)
  simp only [Category.id_comp]
  apply homotopyCofiber.ext_from_X r p (p - 1) (by change p - 1 + 1 = p; omega)
  all_goals simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
    homotopyCofiber.inrCompHomotopy_hom, sub_add_cancel]

private lemma triangleSquare {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) : TriangleSquare r r' a b h := by
  constructor
  · ext p : 1
    simpa only [comp_f, projection_f, Category.assoc] using fiberMap_fst r r' a b h p
  · ext p : 1
    change b.f (p - 1) ≫ (CochainComplex.mappingCone.inr r').f (p - 1) =
      (CochainComplex.mappingCone.inr r).f (p - 1) ≫
        (homotopyCofiber.mapArrowHom r r'
          (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1)
    simp [CochainComplex.mappingCone.inr, homotopyCofiber.mapArrowHom]

private lemma exists_kernelModel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) :
    ∃ κ : kernel (restrictionComplex J f I.cocomplex) ⟶ fiber J f I.cocomplex,
      QuasiIso κ ∧ κ ≫ projection (restrictionComplex J f I.cocomplex) =
        kernel.ι (restrictionComplex J f I.cocomplex) ∧
      ∀ n : ℤ,
        κ.f n ≫ ((CochainComplex.mappingCone
          (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
            (-1) n (n - 1) (by omega)).hom ≫
          homotopyCofiber.sndX (restrictionComplex J f I.cocomplex) (n - 1) = 0 ∧
        κ.f n ≫ ((CochainComplex.mappingCone
          (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
            (-1) n (n - 1) (by omega)).hom ≫
          homotopyCofiber.fstX (restrictionComplex J f I.cocomplex) (n - 1) n
            (by change n - 1 + 1 = n; omega) =
          (kernel.ι (restrictionComplex J f I.cocomplex)).f n := by
  let _ := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  obtain ⟨κ, hc, hq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi
      (restrictionComplex J f I.cocomplex) (restrictionComplex_epi J f I)
  refine ⟨κ, hq, ?_, hc⟩
  ext p : 1
  simpa only [comp_f, projection_f, Category.assoc] using (hc p).2

set_option backward.isDefEq.respectTransparency false in
private lemma kernelSquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b) :
    kernel.map _ _ a b h.symm ≫ R'.κ =
      R.κ ≫ relativeFiberMap _ _ a b h := by
  ext n : 1
  apply (cancel_mono ((CochainComplex.mappingCone
    (restrictionComplex K f' I'.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom).1
  apply homotopyCofiber.ext_to_X (restrictionComplex K f' I'.cocomplex) (n - 1) n
    (by change n - 1 + 1 = n; omega)
  · simp only [comp_f, Category.assoc, (R'.κ_components n).2,
      fiberMap_fst, reassoc_of% ((R.κ_components n).2)]
    have hh : kernel.map _ _ a b h.symm ≫
        kernel.ι (restrictionComplex K f' I'.cocomplex) =
      kernel.ι (restrictionComplex J f I.cocomplex) ≫ a := by simp
    exact congr_hom hh n
  · simp only [comp_f, Category.assoc, (R'.κ_components n).1,
      fiberMap_snd, reassoc_of% ((R.κ_components n).1), comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma computation_natural
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {G H : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}}
    [G.Additive] [H.Additive] (τ : G ⟶ H)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (q : ℕ) :
    (computation J G I q).inv ≫ (NatTrans.rightDerived τ q).app F =
      homologyMap (extendMap ((NatTrans.mapHomologicalComplex τ _).app I.cocomplex)
        ComplexShape.embeddingUpNat) (q : ℤ) ≫ (computation J H I q).inv := by
  rw [InjectiveResolution.rightDerived_app_eq τ I q]
  dsimp only [computation, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ homologyMap _ q ≫ _ = _
  rw [extendHomologyIso_hom_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma computation_coefficients
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    (G : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [G.Additive]
    {F F' : Sheaf J AddCommGrpCat.{u + 1}} (α : F ⟶ F')
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (φ : I.cocomplex ⟶ I'.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = α ≫ I'.ι.f 0)
    (q : ℕ) :
    (computation J G I q).inv ≫ (G.rightDerived q).map α =
      homologyMap (extendMap ((G.mapHomologicalComplex (.up ℕ)).map φ)
        ComplexShape.embeddingUpNat) (q : ℤ) ≫ (computation J G I' q).inv := by
  dsimp only [computation, Iso.trans_inv, Iso.symm_inv]
  rw [Category.assoc,
    InjectiveResolution.isoRightDerivedObj_inv_naturality α I I' φ hφ G q]
  rw [extendHomologyIso_hom_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_realization
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) :
    Nonempty (Realization J f I) := by
  obtain ⟨κ, hκ, hproj, hc⟩ := exists_kernelModel J f I
  have : QuasiIso κ := hκ
  let k := supportKernelIso J f I.cocomplex
  have hr : Epi (restrictionComplex J f I.cocomplex) :=
    epi_of_epi_f _ (restrictionComplex_epi J f I)
  have hs : (ShortComplex.mk (kernel.ι (restrictionComplex J f I.cocomplex))
      (restrictionComplex J f I.cocomplex) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _
      mono_f := inferInstance
      epi_g := hr }
  let e (q : ℕ) :=
    (asIso (homologyMap κ (q : ℤ))).symm ≪≫
      (homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) (q : ℤ)).mapIso k.symm ≪≫
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).symm
  refine ⟨{ kernelIso := k
            kernel_components := ?_
            κ := κ
            κ_quasiIso := hκ
            κ_components := hc
            exact := hs
            e := e
            normalization := ?_
            forget := ?_
            localization := ?_ }⟩
  · intro n
    change (k.hom ≫ kernel.ι (restrictionComplex J f I.cocomplex)).f n = _
    rw [supportKernelIso_ι]
    exact extendMap_f _ _ (by rfl)
  · intro q
    change homologyMap k.hom (q : ℤ) ≫ homologyMap κ (q : ℤ) ≫
      inv (homologyMap κ (q : ℤ)) ≫ homologyMap k.inv (q : ℤ) ≫ _ = _
    simp only [IsIso.hom_inv_id_assoc]
    rw [← homologyMap_comp_assoc, k.hom_inv_id, homologyMap_id, Category.id_comp]
    rfl
  · intro q
    apply (cancel_epi (homologyMap k.hom (q : ℤ) ≫ homologyMap κ (q : ℤ))).1
    simp only [Category.assoc, e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      asIso_inv, IsIso.hom_inv_id_assoc]
    change homologyMap k.hom (q : ℤ) ≫ homologyMap k.inv (q : ℤ) ≫ _ = _
    rw [← homologyMap_comp_assoc, k.hom_inv_id, homologyMap_id, Category.id_comp]
    rw [computation_natural]
    have hp := congrArg (fun t ↦ homologyMap t (q : ℤ)) hproj
    rw [homologyMap_comp] at hp
    rw [reassoc_of% hp, ← homologyMap_comp_assoc, supportKernelIso_ι]
    rfl
  · intro q
    have hb := CochainComplex.kernelShiftedCone_boundary
      (restrictionComplex J f I.cocomplex) hs κ hc (q : ℤ)
    dsimp only [boundary]
    rw [hb]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
      Category.assoc, IsIso.hom_inv_id_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma realization_ι
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (R : Realization J f I) :
    R.kernelIso.hom ≫ kernel.ι (restrictionComplex J f I.cocomplex) =
      supportedInclusion J f I.cocomplex := by
  ext n : 1
  cases n with
  | ofNat n =>
    rw [comp_f]
    have hi := extendMap_f
      ((NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I.cocomplex)
      ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = Int.ofNat n from rfl)
    exact (R.kernel_components n).trans hi.symm
  | negSucc n =>
    exact (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I.cocomplex
      |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
        (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma realization_natural
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b)
    (s : supported J f I.cocomplex ⟶ supported K f' I'.cocomplex)
    (hs : s ≫ supportedInclusion K f' I'.cocomplex =
      supportedInclusion J f I.cocomplex ≫ a)
    (q : ℕ)
    (d : ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).obj F ⟶
      ((Sheaf.supportedSectionsFunctor K AddCommGrpCat.{u + 1} f').rightDerived q).obj F')
    (hd : (computation J
        (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv ≫ d =
      homologyMap s (q : ℤ) ≫ (computation K
        (Sheaf.supportedSectionsFunctor K AddCommGrpCat.{u + 1} f') I' q).inv) :
    homologyMap (relativeFiberMap _ _ a b h) (q : ℤ) ≫ (R'.e q).hom =
      (R.e q).hom ≫ d := by
  have : QuasiIso R.κ := R.κ_quasiIso
  have hs' : s ≫ R'.kernelIso.hom =
      R.kernelIso.hom ≫ kernel.map _ _ a b h.symm := by
    apply (cancel_mono (kernel.ι (restrictionComplex K f' I'.cocomplex))).1
    simp only [Category.assoc, kernel.lift_ι]
    rw [realization_ι, ← Category.assoc, realization_ι, hs]
  have hh : R.kernelIso.hom ≫ R.κ ≫ relativeFiberMap _ _ a b h =
      s ≫ R'.kernelIso.hom ≫ R'.κ := by
    rw [← kernelSquare J K f f' I I' R R' a b h, ← Category.assoc, ← hs']
    simp only [Category.assoc]
  have hH := congrArg (fun t ↦ homologyMap t (q : ℤ)) hh
  simp only [homologyMap_comp] at hH
  apply (cancel_epi (homologyMap R.kernelIso.hom (q : ℤ) ≫
    homologyMap R.κ (q : ℤ))).1
  simp only [Category.assoc]
  rw [reassoc_of% hH, R'.normalization, ← hd, reassoc_of% (R.normalization q)]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_system
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    (P : ∀ {V W : C}, (W ⟶ V) → Prop)
    (hmono : ∀ {V W : C} (f : W ⟶ V), P f → Mono f) : Nonempty (System J P) := by
  classical
  let R : ∀ {V W : C} (f : W ⟶ V), P f →
      ∀ {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F),
        Realization J f I := fun {V W} f hf {F} I ↦ Classical.choice (by
    have := hmono f hf
    exact exists_realization J f I)
  refine ⟨{ realization := R, coefficients := ?_, objects := ?_ }⟩
  · intro V W f hf F F' α I I' φ hφ h q
    refine ⟨?_, triangleSquare _ _ _ _ h⟩
    refine realization_natural J J f f I I' (R f hf I) (R f hf I')
      _ _ h
      (extendMap (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
         (.up ℕ)).map φ) ComplexShape.embeddingUpNat) ?_ q _
      (computation_coefficients J _ α I I' φ hφ q)
    dsimp only [supportedInclusion, coefficientMap]
    rw [← extendMap_comp, ← extendMap_comp]
    congr 1
    exact (NatTrans.mapHomologicalComplex (forgetSupport J f) (.up ℕ)).naturality φ
  · intro V W V' W' f f' hf hf' v w hs F I h q
    refine ⟨?_, triangleSquare _ _ _ _ h⟩
    refine realization_natural J J f f' I I (R f hf I) (R f' hf' I)
      _ _ h
      (extendMap ((NatTrans.mapHomologicalComplex (supportRestriction J f f' v w hs)
        (.up ℕ)).app I.cocomplex) ComplexShape.embeddingUpNat) ?_ q _
      (computation_natural J (supportRestriction J f f' v w hs) I q)
    dsimp only [supportedInclusion, restrictionComplex]
    rw [← extendMap_comp, ← extendMap_comp]
    congr 1
    ext n : 1
    simp [supportRestriction, forgetSupport, restriction]

private noncomputable def transposeLift (T : Scheme.{u})
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    I ⟶ ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
       (.up ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit _).app I ≫
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
       (.up ℕ)).map β

private noncomputable def supportPullback (T : Scheme.{u}) {V W : T.Etale}
    (f : W ⟶ V)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    supported T.smallEtaleTopology f I ⟶
      supported (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K :=
  extendMap (((Sheaf.supportedSectionsFunctor T.smallEtaleTopology
    AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℕ)).map (transposeLift T β))
    ComplexShape.embeddingUpNat

end RelativeCone

end Etale
end AlgebraicGeometry
