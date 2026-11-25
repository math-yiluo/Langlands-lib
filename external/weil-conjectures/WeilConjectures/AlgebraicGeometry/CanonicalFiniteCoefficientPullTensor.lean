/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalFiniteCoefficientTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Tensor coherence of the canonical finite coefficient pullback comparison

Source: the coefficient-presentation step in det-thm-sf-pf-finite.proof.md.
(blueprint: lem-d5-canonical-finite-coefficient-pull-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 30000] CondensedRing.monoidal_upperStar
attribute [local irreducible] Mod.monoidalClosed

-- Check monoidal coherence without unfolding the concrete coefficient functors.
private theorem canonical_monoidal_inverse_exchange
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (NX : C ≌ D) (NY : E ≌ F)
    [NX.functor.Monoidal] [NX.inverse.Monoidal] [NX.IsMonoidal]
    [NY.functor.Monoidal] [NY.inverse.Monoidal] [NY.IsMonoidal]
    (R : C ⥤ E) (S : D ⥤ F) [R.LaxMonoidal] [S.LaxMonoidal]
    (i : R ⋙ NY.functor ≅ NX.functor ⋙ S) [NatTrans.IsMonoidal i.hom] :
    NatTrans.IsMonoidal (Iso.inverseCompIso (G := NX)
      (Iso.isoCompInverse (H := NY) i ≪≫ Functor.associator _ _ _)).hom := by
  let k : R ≅ NX.functor ⋙ S ⋙ NY.inverse :=
    Iso.isoCompInverse (H := NY) i ≪≫ Functor.associator _ _ _
  have : NatTrans.IsMonoidal k.hom := by
    dsimp only [k, Iso.isoCompInverse]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  change NatTrans.IsMonoidal (Iso.inverseCompIso (G := NX) k).hom
  dsimp only [Iso.inverseCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

variable (A : Type) [CommRing A]

private theorem canonicalFixed_tensor_pure (T : Scheme.{u})
    {M M' N N' : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : M ⟶ M') (g : N ⟶ N') (V : T.ProEtᵒᵖ)
    (x : M.obj.obj V) (y : N.obj.obj V) :
    ((f ⊗ₘ g).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
          M N V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        M' N' V ((f.hom.app V) x) ((g.hom.app V) y) := by
  exact (congrArg (fun z ↦ (z.app V) (x ⊗ₜ[ULift.{u + 1} A] y))
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) f g)).symm

private theorem canonicalFixed_push_pure {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (V : Y.ProEtᵒᵖ)
    (x : M.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V))
    (y : N.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)) :
    ((Functor.LaxMonoidal.μ
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p) M N).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y) (ULift.{u + 1} A)
          _ _ V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X) (ULift.{u + 1} A)
        M N ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V) x y := by
  exact congrArg (fun g ↦ (g (x ⊗ₜ[ULift.{u + 1} A] y)))
    (Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) M N V)


-- The composite adjunctions require large monoidal instance arguments.
-- The two composite adjunctions carry large monoidal structures.
/-- The adjoint-normalized finite coefficient pullback comparison is monoidal
for the section-normalized tensor structures.

Source: det-thm-sf-pf-finite.proof.md, coefficient realization and the proper
projection square; the geometric adjunction and its tensor comparison.
(blueprint: lem-d5-canonical-finite-coefficient-pull-tensor).

Proof: the direct-image coefficient comparison is identity on underlying sections
over every fibre product. The lax tensor maps of both direct images send a pure
pairing to the same pairing on that fibre product. Substituting the two normalization
identities therefore proves the tensor equation for the direct-image comparison;
the unit equation follows from uniqueness of the unit of the induced monoid.
Conjugate this monoidal comparison under the two geometric adjunctions and the
coefficient-equivalence adjunctions. The conjugate unit and tensor equations show
that its left-adjoint mate is monoidal. This mate is exactly the published
upperStarFiniteCoefficientModEquivalenceIso, since that is defined by the same
conjugate of the identity-on-sections direct-image comparison. This argument uses
neither properness nor boundedness, and also covers identity and empty morphisms. -/
theorem canonicalFiniteCoefficientPullTensor
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (mX : (finiteCoefficientModEquivalence X A).functor.Monoidal)
    (mY : (finiteCoefficientModEquivalence Y A).functor.Monoidal)
    (hX : CanonicalFiniteTensorNormalized A X mX)
    (hY : CanonicalFiniteTensorNormalized A Y mY) :
    letI := mX
    letI := mY
    NatTrans.IsMonoidal (upperStarFiniteCoefficientModEquivalenceIso f A).hom := by
  let := mX
  let := mY
  let : (CondensedRing.upperStar (Profinite.continuousMapRingObj A) f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar (Profinite.continuousMapRingObj A) f).toOplaxMonoidal
  let aI := CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj A) f
  let := aI.rightAdjointLaxMonoidal
  have hi : NatTrans.IsMonoidal (lowerStarFiniteCoefficientModEquivalenceIso f A).hom := by
    apply FiniteDiscreteOrdinary.isMonoidal_of_tensor
    intro M N
    apply ConstantScalarRestriction.fixedTensor_ext
      (Scheme.ProEt.topology Y) (ULift.{u + 1} A)
    intro V x y
    change (((lowerStarFiniteCoefficientModEquivalenceIso f A).hom.app (M ⊗ N)).hom.app V)
      ((((finiteCoefficientModEquivalence Y A).functor.map
        (Functor.LaxMonoidal.μ (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj A) f) M N)).hom.app V)
        ((Functor.LaxMonoidal.μ (finiteCoefficientModEquivalence Y A).functor _ _).hom.app V
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y)
            (ULift.{u + 1} A) _ _ V _ _))) = _
    rw [hY]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ModuleCat.comp_apply]
    rw [canonicalFixed_tensor_pure A]
    change _ = ((Functor.LaxMonoidal.μ (finiteCoefficientModEquivalence X A).functor M N).hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V))
      (((Functor.LaxMonoidal.μ
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) _ _).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y)
            (ULift.{u + 1} A) _ _ V _ _))
    rw [canonicalFixed_push_pure A, hX]
    exact ModuleRingedComparison.canonicalInternalPush_normalized _ f M N V x y
  let NX := finiteCoefficientModEquivalence X A
  let NY := finiteCoefficientModEquivalence Y A
  let : NX.functor.Monoidal := mX
  let : NY.functor.Monoidal := mY
  let : NX.inverse.Monoidal := NX.inverseMonoidal
  let : NY.inverse.Monoidal := NY.inverseMonoidal
  let : NX.IsMonoidal := inferInstance
  let : NY.IsMonoidal := inferInstance
  let i : CondensedRing.lowerStar (Profinite.continuousMapRingObj A) f ⋙ NY.functor ≅
      NX.functor ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
    lowerStarFiniteCoefficientModEquivalenceIso f A
  have : NatTrans.IsMonoidal i.hom := hi
  let k := Iso.isoCompInverse (H := NY) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := NX) k
  have : NatTrans.IsMonoidal kr.hom :=
    canonical_monoidal_inverse_exchange NX NY _ _ i
  let a := NY.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := aI.comp NX.toAdjunction
  have hj : NatTrans.IsMonoidal ((conjugateIsoEquiv b a).symm kr).hom := by
    change NatTrans.IsMonoidal ((conjugateEquiv b a).symm kr.hom)
    constructor
    · apply (cancel_mono (Functor.OplaxMonoidal.η _)).mp
      rw [Category.assoc, conjugateEquiv_symm_app_unit_comp_η b a kr.hom,
        Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
    · intro M N
      apply (cancel_epi (Functor.OplaxMonoidal.δ _ M N)).mp
      apply (cancel_mono (Functor.OplaxMonoidal.δ _ M N)).mp
      simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc,
        conjugateEquiv_symm_app_tensor_comp_δ b a kr.hom,
        Functor.Monoidal.μ_δ, Category.comp_id]
  unfold upperStarFiniteCoefficientModEquivalenceIso
  change NatTrans.IsMonoidal ((conjugateIsoEquiv b a).symm kr).inv
  infer_instance

end AlgebraicGeometry.ProEtale
