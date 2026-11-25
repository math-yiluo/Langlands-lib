/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryEvaluationMate
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived geometric evaluation from the ordinary singleton mate

Source: Zheng Construction 4.1; Stacks 06YT and 07A6.
(blueprint: lem-coef-geometric-evaluation-mate-invertible)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

-- Keep the universal derivation packaged while using its normalized interface.
@[irreducible]
private noncomputable def singletonModel (n : ℕ) :
    SheafOfModules.SystemDerivedLeftExtension
      (evaluation.{c, v, max c v r} J B τ n)
      (SheafOfModules.systemLevelKFlat.{c, v, max c v r} (rings.{c, v, max c v r} J B τ) n) := by
  classical
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence.{c, v, max c v r} R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let L := SheafOfModules.systemSingleFunctor S T R n
  have : L.Additive := SheafOfModules.systemSingleFunctorAdditive S T R n
  have : (L ⋙ E.functor).Additive := inferInstance
  let η : E.inverse ⋙ SheafOfModules.systemEvaluation R n ≅
      evaluation.{c, v, max c v r} J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let adj := ((SheafOfModules.systemSingleAdjunction S T R n).comp
    E.toAdjunction).ofNatIsoRight η
  have hinv {K L' : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ}
      (f : K ⟶ L') (hK : SheafOfModules.systemLevelKFlat.{c, v, max c v r} R n K)
      (hL : SheafOfModules.systemLevelKFlat.{c, v, max c v r} R n L') (hf : QuasiIso f) :
      QuasiIso (((L ⋙ E.functor).mapHomologicalComplex (.up ℤ)).map f) := by
    have := SheafOfModules.systemSingle_preserves.{c, v, max c v r} S T R n f hK hL hf
    let i := Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ E.functor)) (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (i.app K) (i.app L') (i.hom.naturality f).symm)).1
        (inferInstance : QuasiIso
          ((E.functor.mapHomologicalComplex (.up ℤ)).map
            ((L.mapHomologicalComplex (.up ℤ)).map f)))
  exact (Classical.choice (SheafOfModules.nonempty_normalizedLeftExtension
    (evaluation.{c, v, max c v r} J B τ n) (L ⋙ E.functor) adj
    (SheafOfModules.systemLevelKFlat.{c, v, max c v r} R n)
    (SheafOfModules.systemLevel_kFlatResolution.{c, v, max c v r} R n) hinv)).toExtension

variable
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (Mod.{c, v, max c v r} J' (O.coefficients n))]
  [Abelian.HasKInjectiveResolutions
    (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition)]

-- Compare the singleton adjunctions in four independently derived module categories.
/-- Invertibility of the canonical right mate of exact geometric evaluation.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10; Stacks 03EL,
06YT and 07A6 (blueprint: lem-coef-geometric-evaluation-mate-invertible).

Proof: transport ordinary singleton extension across strictSystemSequenceEquivalence
and derive its normalized adjunction on flat-term K-flat complexes. The ordinary
singleton mate is invertible. Inverse image preserves this resolving class, so the
normalized extension comparison identifies its derived mate on representatives and
makes it invertible. The iterated-mates identity expresses the right geometric mate
as the conjugate of this invertible singleton mate. Conjugation preserves inverses. -/
theorem geometricEvaluationMate_isIso [PreservesFiniteLimits uInv] (n : ℕ) :
    IsIso (mateEquiv O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O) n).inv)) := by
  classical
  let d := singletonModel.{c, v, r} J B τ n
  let d' := singletonModel.{c, v, r} J' O.coefficients O.coefficientTransition n
  let G := (O.inverseImage n).modules
  let δ := (O.ordinaryPullEvaluation n).symm
  let δD := (geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O n).symm
  let a := ((mateEquiv d.ordinaryAdj d'.ordinaryAdj).symm
    (TwoSquare.mk _ _ _ _ δ.hom))
  have ha : IsIso a := geometricOrdinaryEvaluationMate_isIso
    J B τ J' uInv uPush adjSet O n d.ordinary d'.ordinary d.ordinaryAdj d'.ordinaryAdj
  let aD := ((mateEquiv d.adjunction d'.adjunction).symm
    (TwoSquare.mk _ _ _ _ δD.hom))
  have hflat (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
      (hP : SheafOfModules.systemLevelKFlat.{c, v, max c v r} (rings.{c, v, max c v r} J B τ) n P) :
      SheafOfModules.systemLevelKFlat.{c, v, max c v r}
        (rings.{c, v, max c v r} J' O.coefficients O.coefficientTransition) n
          ((G.mapHomologicalComplex (.up ℤ)).obj P) := by
    exact inverseImage_good.{c, v, r} J B τ J' uInv uPush adjSet O n P hP.1 hP.2
  have haD : IsIso aD := by
    refine SheafOfModules.derivedExtensionMate_isIso d d' G O.pull G.mapDerivedCategory
      G.mapDerivedCategoryFactors δD.hom δ.hom ?_
      (@asIso _ _ _ _ a ha) ?_
      (SheafOfModules.systemLevel_kFlatResolution
        (rings.{c, v, max c v r} J B τ) n) hflat
    · intro K
      have hδ : δD.hom = (Functor.mapDerivedCategorySquareIso δ).hom := by
        simp only [δD, geometryPullEvaluation, δ, Functor.mapDerivedCategorySquareIso,
          Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
          Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
      rw [hδ]
      exact exactSquare_fac δ K
    · intro P
      exact (unit_mateEquiv_symm d.ordinaryAdj d'.ordinaryAdj
        (TwoSquare.mk _ _ _ _ δ.hom) P).symm
  have h := iterated_mateEquiv_conjugateEquiv d.adjunction d'.adjunction
    (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
    O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
    ((mateEquiv d.adjunction d'.adjunction).symm
      (TwoSquare.mk _ _ _ _ δD.hom))
  rw [Equiv.apply_symm_apply] at h
  change IsIso (mateEquiv O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
    (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ δD.hom))
  rw [h]
  infer_instance

end WeilConjectures.SemilinearSections
