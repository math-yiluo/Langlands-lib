import Langlands.AlgebraicGeometry.Picard.FieldUniversalRigidifiedPicardTangentH1Proof
import Langlands.AlgebraicGeometry.Picard.DualGroupScheme
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof

/-! # The tangent space of the chosen dual at its origin -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
open Langlands.AlgebraicGeometry.Picard.DualNumberThickening
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

variable {k : Type u} [Field k]

/-- Every point of the dual-number scheme with values in a field factors through its
closed point, since the image of `ε` squares to zero. -/
lemma dualNumber_fieldPoint_factor (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (DualNumber k))) :
    ∃ s' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k),
      s = s' ≫ dualNumberAugmentation k := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.comp (algebraMap k (DualNumber k)))), ?_⟩
  rw [dualNumberAugmentation, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  have hε : φ.hom (TrivSqZeroExt.inr 1) = 0 := by
    apply pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    rw [← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero]
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
    rw [TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  change φ.hom x = φ.hom (algebraMap k (DualNumber k) x.fst)
  conv_lhs => rw [hx]
  rw [map_add, map_mul, hε, mul_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl]

variable (A : AbelianScheme (Spec (CommRingCat.of k)))

private lemma classesPullback_comp' {T U V : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ U) (h' : U ⟶ V) (q : RigidifiedClasses A V) :
    classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
        (classesPullback A.X.hom (unitSection A) (unitSection_comp A) h' q) =
      classesPullback A.X.hom (unitSection A) (unitSection_comp A) (h ≫ h') q := by
  refine Quotient.inductionOn q (fun F ↦ ?_)
  exact Quotient.sound ⟨(relativePullbackComp RigidifiedModule.pullbackCoherence
    A.X.hom (unitSection A) (unitSection_comp A) h h').app F⟩

/-- A rigidified class over the dual numbers whose restriction to the closed point is the
trivial class satisfies the geometric Picard-zero condition: every geometric point of the dual
numbers factors through the closed point. -/
lemma isPicardZeroClass_of_closedPoint_trivial
    (q : RigidifiedClasses A (dualNumberTest k))
    (hq : classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (dualNumberClosedPoint k) q =
      classOf A.X.hom (unitSection A) (unitSection_comp A)
        (relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :
    IsPicardZeroClass A q := by
  revert hq
  refine Quotient.inductionOn q (fun L hL ↦ ?_)
  refine (isPicardZeroClass_classOf A L).mpr ?_
  refine (picardZeroGeometricDetection _ A _ L).mpr ?_
  intro K _ _ s
  obtain ⟨s', hs⟩ := dualNumber_fieldPoint_factor K s
  let h : Over.mk (s ≫ (dualNumberTest k).hom) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.homMk s' (by
      change s' ≫ 𝟙 _ = s ≫ dualNumberProjection k
      rw [hs, Category.assoc, dualNumberAugmentation_comp_dualNumberProjection])
  have hcomp : (Over.homMk s rfl : Over.mk (s ≫ (dualNumberTest k).hom) ⟶ dualNumberTest k) =
      h ≫ dualNumberClosedPoint k :=
    Over.OverMorphism.ext hs
  refine (isPicardZeroClass_classOf A _).mp ?_
  have hc : classOf A.X.hom (unitSection A) (unitSection_comp A)
      ((relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ (dualNumberTest k).hom) ⟶ dualNumberTest k)).obj L) =
      classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ (dualNumberTest k).hom) ⟶ dualNumberTest k)
        (classOf A.X.hom (unitSection A) (unitSection_comp A) L) := rfl
  have hL' : classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (dualNumberClosedPoint k) (classOf A.X.hom (unitSection A) (unitSection_comp A) L) =
      classOf A.X.hom (unitSection A) (unitSection_comp A)
        (relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
          (Over.mk (𝟙 (Spec (CommRingCat.of k))))) := hL
  rw [hc, hcomp, ← classesPullback_comp', hL', classesPullback_trivial]
  exact isPicardZeroFamily_trivial A _

variable (hA : HasDualScheme A)

/-- Dual-number points of the chosen dual through its origin are exactly the first-order
rigidified classes, by classification through the chosen Poincaré family. -/
def dualFirstOrderClassifyingEquiv :
    {t : dualNumberTest k ⟶ dualScheme A hA // dualNumberClosedPoint k ≫ t = dualOrigin A hA} ≃
      FirstOrderClasses A.X.hom (unitSection A) (unitSection_comp A) where
  toFun t := ⟨classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) (dualNumberTest k) t.val, by
    rw [← classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
      RigidifiedModule.pullbackCoherence, t.property, dualOrigin_spec]
    rfl⟩
  invFun q := ⟨dualClassify A hA (dualNumberTest k)
      ⟨q.val, isPicardZeroClass_of_closedPoint_trivial A q.val q.property⟩, by
    refine dualClassify_unique A hA _ (trivialPicardZeroClass A _) _ ?_
    rw [classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
      RigidifiedModule.pullbackCoherence, dualClassify_spec]
    exact q.property⟩
  left_inv t := Subtype.ext (dualClassify_unique A hA _ _ t.val rfl).symm
  right_inv q := Subtype.ext (dualClassify_spec A hA _ _)

@[simp]
lemma dualFirstOrderClassifyingEquiv_val
    (t : {t : dualNumberTest k ⟶ dualScheme A hA //
      dualNumberClosedPoint k ≫ t = dualOrigin A hA}) :
    (dualFirstOrderClassifyingEquiv A hA t).val =
      classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA) (dualNumberTest k) t.val :=
  rfl

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- The actual tangent module of the chosen dual at its origin is in bijection with ordinary
first-order deformations of the structure sheaf of `A`. -/
def dualTangentDeformationEquiv :
    Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA) ≃
      DeformationClasses preservation A.X.hom :=
  (tangentSpaceAtPointDerivationEquiv (dualScheme A hA) (dualOrigin A hA)).toEquiv.trans
    ((rationalStalkDerivationTangentEquiv (dualScheme A hA).hom (dualOrigin A hA).left
      (Over.w (dualOrigin A hA))).trans
      ((dualNumberTangentEquiv (dualScheme A hA) (dualOrigin A hA)).symm.trans
        ((dualFirstOrderClassifyingEquiv A hA).trans
          (firstOrderDeformationEquiv preservation A.X.hom (unitSection A)
            (unitSection_comp A)))))

@[simp]
lemma dualTangentDeformationEquiv_val
    (t : Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA)) :
    (dualTangentDeformationEquiv A hA preservation t).val =
      underlyingDualNumberClassEquiv preservation A.X.hom (unitSection A) (unitSection_comp A)
        (classifyingMap A.X.hom (unitSection A) (unitSection_comp A) (poincareFamily A hA)
          (dualNumberTest k)
          (rationalStalkDerivationPoint (dualScheme A hA) (dualOrigin A hA)
            (tangentSpaceAtPointDerivationEquiv (dualScheme A hA) (dualOrigin A hA) t))) :=
  rfl

/-- Addition of tangent vectors at the origin of the chosen dual corresponds to tensor
product of first-order deformations. The proof uses the group scheme structure of the
chosen dual, whose unit is the origin and whose multiplication classifies tensor products. -/
lemma dualTangentDeformationEquiv_add
    (t s : Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA)) :
    dualTangentDeformationEquiv A hA preservation (t + s) =
      dualTangentDeformationEquiv A hA preservation t *
        dualTangentDeformationEquiv A hA preservation s := by
  let X := (relativeSpace A.X.hom).obj (dualScheme A hA)
  let P : X.Modules := (poincareFamily A hA).obj.carrier
  have hP : Langlands.CategoryTheory.TensorInvertible P :=
    (locallyFreeRankOneIffTensorInvertible X P).mpr (poincareFamily A hA).property
  obtain ⟨N, ⟨e⟩⟩ := hP
  have hN : IsLocallyFreeRankOne N :=
    (locallyFreeRankOneIffTensorInvertible X N).mp ⟨P, ⟨(β_ N P) ≪≫ e⟩⟩
  let M : LineBundle X := ⟨N, hN⟩
  let evaluation : tensorObj P M.obj ≅ structureSheaf X :=
    (localizedTensorIso X P N).symm ≪≫ e
  let G := dualCommGroupSchemeFromEvaluation A hA preservation
    M evaluation picardZeroPullback pullbackTensorComposition pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
  let o : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := dualOrigin A hA
  have he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = o := by
    rw [CategoryTheory.Hom.one_def, dualCommGroupSchemeFromEvaluation_one, ← Category.assoc]
    convert Category.id_comp o
    exact Over.mkIdTerminal.hom_ext _ _
  let := stalkAlgebraOver G.X.hom (o.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation G.X.hom o.left (Over.w o)).toRingHom.toAlgebra
  let D₁ := tangentSpaceAtPointDerivationEquiv (dualScheme A hA) (dualOrigin A hA) t
  let D₂ := tangentSpaceAtPointDerivationEquiv (dualScheme A hA) (dualOrigin A hA) s
  have hp : rationalStalkDerivationPoint G.X o (D₁ + D₂) =
      rationalStalkDerivationPoint G.X o D₁ * rationalStalkDerivationPoint G.X o D₂ :=
    rationalStalkDerivationPoint_add_of_one_eq G.X o he D₁ D₂
  let := picardZeroClassesCommMonoid preservation pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
    A (dualNumberTest k)
  have hm := congrArg Subtype.val
    ((dualCommGroupSchemePointMulEquiv A hA preservation M evaluation picardZeroPullback
      pullbackTensorComposition pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
      tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry (dualNumberTest k)).map_mul
        (rationalStalkDerivationPoint G.X o D₁) (rationalStalkDerivationPoint G.X o D₂))
  apply Subtype.ext
  simp only [dualTangentDeformationEquiv_val, Subgroup.coe_mul]
  rw [map_add (tangentSpaceAtPointDerivationEquiv (dualScheme A hA) (dualOrigin A hA))]
  change underlyingDualNumberClassEquiv preservation A.X.hom (unitSection A) (unitSection_comp A)
      (classifyingMap A.X.hom (unitSection A) (unitSection_comp A) (poincareFamily A hA)
        (dualNumberTest k) (rationalStalkDerivationPoint G.X o (D₁ + D₂))) = _
  rw [hp]
  change underlyingDualNumberClassEquiv preservation A.X.hom (unitSection A) (unitSection_comp A)
      (dualPointClass picardZeroPullback A hA
        (rationalStalkDerivationPoint G.X o D₁ * rationalStalkDerivationPoint G.X o D₂)).val = _
  rw [dualCommGroupSchemePointMulEquiv_apply] at hm
  rw [hm]
  exact underlyingDualNumberClassEquiv_tensor preservation A.X.hom (unitSection A)
    (unitSection_comp A)
    (classifyingMap A.X.hom (unitSection A) (unitSection_comp A) (poincareFamily A hA)
      (dualNumberTest k) (rationalStalkDerivationPoint G.X o D₁))
    (classifyingMap A.X.hom (unitSection A) (unitSection_comp A) (poincareFamily A hA)
      (dualNumberTest k) (rationalStalkDerivationPoint G.X o D₂))

/-- Scalar multiplication of tangent vectors at the origin of the chosen dual is
pullback along actual epsilon scaling of the first-order thickening. -/
lemma dualTangentDeformationEquiv_smul_val (c : k)
    (t : Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA)) :
    (dualTangentDeformationEquiv A hA preservation (c • t)).val =
      LineBundle.pullbackHom preservation (scale A.X.hom c)
        (dualTangentDeformationEquiv A hA preservation t).val := by
  let e := dualOrigin A hA
  let := stalkAlgebraOver (dualScheme A hA).hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation (dualScheme A hA).hom e.left (Over.w e)).toRingHom.toAlgebra
  simp only [dualTangentDeformationEquiv_val]
  rw [map_smul (tangentSpaceAtPointDerivationEquiv (dualScheme A hA) e),
    rationalStalkDerivationPoint_smul,
    classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
      RigidifiedModule.pullbackCoherence,
    underlyingDualNumberClassEquiv_scale]

/-- The tangent space of the chosen dual at its origin is linearly equivalent to the first
cohomology of the structure sheaf of `A`, over every field and without any finiteness
hypothesis on the chosen dual. -/
theorem dualSchemeTangentH1 :
    Nonempty (Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA) ≃ₗ[k]
      (DerivedSections.relativeCohomology A.X.hom 1).obj (structureSheaf A.X.left)) := by
  let preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    @pullbackTensorComparisonIsIso.{u}
  let 𝒰 := CechResolution.orderedAffineCoverOfQuasiCompact A.X.hom
  let E : Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA) ≃+
      Additive (DeformationClasses preservation A.X.hom) :=
    { toEquiv := (dualTangentDeformationEquiv A hA preservation).trans Additive.ofMul
      map_add' := dualTangentDeformationEquiv_add A hA preservation }
  let F := E.trans (deformationH1AddEquiv preservation A.X.hom 𝒰)
  refine ⟨{ F with map_smul' := ?_ }⟩
  intro c t
  change deformationH1AddEquiv preservation A.X.hom 𝒰
      (Additive.ofMul (dualTangentDeformationEquiv A hA preservation (c • t))) =
    c • deformationH1AddEquiv preservation A.X.hom 𝒰
      (Additive.ofMul (dualTangentDeformationEquiv A hA preservation t))
  have hs : dualTangentDeformationEquiv A hA preservation (c • t) =
      scaleClass A.X.hom preservation c (dualTangentDeformationEquiv A hA preservation t) :=
    Subtype.ext (dualTangentDeformationEquiv_smul_val A hA preservation c t)
  rw [hs, deformationH1AddEquiv_scaleClass]

/-- If `A` has relative dimension `g`, the tangent space of the chosen dual at its origin is
finite-dimensional of dimension at most `g`. -/
theorem dualSchemeTangent_finrank_le (g : ℕ) (hg : A.HasRelativeDimension g) :
    FiniteDimensional k
        (Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA)) ∧
      Module.finrank k
        (Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA)) ≤ g := by
  obtain ⟨E⟩ := dualSchemeTangentH1 A hA
  obtain ⟨hfin, hle⟩ := fieldStructureSheafH1DimensionBound k A g hg
  exact ⟨Module.Finite.equiv E.symm, (LinearEquiv.finrank_eq E).trans_le hle⟩

end Langlands.AbelianScheme
