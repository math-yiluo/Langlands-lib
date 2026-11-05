import Langlands.AlgebraicGeometry.Picard.ArtinianTestDeformations
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le

/-! # Actual pointed Picard lifting along square-zero Artinian arrows -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation

namespace ArtinianSquareZeroPicardLifting

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  {A B : ArtinianTest k K} (q : A ⟶ B)

/-- Equip an ordinary lift with the residue identification prescribed by its target. -/
def repointedLift (L : ArtinianTestDeformations.Deformations f M B)
    (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (e : (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N ≅
      L.right.of) : ArtinianTestDeformations.Deformations f M A :=
  ArtinianTestDeformations.mk f M A N
    (ArtinianTestDeformations.reductionIso f M L ≪≫
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.reduction B))).mapIso
        e.symm ≪≫
      (PointedTestDeformations.reductionComparison f (ArtinianTest.pointedMap q)
        (Core.mk N)).symm)

/-- The original underlying lift isomorphism now respects the specified residue data. -/
def repointedLiftIso (L : ArtinianTestDeformations.Deformations f M B)
    (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (e : (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N ≅
      L.right.of) :
    (ArtinianTestDeformations.restrict f M q).obj (repointedLift f M q L N e) ≅ L :=
  StructuredArrow.isoMk (Core.isoMk e) (by
    apply CoreHom.ext
    change ArtinianTestDeformations.reductionIso f M
        ((ArtinianTestDeformations.restrict f M q).obj (repointedLift f M q L N e)) ≪≫
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.reduction B))).mapIso e =
        ArtinianTestDeformations.reductionIso f M L
    rw [ArtinianTestDeformations.restrict_obj_reductionIso]
    simp [repointedLift, ArtinianTestDeformations.mk,
      ArtinianTestDeformations.reductionIso, PointedTestDeformations.mk,
      PointedTestDeformations.reductionIso])

/-- The compatible pointed isomorphism has exactly the supplied underlying isomorphism. -/
lemma repointedLiftIso_underlying
    (L : ArtinianTestDeformations.Deformations f M B)
    (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (e : (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N ≅
      L.right.of) :
    (repointedLiftIso f M q L N e).hom.right.iso = e := rfl

/-- Pointed lift existence is equivalent to ordinary actual bundle lift existence. -/
theorem pointed_lift_iff (L : ArtinianTestDeformations.Deformations f M B) :
    (∃ N : ArtinianTestDeformations.Deformations f M A,
      Nonempty ((ArtinianTestDeformations.restrict f M q).obj N ≅ L)) ↔
    (∃ N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)),
      Nonempty (((LineBundle.pullback
        ((relativeSpace f).map (ArtinianTest.baseMap q))).obj N).obj ≅ L.right.of.obj)) := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩
    exact ⟨N.right.of, ⟨(LineBundle.forget _).mapIso e.hom.right.iso⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    let e' := ObjectProperty.isoMk _ e
    exact ⟨repointedLift f M q L N e', ⟨repointedLiftIso f M q L N e'⟩⟩

/-- A surjective test arrow induces an actual relative closed immersion. -/
lemma relativeMap_isClosedImmersion (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    IsClosedImmersion ((relativeSpace f).map (ArtinianTest.baseMap q)) :=
  relativeSpace_map_property f @IsClosedImmersion (ArtinianTest.baseMap q)
    (ArtinianTest.baseMap_isClosedImmersion q hq)

/-- The source test ring acts on sections of an actual open of its relative scheme. -/
def testSectionHom (A : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    A.algebra →+* Γ((relativeSpace f).obj (ArtinianTest.base A), U) :=
  (((relativeProjection f).app (ArtinianTest.base A)).appLE ⊤ U le_top).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).inv.hom

/-- Base change of a surjective test arrow extends its kernel on actual affine sections. -/
lemma relativeMap_affine_ker (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    RingHom.ker (((relativeSpace f).map (ArtinianTest.baseMap q)).app U).hom =
      (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom).map (testSectionHom f A U) := by
  let i := (relativeSpace f).map (ArtinianTest.baseMap q)
  let p := (relativeProjection f).app (ArtinianTest.base B)
  have H := relativeProjection_isPullback f (ArtinianTest.baseMap q)
  have hUY : i ⁻¹ᵁ U = i ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY
    (isAffineOpen_top (Spec (CommRingCat.of A.algebra)))
    (isAffineOpen_top (Spec (CommRingCat.of B.algebra))) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY).mp h1
  have hleg : (ArtinianTest.baseMap q).left.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).hom ≫
        CommRingCat.ofHom (ArtinianTest.toAlgHom q).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of B.algebra)).inv := by
    change (Spec.map (CommRingCat.ofHom (ArtinianTest.toAlgHom q).toRingHom)).appTop = _
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hg : Function.Surjective ((ArtinianTest.baseMap q).left.appLE ⊤ ⊤ le_top).hom := by
    rw [hleg]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B.algebra)).inv).2.comp
      (hq.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).hom).2)
  have hker :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout
      h2 hg
  rw [Scheme.Hom.appLE_eq_app] at hker
  rw [hker, hleg]
  have hbase : RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of A.algebra)).hom ≫
        CommRingCat.ofHom (ArtinianTest.toAlgHom q).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of B.algebra)).inv).hom =
      (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom).map
        (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).inv.hom := by
    change RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of B.algebra)).inv.hom.comp
        ((ArtinianTest.toAlgHom q).toRingHom.comp
          (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).hom.hom)) = _
    rw [RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B.algebra)).inv).1, ← RingHom.comap_ker]
    exact (Ideal.map_symm
      ((Scheme.ΓSpecIso (CommRingCat.of A.algebra)).commRingCatIsoToRingEquiv)).symm
  rw [hbase, Ideal.map_map]
  rfl

/-- Every vanishing power of a surjective test kernel stays zero on the actual relative scheme. -/
lemma relativeMap_ker_pow_eq_bot
    [QuasiCompact ((relativeSpace f).map (ArtinianTest.baseMap q))]
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) (n : ℕ)
    (hn : (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom) ^ n = ⊥) :
    ((relativeSpace f).map (ArtinianTest.baseMap q)).ker ^ n = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((((relativeSpace f).map (ArtinianTest.baseMap q)).ker).ideal U) ^ n = ⊥
  rw [Scheme.Hom.ker_apply, relativeMap_affine_ker f q hq U.1 U.2,
    ← Ideal.map_pow, hn, Ideal.map_bot]

/-- Elementary Artinian surjections give actual relative square-zero immersions. -/
lemma relativeMap_ker_sq
    [QuasiCompact ((relativeSpace f).map (ArtinianTest.baseMap q))]
    (hq : ArtinianTest.IsElementarySurjection q) :
    ((relativeSpace f).map (ArtinianTest.baseMap q)).ker ^ 2 = ⊥ :=
  relativeMap_ker_pow_eq_bot f q hq.1 2 hq.ker_sq

instance testSpace_compactSpace [QuasiCompact f] (A : ArtinianTest k K) :
    CompactSpace ((relativeSpace f).obj (ArtinianTest.base A)) :=
  inferInstanceAs (CompactSpace
    (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k A.algebra))) f : Scheme.{u}))

section Obstruction

variable [QuasiCompact f]

/-- The actual ideal-module H² obstruction of the underlying bundle of a pointed deformation. -/
def obstruction (hq : ArtinianTest.IsElementarySurjection q)
    (L : ArtinianTestDeformations.Deformations f M B) :
    SquareZeroUnitCohomology.idealCohomology
      ((relativeSpace f).map (ArtinianTest.baseMap q)) 2 :=
  let : IsClosedImmersion ((relativeSpace f).map (ArtinianTest.baseMap q)) :=
    relativeMap_isClosedImmersion f q hq.1
  SquareZeroPicardObstruction.obstructionMap _
    (relativeMap_ker_sq f q hq) L.right.of.classOf

/-- Actual pointed lifts exist precisely when the actual H² obstruction vanishes. -/
theorem pointed_lift_iff_obstruction (hq : ArtinianTest.IsElementarySurjection q)
    (L : ArtinianTestDeformations.Deformations f M B) :
    (∃ N : ArtinianTestDeformations.Deformations f M A,
      Nonempty ((ArtinianTestDeformations.restrict f M q).obj N ≅ L)) ↔
      obstruction f M q hq L = 0 := by
  let : IsClosedImmersion ((relativeSpace f).map (ArtinianTest.baseMap q)) :=
    relativeMap_isClosedImmersion f q hq.1
  exact (pointed_lift_iff f M q L).trans
    (SquareZeroPicardObstruction.lineBundle_lift_iff _
      (relativeMap_ker_sq f q hq) L.right.of)

/-- Vanishing of actual ideal-module H² supplies a lift retaining the specified residue data. -/
theorem exists_lift_of_h2_zero (hq : ArtinianTest.IsElementarySurjection q)
    (L : ArtinianTestDeformations.Deformations f M B)
    (h : ∀ a : SquareZeroUnitCohomology.idealCohomology
      ((relativeSpace f).map (ArtinianTest.baseMap q)) 2, a = 0) :
    ∃ N : ArtinianTestDeformations.Deformations f M A,
      Nonempty ((ArtinianTestDeformations.restrict f M q).obj N ≅ L) :=
  (pointed_lift_iff_obstruction f M q hq L).mpr (h _)

end Obstruction

end ArtinianSquareZeroPicardLifting

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
