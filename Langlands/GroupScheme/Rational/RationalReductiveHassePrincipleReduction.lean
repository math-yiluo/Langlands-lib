import Langlands.GroupScheme.Rational.RationalReductiveHassePrincipleStatement
import Langlands.GroupScheme.Rational.FiniteSeparableCocycleKernelReduction
import Langlands.GroupScheme.CocycleInnerDifference
import Langlands.GroupScheme.InnerTwistQuotient
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistence
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.FppfQuotientUniqueness
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology
import Langlands.Global.AdelicWeilRestrictionArchimedean

/-! # Arithmetic inputs for the reductive Hasse principle over `ℚ` -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

local notation "S" => Spec (CommRingCat.of ℚ)
local notation "F∞" => Rat.infinitePlace.Completion
local notation "p∞" => Spec.algebraMap ℚ Rat.infinitePlace.Completion

private theorem denseRange_changeRing_realCompletion (T : GroupScheme S) [IsAffine T.X.left]
    (h : DenseRange (fun x : RingPoint ℚ T.X ℚ => x.changeRing (Algebra.ofId ℚ ℝ))) :
    DenseRange (fun x : RingPoint ℚ T.X ℚ => x.changeRing (Algebra.ofId ℚ F∞)) := by
  let e := Langlands.Global.AdelicWeilRestriction.realRatCompletion
  let c : RingPoint ℚ T.X ℝ → RingPoint ℚ T.X F∞ := fun x => x.changeRing e.toAlgHom
  have hcont : Continuous c := by
    apply (affineSchemePointHomeomorph ℚ T.X F∞).isInducing.continuous_iff.mpr
    change Continuous (fun x : RingPoint ℚ T.X ℝ =>
      affineSchemePointEquiv ℚ T.X F∞ (x.changeRing e.toAlgHom))
    simp only [affineSchemePointEquiv_changeRing]
    exact (AlgPoint.continuous_mapCoefficients e.toAlgHom
      Langlands.Global.AdelicWeilRestriction.continuous_realRatCompletion).comp
        (affineSchemePointHomeomorph ℚ T.X ℝ).continuous
  have hsurj : Function.Surjective c := by
    intro x
    refine ⟨x.changeRing e.symm.toAlgHom, ?_⟩
    apply (affineSchemePointEquiv ℚ T.X F∞).injective
    apply AlgPoint.ext
    intro a
    simp only [c, affineSchemePointEquiv_changeRing, AlgPoint.mapCoefficients_apply]
    exact e.apply_symm_apply _
  have hcomp : c ∘ (fun x : RingPoint ℚ T.X ℚ => x.changeRing (Algebra.ofId ℚ ℝ)) =
      fun x : RingPoint ℚ T.X ℚ => x.changeRing (Algebra.ofId ℚ F∞) := by
    funext x
    apply (affineSchemePointEquiv ℚ T.X F∞).injective
    apply AlgPoint.ext
    intro a
    simp only [Function.comp_apply, c, affineSchemePointEquiv_changeRing,
      AlgPoint.mapCoefficients_apply]
    exact e.commutes _
  rw [← hcomp]
  exact hsurj.denseRange.comp h hcont

private theorem locallyCohomologous_map {G Q : GroupScheme S} {U : Over S}
    {ξ ζ : Cocycle G U} (h : ξ.LocallyCohomologous ζ) (q : G ⟶ Q) :
    (ξ.map q).LocallyCohomologous (ζ.map q) := by
  intro i
  let b := algebraBaseMap ℚ (Langlands.Global.placeCompletion ℚ i)
  let V := (Over.pullback b).obj U
  let r := (Over.mapPullbackAdj b).counit.app U
  let q' := (baseChange b).map q
  have heq (coc : Cocycle G U) {Z : Over (Spec (CommRingCat.of
      (Langlands.Global.placeCompletion ℚ i)))} (a c : Z ⟶ V) :
      ((coc.map q).baseChange b V r).toFun a c = ((coc.baseChange b V r).map q').toFun a c := by
    apply (baseChangePointsEquiv b Q Z).injective
    rw [Cocycle.baseChange_toFun]
    change _ = baseChangePointsEquiv b Q Z ((coc.baseChange b V r).toFun a c ≫ q'.hom.hom)
    dsimp only [q']
    rw [baseChangePointsEquiv_comp, Cocycle.baseChange_toFun]
    rfl
  obtain ⟨f, hf⟩ := (h i).map q'
  refine ⟨f, fun {Z} a c => ?_⟩
  change ((ζ.map q).baseChange b V r).toFun a c =
    (a ≫ f)⁻¹ * ((ξ.map q).baseChange b V r).toFun a c * (c ≫ f)
  rw [heq ζ, heq ξ]
  exact hf a c

/-- Real detection of trivial cocycles for simply connected groups and real
approximation for tori suffice for the reductive Hasse principle over `ℚ`. -/
def RationalReductiveHassePrincipleReductionStatement : Prop :=
  (∀ H : GroupScheme S, IsSimplyConnected H → Cocycle.TrivialityReflectsFrom H F∞) →
  (∀ (T : GroupScheme S) [IsAffine T.X.left], IsTorus T →
    DenseRange (fun x : RingPoint ℚ T.X ℚ => x.changeRing (Algebra.ofId ℚ ℝ))) →
  RationalReductiveHassePrincipleStatement

/-- Apply the quotient and kernel reduction to the inner difference of the two
cocycles on a finite Galois refinement. -/
theorem rationalReductiveHassePrincipleReduction :
    RationalReductiveHassePrincipleReductionStatement := by
  intro hsc happ G D T d q hG hd hD hq hT L _ _ _ _ ξ ζ hlocal
  obtain ⟨T₀, q₀, _, hq₀, hT₀, _⟩ := cocenterQuotientExistence ℚ G D d hG hd
  have htorus : IsTorus T := IsTorus.of_iso (FppfQuotientComparison.fppfIso hq hq₀) hT₀
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T htorus
  let : IsCommMonObj T.X := htorus.isCommMonObj
  let : QuasiCompact q.hom.hom.left := inferInstance
  have hrep : (SubgroupFunctor.range d).IsRepresentedBy d := hd.2 ▸ hd.isRepresentedBy
  let : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel hrep hD.isSemisimple.isConnectedReductive.smooth
  let : Surjective q.hom.hom.left := hq.2.1
  have hK : IsSimplyConnected (kernel q) := IsSimplyConnected.of_iso (hq.kernelIso hrep).symm hD
  obtain ⟨E, hE, hGal, ⟨φ⟩⟩ := exists_finite_galois_algHom ℚ L
  let : FiniteDimensional ℚ E := hE
  let : IsGalois ℚ E := hGal
  let s := ringTestMap ℚ φ
  let ξ₀ : Cocycle G (ringTest ℚ L) := ξ
  let ζ₀ : Cocycle G (ringTest ℚ L) := ζ
  let ξ' : Cocycle G (Over.mk (algebraBaseMap ℚ E)) := ξ₀.refine s
  let ζ' : Cocycle G (Over.mk (algebraBaseMap ℚ E)) := ζ₀.refine s
  have hlocal₀ : ξ₀.LocallyCohomologous ζ₀ := hlocal
  have hlocal' : ξ'.LocallyCohomologous ζ' := hlocal₀.refine s
  obtain ⟨H, e, hH, he⟩ := finiteGaloisTwistExistence ℚ E G G hG.isAffineHom
    (AutomorphicAction.conjugation (𝟙 G)) ζ'
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc ℚ E
  let : Surjective (Over.mk (algebraBaseMap ℚ E)).hom := hsurj
  let : Flat (Over.mk (algebraBaseMap ℚ E)).hom := hflat
  let : QuasiCompact (Over.mk (algebraBaseMap ℚ E)).hom := hqc
  let r := e.descendInnerQuotient q ζ' he
  obtain ⟨hrsmooth, hrsurj⟩ := e.smooth_surjective_descendInnerQuotient q ζ' he
  let : Smooth r.hom.hom.left := hrsmooth
  let : Surjective r.hom.hom.left := hrsurj
  let : IsAffineHom H.X.hom := hH
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hKr : IsSimplyConnected (kernel r) :=
    e.isSimplyConnected_kernel_descendInnerQuotient q ζ' he hK
  let diff := Cocycle.innerDifference ξ' ζ' e he
  let U := Over.mk (algebraBaseMap ℚ E)
  let V := (Over.pullback p∞).obj U
  let pr := (Over.mapPullbackAdj p∞).counit.app U
  have hDiffReal : (diff.baseChange p∞ V pr).IsTrivial :=
    Cocycle.isTrivial_innerDifference_baseChange ξ' ζ' e he p∞ V pr
      (hlocal' (.inl Rat.infinitePlace))
  have hDiffQuotient : (diff.map r).IsTrivial := by
    obtain ⟨f, hf⟩ := hT E (ξ'.map q) (ζ'.map q) (locallyCohomologous_map hlocal' q)
    refine ⟨f, fun a b => ?_⟩
    change (diff.map r).toFun a b = (a ≫ f) * (b ≫ f)⁻¹
    rw [Cocycle.map_innerDifference_toFun ξ' ζ' e he q r
      (e.comp_descendInnerQuotient q ζ' he), hf]
    simp only [Cocycle.twist]
    rw [mul_right_comm ((a ≫ f)⁻¹) _ (b ≫ f), mul_comm ((a ≫ f)⁻¹) (b ≫ f)]
    group
  let : NontriviallyNormedField F∞ := infiniteCompletionNontriviallyNormedField Rat.infinitePlace
  have hdense := denseRange_changeRing_realCompletion T (happ T htorus)
  have hcoset := Cocycle.exists_quotient_point_in_translate (F := F∞) r hdense
  have hDetect := hsc (kernel r) hKr
  have hDiff : diff.IsTrivial := Cocycle.isTrivial_of_quotient_and_baseChange
    (F := F∞) (L := (E : Type)) r hcoset hDetect diff hDiffQuotient hDiffReal
  have h' := (Cocycle.isTrivial_innerDifference_iff ξ' ζ' e he).mp hDiff
  let : Algebra L E := φ.toRingHom.toAlgebra
  obtain ⟨hp₁, hp₂, hp₃⟩ := fieldExtension_fpqc L E
  let : Surjective s.left := hp₁
  let : Flat s.left := hp₂
  let : QuasiCompact s.left := hp₃
  exact (ξ₀.cohomologous_refine_iff ζ₀ s).mp h'

end Langlands.GroupScheme
