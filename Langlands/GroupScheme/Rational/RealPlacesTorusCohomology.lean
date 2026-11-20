import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.AlgClosedFiniteKernelHomIsogeny
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.FiniteSeparableQuotientLifts
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.QuotientPointCocycleComparison
import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesSurjectivity
import Langlands.GroupScheme.Torus.InducedTorusResolution
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.Torus.RealTorusPointApproximation
import Langlands.GroupScheme.Torus.WeilRestrictionSemilocalCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Localization of torus cohomology at the real places -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
private theorem isTrivial_of_weilPresentation_baseChange
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (B : Type u) [CommRing B] [Algebra F B] [Module.Finite F B] [Module.Projective F B]
    {P : GroupScheme (Spec (CommRingCat.of F))}
    (e : P ≅ WeilGm.groupScheme (CommRingCat.of F) B)
    {U : Over (Spec (CommRingCat.of K))} [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (d : Cocycle ((baseChange (algebraBaseMap F K)).obj P) U) : d.IsTrivial := by
  let eK : (baseChange (algebraBaseMap F K)).obj P ≅
      WeilGm.groupScheme (CommRingCat.of K) (K ⊗[F] B) :=
    (baseChange (algebraBaseMap F K)).mapIso e ≪≫
      WeilGm.algebraBaseChangeIso (CommRingCat.of F) (CommRingCat.of K) B
  exact Cocycle.isTrivial_of_weilPresentation_of_semilocal
    (A := CommRingCat.of K) (B := CommRingCat.of (K ⊗[F] B)) d eK

private theorem isTrivial_of_inducedTorus_baseChange
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (P : CommGroupScheme (Spec (CommRingCat.of F))) (hP : IsInducedTorus P)
    {U : Over (Spec (CommRingCat.of K))} [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (d : Cocycle ((baseChange (algebraBaseMap F K)).obj P.toGrp) U) : d.IsTrivial := by
  have hp := hP
  obtain ⟨D, _, _, hfin, hgal, hsplit, _⟩ := hp
  let : FiniteDimensional F D := hfin
  let : IsGalois F D := hgal
  obtain ⟨n, Es, ⟨e⟩⟩ := inducedTorusWeilDecomposition F D P hsplit hP
  exact isTrivial_of_weilPresentation_baseChange F K (∀ j, Es j)
    (Langlands.CommGroupScheme.groupIso e) d

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_fieldCover_properties
    (F L : Type u) [Field F] [Field L] [Algebra F L] {S : Scheme.{u}}
    (b : S ⟶ Spec (CommRingCat.of F)) :
    let U := (Over.pullback b).obj (ringTest F L)
    IsAffineHom U.hom ∧ Flat U.hom ∧ Surjective U.hom := by
  let U := ringTest F L
  let : Flat U.hom := (fieldExtension_fpqc F L).2.1
  let : Surjective U.hom := (fieldExtension_fpqc F L).1
  let : IsAffineHom U.hom := inferInstanceAs (IsAffineHom (Spec.algebraMap F L))
  let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    isAffineHom_isStableUnderBaseChange
  change IsAffineHom (pullback.snd U.hom b) ∧ Flat (pullback.snd U.hom b) ∧
    Surjective (pullback.snd U.hom b)
  exact ⟨MorphismProperty.pullback_snd (P := @IsAffineHom) U.hom b ‹IsAffineHom U.hom›,
    inferInstance, inferInstance⟩

private theorem kernelRange_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {T P Q : GroupScheme S} {i : T ⟶ P} {q : P ⟶ Q}
    (h : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q)) :
    SubgroupFunctor.range ((baseChange b).map i) =
      SubgroupFunctor.range (kernelι ((baseChange b).map q)) := by
  rw [SubgroupFunctor.range_baseChangeHom, kernel_range_baseChange, h]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_local_quotientPoint
    (F K L : Type u) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    {T Q : GroupScheme (Spec (CommRingCat.of F))}
    {P : CommGroupScheme (Spec (CommRingCat.of F))} (hP : IsInducedTorus P)
    {i : T ⟶ P.toGrp} (hi : IsClosedSubgroup i) (q : P.toGrp ⟶ Q)
    (hker : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q)) :
    let b := algebraBaseMap F K
    let U := (Over.pullback b).obj (ringTest F L)
    let iK := (baseChange b).map i
    let qK := (baseChange b).map q
    letI : Mono iK.hom.hom := (hi.baseChange b).mono_overHom
    ∀ d : Cocycle ((baseChange b).obj T) U,
      ∃ (y : rationalPoints ((baseChange b).obj Q))
        (g : U ⟶ ((baseChange b).obj P.toGrp).X)
        (hg : g ≫ qK.hom.hom = toUnit U ≫ y),
        ∀ {Z : Over (Spec (CommRingCat.of K))} (a s : Z ⟶ U),
          d.toFun a s =
            (QuotientPointCocycle.obstruction iK qK (kernelRange_baseChange b hker) y g hg).toFun
              a s := by
  intro b U iK qK d
  let : Mono iK.hom.hom := (hi.baseChange b).mono_overHom
  obtain ⟨haff, hflat, hsurj⟩ := pullback_fieldCover_properties F L b
  let : IsAffineHom U.hom := haff
  let : Flat U.hom := hflat
  let : Surjective U.hom := hsurj
  let : EffectiveEpi U.hom := inferInstance
  exact QuotientPointCocycle.exists_quotientPoint_of_isTrivial_map iK qK
    (kernelRange_baseChange b hker) d
    (isTrivial_of_inducedTorus_baseChange F K P hP (d.map iK))

set_option backward.isDefEq.respectTransparency false in
private theorem rationalCoeffEquiv_baseChangeSectionHom
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (Q : GroupScheme (Spec (CommRingCat.of F))) (z : rationalPoints Q) :
    rationalCoeffEquiv K ((baseChange (algebraBaseMap F K)).obj Q)
      (baseChangeSectionHom (algebraBaseMap F K) Q z) =
      (Lie.affineBaseChangeEquiv F K Q K).symm
        (GaloisPoint.extend F K Q (rationalCoeffEquiv F Q z)) := by
  apply (Lie.affineBaseChangeEquiv F K Q K).injective
  rw [MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left, rationalCoeffEquiv_left, baseChangeSectionHom_fst]
  change algebraBaseMap F K ≫ z.left = algebraBaseMap F K ≫ (rationalCoeffEquiv F Q z).left
  rw [rationalCoeffEquiv_left]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_point_map_eq_norm
    (K M : Type u) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M]
    [IsGalois K M] [IsAlgClosed M]
    {P Q : CommGroupScheme (Spec (CommRingCat.of K))}
    [IsAffine P.X.left] [IsAffine Q.X.left]
    [LocallyOfFiniteType P.X.hom] [LocallyOfFiniteType Q.X.hom]
    (q : P.toGrp ⟶ Q.toGrp) (hq : Surjective q.hom.hom.left)
    (r : Lie.AffinePoints Q.toGrp M) :
    ∃ x : rationalPoints P.toGrp,
      rationalCoeffEquiv K Q.toGrp (x ≫ q.hom.hom) = GaloisPoint.norm K M Q r := by
  let b := GaloisPointComparison.baseMap K M
  let qM := (baseChange b).map q
  let : LocallyOfFiniteType ((baseChange b).obj P.toGrp).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd P.X.hom b))
  let : LocallyOfFiniteType ((baseChange b).obj Q.toGrp).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Q.X.hom b))
  let : Surjective qM.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq
  let rM := (baseChangeCoeffEquiv K M Q.toGrp).symm r
  obtain ⟨p, hp⟩ := HomIsogeny.rationalPoint_surjective qM rM
  change p ≫ qM.hom.hom = rM at hp
  let t := baseChangeCoeffEquiv K M P.toGrp p
  have ht : affinePointsTarget P.toGrp q (CommAlgCat.of K M) t = r := by
    rw [← baseChangeCoeffEquiv_map, rationalPoints.map_apply, hp]
    exact (baseChangeCoeffEquiv K M Q.toGrp).apply_symm_apply r
  let x := (rationalCoeffEquiv K P.toGrp).symm (GaloisPoint.norm K M P t)
  refine ⟨x, ?_⟩
  change rationalCoeffEquiv K Q.toGrp (rationalPoints.map q x) = _
  rw [rationalCoeffEquiv_map, MulEquiv.apply_symm_apply]
  have hnorm := GaloisPoint.norm_naturality K M (T := P) (U := Q) (Additive.ofMul q) t
  change affinePointsTarget P.toGrp q (CommAlgCat.of K K) (GaloisPoint.norm K M P t) =
    GaloisPoint.norm K M Q (affinePointsTarget P.toGrp q (CommAlgCat.of K M) t) at hnorm
  rwa [ht] at hnorm

local notation "K[" w "]" => InfinitePlace.Completion (Subtype.val w)

/-- For a surjection of tori over a number field, one global point of the
target realizes all prescribed real-place points modulo the local images. -/
def RealQuotientPointApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    {P Q : CommGroupScheme (Spec (CommRingCat.of F))},
    IsTorus P.toGrp → IsTorus Q.toGrp →
    ∀ (q : P.toGrp ⟶ Q.toGrp), Surjective q.hom.hom.left →
      ∀ (y : ∀ w : RealPlaceIndex F,
        rationalPoints ((baseChange (algebraBaseMap F (K[w]))).obj Q.toGrp)),
        ∃ z : rationalPoints Q.toGrp, ∀ w : RealPlaceIndex F,
          let b := algebraBaseMap F (K[w])
          ∃ x : rationalPoints ((baseChange b).obj P.toGrp),
            y w = baseChangeSectionHom b Q.toGrp z * (x ≫ ((baseChange b).map q).hom.hom)

set_option backward.isDefEq.respectTransparency false in
/-- Apply simultaneous norm approximation to the target torus and lift
each correcting norm through the surjection. -/
theorem realQuotientPointApproximation : RealQuotientPointApproximationStatement.{u} := by
  intro F _ _ P Q hP hQ q hq y
  let Qloc (w : RealPlaceIndex F) := (baseChange (algebraBaseMap F (K[w]))).obj Q.toGrp
  let p (w : RealPlaceIndex F) : Lie.AffinePoints (Qloc w) (K[w]) :=
    rationalCoeffEquiv (K[w]) (Qloc w) (y w)
  obtain ⟨z, hz⟩ := RealTorusNorm.realTorusPointApproximation F Q hQ p
  let zF := (rationalCoeffEquiv F Q.toGrp).symm z
  refine ⟨zF, fun w => ?_⟩
  let b := algebraBaseMap F (K[w])
  let Pw := (CommGroupScheme.baseChange b).obj P
  let Qw := (CommGroupScheme.baseChange b).obj Q
  let qW : Pw.toGrp ⟶ Qw.toGrp := (baseChange b).map q
  let : IsAffine Pw.X.left := SplittingAssembly.isAffine_of_isTorus Pw.toGrp
    (hP.baseChange (K := K[w]))
  let : IsAffine Qw.X.left := SplittingAssembly.isAffine_of_isTorus Qw.toGrp
    (hQ.baseChange (K := K[w]))
  let : Smooth Pw.X.hom := (hP.baseChange (K := K[w])).smooth
  let : Smooth Qw.X.hom := (hQ.baseChange (K := K[w])).smooth
  let : FiniteDimensional (K[w]) (AlgebraicClosure (K[w])) :=
    RealTorusNorm.completionClosure_finiteDimensional w
  let : CharZero (K[w]) := charZero_of_injective_algebraMap (algebraMap F (K[w])).injective
  obtain ⟨r, hr⟩ := hz w
  have hqW : Surjective qW.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq
  obtain ⟨x, hx⟩ := exists_point_map_eq_norm (K[w]) (AlgebraicClosure (K[w]))
    (P := Pw) (Q := Qw) qW hqW r
  let eQ := rationalCoeffEquiv (K[w]) Qw.toGrp
  have hzF : eQ (baseChangeSectionHom b Q.toGrp zF) =
      (Lie.affineBaseChangeEquiv F (K[w]) Q.toGrp (K[w])).symm
        (GaloisPoint.extend F (K[w]) Q.toGrp z) := by
    have h := rationalCoeffEquiv_baseChangeSectionHom F (K[w]) Q.toGrp zF
    have hzz : rationalCoeffEquiv F Q.toGrp zF = z :=
      (rationalCoeffEquiv F Q.toGrp).apply_symm_apply z
    rw [hzz] at h
    exact h
  refine ⟨x, eQ.injective ?_⟩
  exact (show eQ (y w) = _ from hr).trans
    ((congrArg₂ (· * ·) hzF hx).symm.trans (eQ.map_mul _ _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_refined_quotient_lift
    (F L : Type u) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {P Q : GroupScheme (Spec (CommRingCat.of F))} (q : P ⟶ Q)
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left] (z : rationalPoints Q) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E),
      FiniteDimensional F E ∧ Algebra.IsSeparable F E ∧
      ∃ (_e : L →ₐ[F] E) (g : ringTest F E ⟶ P.X),
        g ≫ q.hom.hom = toUnit (ringTest F E) ≫ z := by
  let v := toUnit (ringTest F L) ≫ z
  let Y : Over (Spec (CommRingCat.of L)) := Over.mk (pullback.snd q.hom.hom.left v.left)
  let : Smooth Y.hom := inferInstanceAs (Smooth (pullback.snd q.hom.hom.left v.left))
  let : Surjective Y.hom := inferInstanceAs (Surjective (pullback.snd q.hom.hom.left v.left))
  let : Nonempty Y.left := by
    obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨p, _⟩ := (inferInstance : Surjective Y.hom).surj a
    exact ⟨p⟩
  obtain ⟨E, _, _, hfin, hsep, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.exists_finiteSeparable_point_of_smooth (F := L) Y
  let : Algebra F E := ((algebraMap L E).comp (algebraMap F L)).toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L E := hfin
  let : Algebra.IsSeparable L E := hsep
  let e := IsScalarTower.toAlgHom F L E
  have hw : w.left ≫ pullback.snd q.hom.hom.left v.left = (ringTestMap F e).left := Over.w w
  let g : ringTest F E ⟶ P.X := Over.homMk (w.left ≫ pullback.fst q.hom.hom.left v.left) (by
    rw [Category.assoc, ← Over.w q.hom.hom, pullback.condition_assoc,
      Over.w v, ← Category.assoc, hw, Over.w (ringTestMap F e)])
  refine ⟨E, inferInstance, inferInstance, FiniteDimensional.trans F L E,
    Algebra.IsSeparable.trans F L E, e, g, ?_⟩
  have hg : g ≫ q.hom.hom = ringTestMap F e ≫ v := by
    apply Over.OverMorphism.ext
    change (w.left ≫ pullback.fst q.hom.hom.left v.left) ≫ q.hom.hom.left =
      (ringTestMap F e).left ≫ v.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  exact hg.trans (comp_toUnit_assoc _ _)

private theorem cocycle_eq_of_toFun_eq
    {S : Scheme.{u}} {T : GroupScheme S} {U : Over S} {ξ ζ : Cocycle T U}
    (h : ∀ {Z : Over S} (a s : Z ⟶ U), ξ.toFun a s = ζ.toFun a s) : ξ = ζ := by
  cases ξ
  cases ζ
  congr
  funext Z a s
  exact h a s

set_option backward.isDefEq.respectTransparency false in
private theorem exists_baseChange_obstruction
    {S S' : Scheme.{u}} {T P Q : GroupScheme S} {U : Over S} {V : Over S'}
    (b : S' ⟶ S) (r : (Over.map b).obj V ⟶ U)
    (i : T ⟶ P) (q : P ⟶ Q)
    (hker : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q))
    [Mono i.hom.hom] [Mono ((baseChange b).map i).hom.hom]
    (z : 𝟙_ (Over S) ⟶ Q.X) (g : U ⟶ P.X) (hg : g ≫ q.hom.hom = toUnit U ≫ z) :
    let i' := (baseChange b).map i
    let q' := (baseChange b).map q
    let z' := baseChangeSectionHom b Q z
    ∃ (g' : V ⟶ ((baseChange b).obj P).X) (hg' : g' ≫ q'.hom.hom = toUnit V ≫ z'),
      (QuotientPointCocycle.obstruction i q hker z g hg).baseChange b V r =
        QuotientPointCocycle.obstruction i' q' (kernelRange_baseChange b hker) z' g' hg' := by
  intro i' q' z'
  let g' := (baseChangePointsEquiv b P V).symm (r ≫ g)
  have hg' : g' ≫ q'.hom.hom = toUnit V ≫ z' := by
    apply (baseChangePointsEquiv b Q V).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, Category.assoc, hg,
      comp_toUnit_assoc]
    apply Over.OverMorphism.ext
    change (V.hom ≫ b) ≫ z.left =
      (V.hom ≫ (baseChangeSectionHom b Q z).left) ≫ pullback.fst Q.X.hom b
    simp only [Category.assoc, baseChangeSectionHom_fst]
  refine ⟨g', hg', cocycle_eq_of_toFun_eq (fun {Z} a s => ?_)⟩
  apply (cancel_mono i'.hom.hom).mp
  apply (baseChangePointsEquiv b P Z).injective
  rw [baseChangePointsEquiv_comp, Cocycle.baseChange_toFun]
  simp only [QuotientPointCocycle.obstruction_toFun_comp, map_mul, map_inv,
    baseChangePointsEquiv_naturality, g', MulEquiv.apply_symm_apply, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem refine_eq_obstruction
    {S : Scheme.{u}} {T P Q : GroupScheme S} {U V : Over S}
    (i : T ⟶ P) (q : P ⟶ Q)
    (hker : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q))
    [Mono i.hom.hom] (d : Cocycle T U) (s : V ⟶ U)
    (y : 𝟙_ (Over S) ⟶ Q.X) (g : U ⟶ P.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y)
    (hd : ∀ {Z : Over S} (a c : Z ⟶ U),
      d.toFun a c = (QuotientPointCocycle.obstruction i q hker y g hg).toFun a c) :
    ∃ (hg' : (s ≫ g) ≫ q.hom.hom = toUnit V ≫ y),
      d.refine s = QuotientPointCocycle.obstruction i q hker y (s ≫ g) hg' := by
  have hg' : (s ≫ g) ≫ q.hom.hom = toUnit V ≫ y := by
    rw [Category.assoc, hg, comp_toUnit_assoc]
  refine ⟨hg', cocycle_eq_of_toFun_eq (fun a c => (cancel_mono i.hom.hom).mp ?_)⟩
  rw [Cocycle.refine_toFun, hd, QuotientPointCocycle.obstruction_toFun_comp,
    QuotientPointCocycle.obstruction_toFun_comp, Category.assoc, Category.assoc]

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every family of real-place torus classes comes from a global class after
one finite separable refinement of the original cover. -/
theorem realPlacesTorusCohomologySurjectivity : RealPlacesTorusCohomologySurjectivityStatement.{u} := by
  classical
  intro F _ _ T hT L _ _ _ _ c
  obtain ⟨P, Q, i, q, hP, hQ, hi, hq⟩ := inducedTorusResolution F T hT
  have hker : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q) := hq.2.2.2.symm
  let : Mono i.hom.hom := hi.mono_overHom
  have hlocal (w : RealPlaceIndex F) :=
    exists_local_quotientPoint F (K[w]) L hP hi q hker (c w)
  choose y gLoc hgLoc hdLoc using hlocal
  obtain ⟨z, hz⟩ := realQuotientPointApproximation F hP.isTorus hQ q hq.2.1 y
  let : IsAffineHom P.X.hom := hP.isTorus.isRelativeTorus.isAffineHom
  let : IsAffineHom Q.X.hom := hQ.isRelativeTorus.isAffineHom
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  let : Surjective q.hom.hom.left := hq.2.1
  let : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨hi.mono_overHom, rfl⟩ hT.smooth
  obtain ⟨E, _, _, hfin, hsep, e, g, hg⟩ := exists_refined_quotient_lift F L q z
  refine ⟨E, ‹Field E›, ‹Algebra F E›, hfin, hsep, e,
    QuotientPointCocycle.obstruction i q hker z g hg, fun w => ?_⟩
  let b := algebraBaseMap F (K[w])
  let i' := (baseChange b).map i
  let q' := (baseChange b).map q
  let V := (Over.pullback b).obj (ringTest F E)
  let r := (Over.mapPullbackAdj b).counit.app (ringTest F E)
  let s := (Over.pullback b).map (ringTestMap F e)
  let : Mono i'.hom.hom := (hi.baseChange b).mono_overHom
  have hker' := kernelRange_baseChange b hker
  obtain ⟨g', hg', hglob⟩ := exists_baseChange_obstruction b r i q hker z g hg
  obtain ⟨hgLoc', hloc⟩ :=
    refine_eq_obstruction i' q' hker' (c w) s (y w) (gLoc w) (hgLoc w) (hdLoc w)
  obtain ⟨x, hx⟩ := hz w
  change ((QuotientPointCocycle.obstruction i q hker z g hg).baseChange b V r).Cohomologous
    ((c w).refine s)
  rw [hglob, hloc]
  exact QuotientPointCocycle.cohomologous_obstruction_of_mul i' q' hker'
    (baseChangeSectionHom b Q.toGrp z) (y w) x g' (s ≫ gLoc w) hg' hgLoc' hx

end Langlands.GroupScheme
