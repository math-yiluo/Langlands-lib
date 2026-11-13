import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingStatement
import Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityStatement
import Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel
import Langlands.AlgebraicGeometry.Picard.StructureKernelMorphism
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Primitive line-bundle lifting from obstruction naturality and H² injectivity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Picard.StructureKernelModule
  Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace ArtinianPrimitiveLineBundleLifting

/-- Pull back an isomorphism `m^*M ≅ p^*M ⊗ q^*M` along `F`, for maps `m' = F ≫ m`,
`p' = F ≫ p` and `q' = F ≫ q`. -/
lemma nonempty_tensor_iso_of_comp_eq {P Q Z : Scheme.{u}} (F : P ⟶ Q)
    (m p q : Q ⟶ Z) (m' p' q' : P ⟶ Z) (hm : F ≫ m = m') (hp : F ≫ p = p')
    (hq : F ≫ q = q') (M : Z.Modules)
    (e : (Scheme.Modules.pullback m).obj M ≅
      tensorObj ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback q).obj M)) :
    Nonempty ((Scheme.Modules.pullback m').obj M ≅
      tensorObj ((Scheme.Modules.pullback p').obj M) ((Scheme.Modules.pullback q').obj M)) := by
  have : IsIso (pullbackTensorComparison F) := pullbackTensorComparisonIsIso F
  let c : ∀ (r : Q ⟶ Z) (r' : P ⟶ Z), F ≫ r = r' →
      ((Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback r).obj M) ≅
        (Scheme.Modules.pullback r').obj M) :=
    fun r r' h ↦ (Scheme.Modules.pullbackComp F r).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M
  exact ⟨(c m m' hm).symm ≪≫ (Scheme.Modules.pullback F).mapIso e ≪≫
    asIso ((pullbackTensorComparison F).app
      ((Scheme.Modules.pullback p).obj M, (Scheme.Modules.pullback q).obj M)) ≪≫
    tensorMapIso (c p p' hp) (c q q' hq)⟩

/-- If `m'^*L ≅ p'^*L ⊗ q'^*L` for a line bundle `L`, then the Picard classes satisfy
`m'^*[L] = p'^*[L] + q'^*[L]`. -/
lemma pullback_classOf_eq_add {P Z : Scheme.{u}} (m' p' q' : P ⟶ Z) (L : LineBundle Z)
    (e : (Scheme.Modules.pullback m').obj L.obj ≅
      tensorObj ((Scheme.Modules.pullback p').obj L.obj)
        ((Scheme.Modules.pullback q').obj L.obj)) :
    Group.pullback m' L.classOf = Group.pullback p' L.classOf + Group.pullback q' L.classOf := by
  rw [Group.pullback_lineBundle_classOf, Group.pullback_lineBundle_classOf,
    Group.pullback_lineBundle_classOf]
  change Picard.classOf P ((LineBundle.pullback m').obj L).toInvertibleSheaf =
    Picard.classOf P ((LineBundle.pullback p').obj L).toInvertibleSheaf +
      Picard.classOf P ((LineBundle.pullback q').obj L).toInvertibleSheaf
  rw [← Picard.classOf_tensor]
  exact (Picard.classOf_eq_iff P _ _).mpr
    ⟨e ≪≫ (localizedTensorIso P ((Scheme.Modules.pullback p').obj L.obj)
      ((Scheme.Modules.pullback q').obj L.obj)).symm⟩

end ArtinianPrimitiveLineBundleLifting

/-- The implication from naturality of square-zero Picard obstructions under morphisms of
thickenings and injectivity of the reduced coproduct on the ideal H² of an elementary
Artinian thickening of an abelian scheme to the lifting of primitive line bundles along that
thickening. It is the internal anchor proposition of this module and is proved below by
`artinianPrimitiveLineBundleLiftingReduction`. -/
def ArtinianPrimitiveLineBundleLiftingReductionStatement : Prop :=
  Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u} →
    ArtinianH2PrimitiveInjectivityStatement.{u} →
      ArtinianPrimitiveLineBundleLiftingStatement.{u}

open ArtinianPrimitiveLineBundleLifting in
/-- The reduction holds: lifting of primitive line bundles along elementary Artinian
thickenings follows from obstruction naturality and reduced-coproduct H² injectivity. -/
theorem artinianPrimitiveLineBundleLiftingReduction :
    ArtinianPrimitiveLineBundleLiftingReductionStatement.{u} := by
  intro hnat hinj B' B _ _ _ _ _ _ φ hφ hker A j A₀ L hL
  obtain ⟨e⟩ := hL
  -- The thickening `A₀ ⟶ A` and its ideal.
  let i : pullback A.X.hom j ⟶ A.X.left := pullback.fst A.X.hom j
  have : IsClosedImmersion i := AffineBaseChangeKernel.isClosedImmersion φ A.X.hom hφ
  have hi : i.ker ^ 2 = ⊥ := AffineBaseChangeKernel.ker_sq φ A.X.hom hφ hker
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  -- The product `A ×_{B'} A`, its projections and group law.
  let P : Over (Spec (CommRingCat.of B')) := A.X ⨯ A.X
  let p1 : P ⟶ A.X := Limits.prod.fst
  let p2 : P ⟶ A.X := Limits.prod.snd
  let m : P ⟶ A.X := p1 * p2
  have hPq : QuasiCompact P.hom := by
    have hP : P.hom = (Over.prodLeftIsoPullback A.X A.X).hom ≫
        pullback.fst A.X.hom A.X.hom ≫ A.X.hom := by
      rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
    rw [hP]
    infer_instance
  have : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  -- The thickening `A₀ ×_B A₀ = (A ×_{B'} A) ×_{B'} B ⟶ A ×_{B'} A` and its ideal.
  let iP : pullback P.hom j ⟶ P.left := pullback.fst P.hom j
  have : IsClosedImmersion iP := AffineBaseChangeKernel.isClosedImmersion φ P.hom hφ
  have hiP : iP.ker ^ 2 = ⊥ := AffineBaseChangeKernel.ker_sq φ P.hom hφ hker
  -- Base change of morphisms `P ⟶ A.X`.
  let Fj := Over.pullback j
  let g : (P ⟶ A.X) → (pullback P.hom j ⟶ pullback A.X.hom j) := fun f ↦ (Fj.map f).left
  have w : ∀ f : P ⟶ A.X, iP ≫ f.left = g f ≫ i := fun f ↦
    (pullback.lift_fst _ _ _).symm
  let k : ∀ f : P ⟶ A.X,
      kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP) :=
    fun f ↦ StructureKernelMorphism.kernelModuleMap f.left i iP (g f) (w f)
  have hk : ∀ f : P ⟶ A.X, k f ≫ (Scheme.Modules.pushforward f.left).map (kernelModuleι iP) =
      kernelModuleι i ≫ unitToPushforwardUnit f.left := fun f ↦
    StructureKernelMorphism.kernelModuleMap_ι f.left i iP (g f) (w f)
  let pull : (P ⟶ A.X) → _ := fun f ↦
    (relativeCohomologyPullback f (kernelModule i) 2 ≫
      (relativeCohomology P.hom 2).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm (k f))).hom
  have hinj' : Function.Injective (pull m - pull p1 - pull p2) :=
    hinj B' B φ hφ hker A (k m) (k p1) (k p2) (hk m) (hk p1) (hk p2)
  -- Naturality of the obstruction.
  let y : Group (pullback A.X.hom j) := L.classOf
  let ρ := SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv A.X.hom i 2
  let ρP := SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv P.hom iP 2
  have hpull : ∀ f : P ⟶ A.X, pull f (ρ (SquareZeroPicardObstruction.obstructionMap i hi y)) =
      ρP (SquareZeroPicardObstruction.obstructionMap iP hiP (Group.pullback (g f) y)) :=
    fun f ↦ (hnat (CommRingCat.of B') A.X P f (pullback A.X.hom j) (pullback P.hom j) i iP (g f)
      hi hiP (w f) (k f) (hk f) y).symm
  -- The primitivity isomorphism, transported to `(A ×_{B'} A) ×_{B'} B`.
  let c : Fj.obj P ⟶ A₀.X ⨯ A₀.X := prod.lift (Fj.map p1) (Fj.map p2)
  have hc1 : c ≫ Limits.prod.fst = Fj.map p1 := prod.lift_fst _ _
  have hc2 : c ≫ Limits.prod.snd = Fj.map p2 := prod.lift_snd _ _
  have hcm : c ≫ ((Limits.prod.fst : A₀.X ⨯ A₀.X ⟶ A₀.X) * Limits.prod.snd) = Fj.map m := by
    have h1 : c ≫ ((Limits.prod.fst : A₀.X ⨯ A₀.X ⟶ A₀.X) * Limits.prod.snd) =
        (c ≫ Limits.prod.fst) * (c ≫ Limits.prod.snd) := MonObj.comp_mul ..
    refine h1.trans ((congrArg₂ (· * ·) hc1 hc2).trans ?_)
    exact (Functor.map_mul Fj p1 p2).symm
  obtain ⟨e'⟩ := nonempty_tensor_iso_of_comp_eq c.left _ _ _ (g m) (g p1) (g p2)
    (congrArg CommaMorphism.left hcm) (congrArg CommaMorphism.left hc1)
    (congrArg CommaMorphism.left hc2) L.obj e
  have hclass : Group.pullback (g m) y = Group.pullback (g p1) y + Group.pullback (g p2) y :=
    pullback_classOf_eq_add (g m) (g p1) (g p2) L e'
  -- Injectivity forces the obstruction to vanish.
  have hzero : (pull m - pull p1 - pull p2)
      (ρ (SquareZeroPicardObstruction.obstructionMap i hi y)) = 0 := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hpull, hpull, hpull, ← map_sub, ← map_sub,
      ← map_sub, ← map_sub, hclass, sub_sub, sub_self, map_zero, map_zero]
  have hobs : SquareZeroPicardObstruction.obstructionMap i hi y = 0 := by
    have := hinj' (hzero.trans (map_zero _).symm)
    exact (map_eq_zero_iff ρ ρ.injective).mp this
  obtain ⟨M, ⟨eM⟩⟩ := (SquareZeroPicardObstruction.lineBundle_lift_iff i hi L).mpr hobs
  exact ⟨M, ⟨ObjectProperty.isoMk _ eM⟩⟩

end Langlands.AbelianScheme
