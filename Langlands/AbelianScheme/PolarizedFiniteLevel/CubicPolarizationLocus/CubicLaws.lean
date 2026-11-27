import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.MumfordLaws
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocusStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizedBundleTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.QuasiSeparatedDualWitness

/-! # Cubic diagonal line bundles under dual comparison -/

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} {A B : AbelianScheme S}
variable (W : DualWitness A) (lam : A ⟶ W.dual P)

/-- The cubic power of the diagonal Poincaré pullback of an actual homomorphism. -/
def cubicDiagonalBundle : LineBundle A.X.left :=
  let D := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
  ⟨tensorPow D.obj 3, tensorPow_isLocallyFreeRankOne _ D 3⟩

/-- The relative cubic formula holds for a polarization without a choice of level. -/
lemma lineBundleMumford_cubicDiagonal [IsLocallyNoetherian S] (h : W.IsPolarization P lam) :
    lineBundleMumford P A W (cubicDiagonalBundle P W lam) = 6 • lam := by
  let D := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
  obtain ⟨U, evU, M, evM, hmap⟩ := polarizationDiagonalMumford P.preservation P.square
    P.universality P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability S A W.hasDual W.geometry W.inverseBundle W.evaluation lam h
  have hD : lineBundleMumford P A W D = 2 • lam := by
    apply Grp.hom_ext
    exact (lineBundleMumford_parameterMap_eq P A W D U evU M evM).trans hmap
  change lineBundleMumford P A W ⟨tensorPow D.obj 3, tensorPow_isLocallyFreeRankOne _ D 3⟩ = _
  rw [lineBundleMumford_tensorPow, hD, smul_smul]
  rfl

/-- The cube for the canonically changed map is the actual pullback of the cube. -/
def cubicDiagonalBundlePullbackIso (b : T ⟶ S) (W' : DualWitness ((baseChange b).obj A)) :
    cubicDiagonalBundle P W' (W.pullbackMap P b W' lam) ≅
      (LineBundle.pullback (pullback.fst A.X.hom b)).obj (cubicDiagonalBundle P W lam) := by
  let D := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
  have e : poincareDiagonalBundle ((baseChange b).obj A) W'.hasDual
      (W'.parameterMap P (W.pullbackMap P b W' lam)) ≅
        (LineBundle.pullback (pullback.fst A.X.hom b)).obj D := by
    rw [DualWitness.parameterMap_pullbackMap]
    exact poincareDiagonalBaseChangeIso P.universality b A W.hasDual (W.parameterMap P lam)
  exact ObjectProperty.isoMk _
    (tensorPowIso ((LineBundle.forget _).mapIso e) 3 ≪≫
      (actualPullbackTensorPowIso (pullback.fst A.X.hom b) D.obj 3).symm)

/-- Comparing abelian schemes and their duals transports the cubic diagonal bundle. -/
def cubicDiagonalBundleTransportIso (e : B ≅ A) (V : DualWitness B) :
    (LineBundle.pullback (hom e.hom)).obj (cubicDiagonalBundle P W lam) ≅
      cubicDiagonalBundle P V (DualWitness.transportMap P e V W lam) := by
  let D := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
  let D' := poincareDiagonalBundle B V.hasDual
    (V.parameterMap P (DualWitness.transportMap P e V W lam))
  have h₀ : (LineBundle.pullback (hom e.hom)).obj D ≅ D' :=
    poincareDiagonalHomPullbackIso e.hom V.hasDual W.hasDual (W.parameterMap P lam)
  exact ObjectProperty.isoMk _ (actualPullbackTensorPowIso (hom e.hom) D.obj 3 ≪≫
    tensorPowIso ((LineBundle.forget _).mapIso h₀) 3)

/-- The cubic polarization condition is intrinsic under an isomorphism of abelian schemes. -/
lemma existsCubicPolarization_of_iso [QuasiSeparatedSpace S] (e : B ≅ A) (d : ℕ)
    {L : LineBundle A.X.left} {L' : LineBundle B.X.left}
    (hL : L' ≅ (LineBundle.pullback (hom e.hom)).obj L)
    (h : ExistsCubicPolarization P d A L) : ExistsCubicPolarization P d B L' := by
  obtain ⟨W, lam, hp, hd, N, ⟨eL⟩⟩ := h
  let V := DualWitness.ofQuasiSeparated B
  refine ⟨V, DualWitness.transportMap P e V W lam,
    DualWitness.isPolarization_transportMap P e V W lam hp,
    (hasDegreeSquare_iso_iff lam hp.1 e (V.mapIso P W e) d).mpr hd, N, ?_⟩
  have hπ : hom e.hom ≫ A.X.hom = B.X.hom := (groupHom e.hom).hom.hom.w
  exact ⟨hL ≪≫ (LineBundle.pullback (hom e.hom)).mapIso eL ≪≫
    LineBundle.pullbackTensorObjIso P.preservation _ _ _ ≪≫
    LineBundle.tensorIso P.preservation (cubicDiagonalBundleTransportIso P W lam e V)
      (LineBundle.pullbackCompEqIso (hom e.hom) A.X.hom hπ N)⟩

/-- The existential cubic condition can use any given witness for the dual. -/
lemma existsCubicPolarization_atWitness (V : DualWitness A) (d : ℕ) (L : LineBundle A.X.left)
    (h : ExistsCubicPolarization P d A L) :
    ∃ lam : A ⟶ V.dual P, V.IsPolarization P lam ∧ HasDegreeSquare lam d ∧
      ∃ N : LineBundle S, Nonempty (L ≅ LineBundle.tensor P.preservation
        (cubicDiagonalBundle P V lam) ((LineBundle.pullback A.X.hom).obj N)) := by
  obtain ⟨W, lam, hp, hd, N, ⟨eL⟩⟩ := h
  let e := CategoryTheory.Iso.refl A
  refine ⟨DualWitness.transportMap P e V W lam, DualWitness.isPolarization_transportMap P e V W lam hp,
    (hasDegreeSquare_iso_iff lam hp.1 e (V.mapIso P W e) d).mpr hd, N, ?_⟩
  have hC : cubicDiagonalBundle P W lam ≅ cubicDiagonalBundle P V
      (DualWitness.transportMap P e V W lam) :=
    ((LineBundle.pullbackId A.X.left).app _).symm ≪≫ cubicDiagonalBundleTransportIso P W lam e V
  exact ⟨eL ≪≫ LineBundle.tensorIso P.preservation hC (Iso.refl _)⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
