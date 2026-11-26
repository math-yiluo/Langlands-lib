import Langlands.AbelianScheme.IsogenyFinrankKernelCardProof
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof

/-! # The degree of a doubled polarization on a connected base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A : AbelianScheme S}
  (W : DualWitness A) (lam : A ⟶ W.dual P)

private theorem doubled_isIsogeny_of (h : IsIsogeny lam) : IsIsogeny (2 • lam) := by
  have h2 : IsIsogeny ((2 : ℕ) • 𝟙 A) := by
    change GroupScheme.IsIsogeny (groupHom ((2 : ℕ) • 𝟙 A))
    rw [Tate.groupHom_nsmul_id]
    exact GroupScheme.multiplicationIsogeny S A.toGrp A.smooth A.proper
      A.geometricallyConnected (2 : ℤ) (by decide)
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using h2.comp h

/-- Over a connected locally noetherian base with an algebraically closed
characteristic-zero point, the double of a polarization has degree `d²`
for a positive integer `d`. -/
theorem DualWitness.exists_pos_hasDegreeSquare_double
    [IsLocallyNoetherian S] [ConnectedSpace S]
    (hpol : W.IsPolarization P lam)
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S) :
    ∃ d : ℕ, 0 < d ∧ HasDegreeSquare (2 • lam) d := by
  let A' := (baseChange s).obj A
  let V := W.pullback P s
  let f := W.pullbackMap P s V lam
  let E := W.baseChangeIso P s V
  let g := (baseChange s).map (2 • lam)
  have hpol' : V.IsPolarization P f :=
    P.polarizationBaseChange P.preservation P.square P.universality P.stability P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.compatibility S _ s A
      W.hasDual W.geometry W.inverseBundle W.evaluation
      V.hasDual V.geometry V.inverseBundle V.evaluation lam hpol
  let L := poincareDiagonalBundle A' V.hasDual (V.parameterMap P f)
  have hL : L.IsAmple := by
    apply poincareDiagonal_isAmple_of_fieldPresentation P K A' V
    rw [DualWitness.parameterMap_pullbackMap]
    exact hpol.2 K s
  obtain ⟨B, evB, M, evM, he⟩ := polarizationDiagonalMumford P.preservation
    P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability _ A' V.hasDual V.geometry
    V.inverseBundle V.evaluation f hpol'
  have hfinite : HasFiniteCohomology A'.X.hom L.obj :=
    smoothProperLineBundleFiniteCohomology K A'.X.left A'.X.hom
      inferInstance inferInstance L
  have hf : IsIsogeny (2 • f) := doubled_isIsogeny_of P V f hpol'.1
  let d := (eulerCharacteristic A'.X.hom L.obj hfinite).natAbs
  have hd : HasDegreeSquare (2 • f) d := by
    intro y
    have hsquare := algClosedFieldAmpleMumfordEulerSquare P.preservation P.square K
      A' V.hasDual L hL hfinite B evB M evM (groupHom (2 • f)).hom.hom he.symm
      hf.1 hf.2.1 y
    simpa only [d, Int.natAbs_pow, Int.natAbs_natCast] using
      (congrArg Int.natAbs hsquare).symm
  have hdpos : 0 < d := by
    let y := unitSection (V.dual P) (IsLocalRing.closedPoint K)
    have hpos : 0 < (hom (2 • f)).finrank y := by
      rw [isogenyFinrankKernelCard K A' (V.dual P) _ hf y]
      exact Nat.card_pos_iff.mpr ⟨⟨1⟩, hf.finite_ker_pointsHom (𝟙 _)⟩
    rw [hd y] at hpos
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    rw [hd0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hpos
    exact (lt_irrefl 0) hpos
  have hgf : 2 • f = g ≫ E.hom := by
    change 2 • ((baseChange s).map lam ≫ E.hom) =
      (baseChange s).map (2 • lam) ≫ E.hom
    rw [Functor.map_nsmul, Preadditive.nsmul_comp]
  have htotal : IsIsogeny (2 • lam) := doubled_isIsogeny_of P W lam hpol.1
  let : IsFinite (hom (2 • lam)) := htotal.1
  let : Flat (hom (2 • lam)) := htotal.2.1
  let : IsFinite (hom g) := (htotal.baseChange s).1
  let : Flat (hom g) := (htotal.baseChange s).2.1
  have hg : HasDegreeSquare g d := by
    rw [hgf] at hd
    change HasConstantDegree (hom g ≫ (underlyingSchemeIso E).hom) (d ^ 2) at hd
    exact (hasConstantDegree_post_iso_iff (hom g) (underlyingSchemeIso E) (d ^ 2)).mp hd
  let y₀ := unitSection ((baseChange s).obj (W.dual P)) (IsLocalRing.closedPoint K)
  let y := pullback.fst (W.dual P).X.hom s y₀
  have hy : (hom (2 • lam)).finrank y = d ^ 2 :=
    (Scheme.Hom.finrank_of_isPullback _ _ _ _ (hom_baseChange_isPullback s (2 • lam)) y₀).symm.trans
      (hg y₀)
  have : ConnectedSpace (W.dual P).X.left :=
    GeometricallyConnected.connectedSpace (W.dual P).X.hom (W.dual P).X.hom.isOpenMap
  refine ⟨d, hdpos, fun z => ?_⟩
  exact ((isLocallyConstant_finrank_of_isIsogeny (2 • lam) htotal).apply_eq_of_preconnectedSpace
    z y).trans hy

/-- The positive degree index of twice the polarization, computed on the
given geometric fibre. -/
def DualWitness.doubledDegreeIndex [IsLocallyNoetherian S] [ConnectedSpace S]
    (hpol : W.IsPolarization P lam)
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S) : ℕ :=
  Classical.choose (W.exists_pos_hasDegreeSquare_double P lam hpol s)

theorem DualWitness.doubledDegreeIndex_spec [IsLocallyNoetherian S] [ConnectedSpace S]
    (hpol : W.IsPolarization P lam)
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S) :
    0 < W.doubledDegreeIndex P lam hpol s ∧
      HasDegreeSquare (2 • lam) (W.doubledDegreeIndex P lam hpol s) :=
  Classical.choose_spec (W.exists_pos_hasDegreeSquare_double P lam hpol s)

end Langlands.AbelianScheme.PolarizedFiniteLevel
