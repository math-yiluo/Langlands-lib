import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEmbeddingBoundedEquations
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionPowerSectionBound
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneBaseChange
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistTensorPowers
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingProof

/-! # Recovering the ideal of a cubic embedding from labelled torsion points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open ProjectiveSpace RelativeProjectiveSpace

variable {K : Type u} [Field K] [IsAlgClosed K] {P : Prerequisites.{u}} {g d n m : ℕ}
  {a b : Datum P (Spec (CommRingCat.of K)) g d n}
  {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m}
  {χ : b.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m}

/-- The relative-to-polynomial comparison identifies the pulled-back twists of a cubic
embedding over a field. -/
def Datum.IsCubicEmbedding.polynomialTwistIso (hψ : a.IsCubicEmbedding ψ) :
    (Scheme.Modules.pullback (ψ ≫ (polynomialIsoSpec K m).inv)).obj
      (Langlands.AlgebraicGeometry.twistOne K m) ≅ a.cubicBundle.obj := by
  let e := polynomialIsoSpec K m
  let i := ψ ≫ e.inv
  let M := (RelativeProjectiveSpace.twistOne (Spec (CommRingCat.of K)) m).obj
  exact (Scheme.Modules.pullback i).mapIso (polynomialIsoSpec_twistOneIso K m).symm ≪≫
    (Scheme.Modules.pullbackComp i e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr (show i ≫ e.hom = ψ by simp [i])).app M ≪≫ hψ.cubic.some

/-- Under the level-square inequality for a degree, a homogeneous form vanishes in the
kernel of a supplied cubic embedding exactly when every labelled torsion image lies in its
homogeneous zero locus. -/
theorem Datum.IsCubicEmbedding.homogeneousVanishes_iff_torsion (hψ : a.IsCubicEmbedding ψ)
    (hg : 0 < g) (hd : 0 < d) (hn : (n : K) ≠ 0) {t : ℕ}
    {F : ProjectiveCoordinateRing K m} (hF : F.IsHomogeneous t)
    (hsize : 6 ^ g * d * Nat.factorial g * t < n ^ 2) :
    let i := ψ ≫ (polynomialIsoSpec K m).inv
    HomogeneousVanishes i.ker hF ↔ ∀ r,
      F ∈ (i (a.torsionPoint r (IsLocalRing.closedPoint K))).asHomogeneousIdeal := by
  let e := polynomialIsoSpec K m
  let i := ψ ≫ e.inv
  change HomogeneousVanishes i.ker hF ↔ _
  have := hψ.isClosedImmersion
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  have hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom := by
    have he : e.hom ≫ RelativeProjectiveSpace.toBase (Spec (CommRingCat.of K)) m =
        projectiveSpaceToSpec K m :=
      polynomialIsoSpec_hom_toBase K m
    rw [← he]
    simpa only [i, Category.assoc, Iso.inv_hom_id_assoc] using hψ.toBase
  let M := Langlands.AlgebraicGeometry.twistOne K m
  let L := twistLineBundle K m t
  let E : (Scheme.Modules.pullback i).obj L.obj ≅ tensorPow a.cubicBundle.obj t :=
    (Scheme.Modules.pullback i).mapIso (twistTensorPowIso K m t).symm ≪≫
      pullbackTensorPowIso i M t ≪≫ tensorPowIso hψ.polynomialTwistIso t
  let s : a.cubicBundle.powSections t := isoPullbackSection i L E (homogeneousSection hF)
  have hopen : a.cubicBundle.sectionOpen s = i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K m) F := by
    exact (trivializationOpen_isoPullbackSection i L E _).trans
      (congrArg (fun U => i ⁻¹ᵁ U) (trivializationOpen_homogeneousSection hF))
  have hz : HomogeneousVanishes i.ker hF ↔ s = 0 := by
    rw [homogeneousVanishes_ker_iff_pullbackSection_eq_zero]
    change _ ↔ E.hom.app ⊤ (pullbackSection i L.obj (homogeneousSection hF)) = 0
    have : IsIso (E.hom.app ⊤) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
    rw [← (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).injective.eq_iff, map_zero]
  have hmem (r : Fin (2 * g) → ZMod n) :
      a.torsionPoint r (IsLocalRing.closedPoint K) ∉ a.cubicBundle.sectionOpen s ↔
        F ∈ (i (a.torsionPoint r (IsLocalRing.closedPoint K))).asHomogeneousIdeal := by
    rw [hopen, Scheme.Hom.mem_preimage, Proj.mem_basicOpen, not_not]
  constructor
  · intro h r
    apply (hmem r).mp
    rw [hz.mp h]
    change a.torsionPoint r (IsLocalRing.closedPoint K) ∉
      trivializationOpen (tensorPow a.cubicBundle.obj t) 0
    rw [trivializationOpen_zero (⟨tensorPow a.cubicBundle.obj t,
      tensorPow_isLocallyFreeRankOne _ a.cubicBundle t⟩ : LineBundle _)]
    exact fun h => h
  · intro h
    apply hz.mpr
    have : IsIntegral a.abelian.X.left := field_isIntegral a.abelian
    let Q : LineBundle a.abelian.X.left := ⟨tensorPow a.cubicBundle.obj t,
      tensorPow_isLocallyFreeRankOne _ a.cubicBundle t⟩
    exact Q.eq_zero_of_trivializationOpen_eq_bot s
      (a.sectionOpen_eq_bot_of_forall_torsion_notMem hg hd hn i hi hψ.polynomialTwistIso s
        hsize (fun r => (hmem r).mpr (h r)))

/-- For every given `g,d,m`, sufficiently large labelled torsion configurations determine
the actual embedded ideal, uniformly across fields, levels and cubic embeddings. -/
theorem exists_cubicEmbedding_ker_eq_of_torsion (g d m : ℕ) (hg : 0 < g) (hd : 0 < d) :
    ∃ N : ℕ, ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K]
      (n : ℕ), N ≤ n → (n : K) ≠ 0 →
      ∀ (a b : Datum P (Spec (CommRingCat.of K)) g d n)
        (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m)
        (χ : b.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m),
        a.IsCubicEmbedding ψ → b.IsCubicEmbedding χ →
        (∀ r, a.torsionPoint r ≫ ψ = b.torsionPoint r ≫ χ) → ψ.ker = χ.ker := by
  obtain ⟨D, hD⟩ := exists_boundedEquations_cubicEmbedding.{u} g d m
  let C := 6 ^ g * d * Nat.factorial g
  refine ⟨C * D + 1, fun P K _ _ n hN hn a b ψ χ hψ hχ hpoints => ?_⟩
  let e := polynomialIsoSpec K m
  let i := ψ ≫ e.inv
  let j := χ ≫ e.inv
  have hi := hD P n K a ψ hψ
  have hj := hD P n K b χ hχ
  have hker : i.ker = j.ker := by
    apply HasBoundedHomogeneousEquations.eq_of_vanishing_iff hi hj
    intro t F hF ht
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
    have hsize : C * t < n ^ 2 :=
      (lt_of_le_of_lt (Nat.mul_le_mul_left C ht) (show C * D < n from hN)).trans_le
        (le_self_pow hn0 two_ne_zero)
    have hI := hψ.homogeneousVanishes_iff_torsion hg hd hn hF hsize
    have hJ := hχ.homogeneousVanishes_iff_torsion hg hd hn hF hsize
    dsimp only at hI hJ
    rw [hI, hJ]
    have hx (r : Fin (2 * g) → ZMod n) :
        i (a.torsionPoint r (IsLocalRing.closedPoint K)) =
          j (b.torsionPoint r (IsLocalRing.closedPoint K)) := by
      change e.inv (ψ (a.torsionPoint r (IsLocalRing.closedPoint K))) =
        e.inv (χ (b.torsionPoint r (IsLocalRing.closedPoint K)))
      exact congrArg e.inv (congrArg (fun f => f (IsLocalRing.closedPoint K)) (hpoints r))
    change (∀ r, F ∈ (i (a.torsionPoint r (IsLocalRing.closedPoint K))).asHomogeneousIdeal) ↔
      ∀ r, F ∈ (j (b.torsionPoint r (IsLocalRing.closedPoint K))).asHomogeneousIdeal
    exact ⟨fun h r => hx r ▸ h r, fun h r => (hx r).symm ▸ h r⟩
  have := hψ.isClosedImmersion
  have := hχ.isClosedImmersion
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  let f := IsClosedImmersion.lift j i hker.ge
  have hf : f ≫ j = i := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ hker.symm
  have hc : f ≫ χ = ψ := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, ← show j = χ ≫ e.inv from rfl] using hf
  rw [← hc, Scheme.Hom.ker_comp_of_isIso]

end Langlands.AbelianScheme.PolarizedFiniteLevel
