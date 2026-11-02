import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionHyperplaneSections
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionPointFibre
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearPullbackBaseLocus
import Langlands.AlgebraicGeometry.Picard.LinearSystemBaseLocusBezoutProof
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomialSquare
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleSymmetry
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackStatement

/-! # Reduction of the torsion-hyperplane count to the Bezout count -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
  Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections GroupScheme.Tate

variable {K : Type u} [Field K]

variable {P : Prerequisites.{u}} {g d n : ℕ} (a : Datum P (Spec (CommRingCat.of K)) g d n)
  {m : ℕ} (i : a.abelian.X.left ⟶ ProjectiveSpace K m)
  (eM : (Scheme.Modules.pullback i).obj (twistOne K m) ≅ a.cubicBundle.obj)

/-- The section of the cubic bundle `M = M^1` obtained by pulling back the linear section
`f / 1` of `𝒪(1)` along `i`, using `eM : i^*𝒪(1) ≅ M`. -/
def torsionHyperplaneSection (f : projectiveSpaceGrading K m 1) : a.cubicBundle.powSections 1 :=
  isoPullbackSection i (twistOneLineBundle K m)
    (eM ≪≫ (tensorPowOneIso a.cubicBundle.obj).symm) (twistOneLinearSection K m f)

/-- A point lies in the generation open of `torsionHyperplaneSection a i eM f` exactly when
its image under `i` is off the hyperplane `f = 0`. -/
theorem mem_sectionOpen_torsionHyperplaneSection_iff (f : projectiveSpaceGrading K m 1)
    (x : a.abelian.X.left) :
    x ∈ a.cubicBundle.sectionOpen (torsionHyperplaneSection a i eM f) ↔
      (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal :=
  mem_trivializationOpen_isoPullbackSection_twistOne_iff i _ f x

/-- The linear system of GIT Prop. 7.7: the sections of `M^(n*n)` obtained by pulling back,
along `i` and then along `[n]`, the linear forms through the image of the origin. The
isomorphism `eB : [n]^*M ≅ M^(n*n)` identifies the pullbacks with sections of `M^(n*n)`. -/
def torsionBezoutSystem
    (eB : (Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ)).hom.hom.left).obj
          a.cubicBundle.obj ≅ tensorPow a.cubicBundle.obj (n * n)) :
    Set (a.cubicBundle.powSections (n * n)) :=
  linearPullbackSystem i a.cubicBundle eM
    (GroupScheme.multiplication a.abelian.toGrp (n : ℤ)).hom.hom.left eB
    (η[a.abelian.X].left (IsLocalRing.closedPoint K))

/-- For a closed immersion `i` over `K`, the base locus of `torsionBezoutSystem` is the
fibre of `[n]` over the origin. -/
theorem baseLocus_torsionBezoutSystem [IsClosedImmersion i]
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (eB : (Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ)).hom.hom.left).obj
          a.cubicBundle.obj ≅ tensorPow a.cubicBundle.obj (n * n)) :
    {x : a.abelian.X.left | ∀ t ∈ torsionBezoutSystem a i eM eB,
        x ∉ a.cubicBundle.sectionOpen t} = TorsionPointFibre a.abelian n := by
  have hσ : η[a.abelian.X].left ≫ i ≫ projectiveSpaceToSpec K m = 𝟙 _ := by
    rw [hi]
    exact Over.w η[a.abelian.X]
  exact baseLocus_linearPullbackSystem i i.isClosedEmbedding.injective η[a.abelian.X].left hσ
    a.cubicBundle eM _ eB

include eM in
/-- **Reduction to the Bezout count.** Let `a` be a datum over an algebraically closed
field `K` with `n ≠ 0` in `K`, let `i` be a closed embedding into `ℙᵐ_K` over `K` with
`i^*𝒪(1) ≅ M` for the cubic bundle `M`, and let `f` be a linear form not vanishing on
all of `i(A)`. Suppose that `[n]^*M ≅ M^(n*n)` and that the degree-`g` coefficient of
the Euler polynomial of `M` is `6^g*d`. Then the Bezout count bounds the number of
`n`-torsion `K`-points on the hyperplane `f = 0` by `6^g*d*g!*n^(2g-2)`. -/
theorem card_torsionHyperplaneSections_le_of_bezout [IsAlgClosed K]
    (hC : LinearSystemBaseLocusBezoutStatement.{u}) (hg : 0 < g) (hn : (n : K) ≠ 0)
    [IsClosedImmersion i] (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (eB : (Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ)).hom.hom.left).obj
          a.cubicBundle.obj ≅ tensorPow a.cubicBundle.obj (n * n))
    (hcoeff : (lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g =
      6 ^ g * d)
    (f : projectiveSpaceGrading K m 1)
    (hf : ∃ x : a.abelian.X.left,
      (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal) :
    Nat.card (TorsionHyperplaneSections i f n) ≤
      6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) := by
  have : IsIntegral a.abelian.X.left := field_isIntegral a.abelian
  have : IsNoetherian a.abelian.X.left := field_isNoetherian a.abelian
  have : a.abelian.X.left.IsSeparated := field_isSeparated a.abelian
  let s := torsionHyperplaneSection a i eM f
  let S := torsionBezoutSystem a i eM eB
  have hs := mem_sectionOpen_torsionHyperplaneSection_iff a i eM f
  have hBs := baseLocus_torsionBezoutSystem a i eM hi eB
  have hfin := torsionPointFibre_finite a.abelian n hn
  have hdim := field_topologicalKrullDim a.dimension
  have hbound := hC K a.abelian.X.left a.abelian.X.hom g hg hdim.le a.cubicBundle 1 (n * n)
    s S (by obtain ⟨x, hx⟩ := hf; exact ⟨x, (hs x).mpr hx⟩) (hBs ▸ hfin)
    (fun x hx _ => field_closedPoint_stalk_dimension a.dimension x
      (torsionPointFibre_isClosed_singleton a.abelian n hn (hBs ▸ hx)))
  rw [hcoeff] at hbound
  have : Finite {x : a.abelian.X.left //
      (∀ t ∈ S, x ∉ a.cubicBundle.sectionOpen t) ∧ x ∉ a.cubicBundle.sectionOpen s} :=
    ((hBs ▸ hfin : Set.Finite {x : a.abelian.X.left |
      ∀ t ∈ S, x ∉ a.cubicBundle.sectionOpen t}).subset fun x hx => hx.1).to_subtype
  let φ : TorsionHyperplaneSections i f n → {x : a.abelian.X.left //
      (∀ t ∈ S, x ∉ a.cubicBundle.sectionOpen t) ∧ x ∉ a.cubicBundle.sectionOpen s} :=
    fun x => ⟨(levelToTorsionPointFibre a.abelian n x.val).val,
      ⟨(Set.ext_iff.mp hBs _).mpr (levelToTorsionPointFibre a.abelian n x.val).property,
        (not_congr (hs _)).mpr (not_not.mpr x.property)⟩⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hv : (φ x).val = (φ y).val := congrArg Subtype.val hxy
    exact Subtype.ext (levelToTorsionPointFibre_injective a.abelian n (Subtype.ext hv))
  have hcard := Nat.card_le_card_of_injective φ hφ
  have hpow : ((n : ℚ) * n) ^ (g - 1) = (n : ℚ) ^ (2 * g - 2) := by
    rw [← sq, ← pow_mul]
    congr 1
    omega
  have hq : (Nat.card (TorsionHyperplaneSections i f n) : ℚ) ≤
      ((6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) : ℕ) : ℚ) := by
    calc (Nat.card (TorsionHyperplaneSections i f n) : ℚ)
        ≤ (Nat.card {x : a.abelian.X.left //
            (∀ t ∈ S, x ∉ a.cubicBundle.sectionOpen t) ∧
              x ∉ a.cubicBundle.sectionOpen s} : ℚ) := by exact_mod_cast hcard
      _ ≤ _ := hbound
      _ = _ := by
        push_cast
        rw [hpow]
        ring
  exact_mod_cast hq

include eM in
/-- The reduction `card_torsionHyperplaneSections_le_of_bezout` with the Euler-coefficient
hypothesis replaced by squared Euler characteristics: `χ(M^k)^2 = (6^g*d)^2 k^(2g)` for
every positive `k`, and `χ(M) ≥ 0`. -/
theorem card_torsionHyperplaneSections_le_of_bezout_of_eulerCharacteristic_sq [IsAlgClosed K]
    (hC : LinearSystemBaseLocusBezoutStatement.{u}) (hg : 0 < g) (hn : (n : K) ≠ 0)
    [IsClosedImmersion i] (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (eB : (Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ)).hom.hom.left).obj
          a.cubicBundle.obj ≅ tensorPow a.cubicBundle.obj (n * n))
    (hsq : ∀ k : ℕ, 0 < k →
      ∀ h : HasFiniteCohomology a.abelian.X.hom (tensorPow a.cubicBundle.obj k),
        eulerCharacteristic a.abelian.X.hom (tensorPow a.cubicBundle.obj k) h ^ 2 =
          ((6 ^ g * d : ℕ) : ℤ) ^ 2 * (k : ℤ) ^ (2 * g))
    (hpos : ∀ h : HasFiniteCohomology a.abelian.X.hom (tensorPow a.cubicBundle.obj 1),
      0 ≤ eulerCharacteristic a.abelian.X.hom (tensorPow a.cubicBundle.obj 1) h)
    (f : projectiveSpaceGrading K m 1)
    (hf : ∃ x : a.abelian.X.left,
      (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal) :
    Nat.card (TorsionHyperplaneSections i f n) ≤
      6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) := by
  have : IsNoetherian a.abelian.X.left := field_isNoetherian a.abelian
  have : a.abelian.X.left.IsSeparated := field_isSeparated a.abelian
  have hcoeff := lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq a.abelian.X.hom
    a.cubicBundle g (field_topologicalKrullDim a.dimension).le (6 ^ g * d) hsq hpos
  push_cast at hcoeff
  exact card_torsionHyperplaneSections_le_of_bezout a i eM hC hg hn hi eB hcoeff f hf

include eM in
/-- The reduction `card_torsionHyperplaneSections_le_of_bezout` with the isomorphism
`[n]^*M ≅ M^(n*n)` obtained from the symmetric multiplication-pullback statement, which
applies because the cubic bundle is symmetric
(`Datum.nonempty_pullback_neg_cubicBundle_iso`). -/
theorem card_torsionHyperplaneSections_le_of_bezout_of_symmetricPullback [IsAlgClosed K]
    (hC : LinearSystemBaseLocusBezoutStatement.{u})
    (hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u})
    (hg : 0 < g) (hn : (n : K) ≠ 0)
    [IsClosedImmersion i] (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (hcoeff : (lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g =
      6 ^ g * d)
    (f : projectiveSpaceGrading K m 1)
    (hf : ∃ x : a.abelian.X.left,
      (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal) :
    Nat.card (TorsionHyperplaneSections i f n) ≤
      6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨eB⟩ := hB K a.abelian.toGrp inferInstance inferInstance inferInstance a.cubicBundle
    a.nonempty_pullback_neg_cubicBundle_iso n hn0
  exact card_torsionHyperplaneSections_le_of_bezout a i eM hC hg hn hi eB hcoeff f hf

/-- **Conditional form of the target.** The torsion-hyperplane bound follows from the
Bezout count, the symmetric multiplication-pullback statement, and the coefficient formula
`(lineBundleEulerPolynomial M).coeff g = 6^g*d` for the cubic bundle `M` of every datum
with `0 < g` and `0 < d` over an algebraically closed field. -/
theorem cubicTorsionHyperplaneBound_of_bezout
    (hC : LinearSystemBaseLocusBezoutStatement.{u})
    (hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u})
    (hA : ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K] (g d n : ℕ),
      0 < g → 0 < d → ∀ a : Datum P (Spec (CommRingCat.of K)) g d n,
      (lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g = 6 ^ g * d) :
    CubicTorsionHyperplaneBoundStatement.{u} := by
  intro P K _ _ g d n hg hd _ hn a m i hi hcomp ⟨eM⟩ hnd f hf
  exact card_torsionHyperplaneSections_le_of_bezout_of_symmetricPullback a i eM hC hB hg hn
    hcomp (hA P K g d n hg hd a) f (hnd f hf)

/-- `cubicTorsionHyperplaneBound_of_bezout` with the Bezout statement discharged by the
published proof `linearSystemBaseLocusBezout`: the target follows from the symmetric
multiplication-pullback statement and the coefficient formula alone. -/
theorem cubicTorsionHyperplaneBound_of_symmetricPullback
    (hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u})
    (hA : ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K] (g d n : ℕ),
      0 < g → 0 < d → ∀ a : Datum P (Spec (CommRingCat.of K)) g d n,
      (lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g = 6 ^ g * d) :
    CubicTorsionHyperplaneBoundStatement.{u} :=
  cubicTorsionHyperplaneBound_of_bezout linearSystemBaseLocusBezout hB hA

end Langlands.AbelianScheme.PolarizedFiniteLevel
