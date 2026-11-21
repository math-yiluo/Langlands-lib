import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusField

/-! # The torsion bound for sections of every power of the cubic bundle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.SchemeModule
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {P : Prerequisites.{u}} {g d n m : ℕ}

/-- The coefficient tuples whose actual torsion points are outside the generation open
of a section of a power of the cubic bundle. -/
def Datum.TorsionZeros (a : Datum P (Spec (CommRingCat.of K)) g d n) {t : ℕ}
    (s : a.cubicBundle.powSections t) :=
  {r : Fin (2 * g) → ZMod n //
    a.torsionPoint r (IsLocalRing.closedPoint K) ∉ a.cubicBundle.sectionOpen s}

/-- A non-identically vanishing section of the `t`-th power of the cubic bundle has at most
`6^g * d * g! * t * n^(2g-2)` labelled torsion zeros. The supplied cubic embedding is used
only to get a system of sections of `M^(n*n)` whose base locus is the multiplication fibre. -/
theorem Datum.card_torsionZeros_le (a : Datum P (Spec (CommRingCat.of K)) g d n)
    (hg : 0 < g) (hd : 0 < d) (hn : (n : K) ≠ 0)
    (i : a.abelian.X.left ⟶ ProjectiveSpace K m) [IsClosedImmersion i]
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (eM : (Scheme.Modules.pullback i).obj (twistOne K m) ≅ a.cubicBundle.obj)
    {t : ℕ} (s : a.cubicBundle.powSections t)
    (hs : (a.cubicBundle.sectionOpen s : Set a.abelian.X.left).Nonempty) :
    Nat.card (a.TorsionZeros s) ≤ 6 ^ g * d * Nat.factorial g * t * n ^ (2 * g - 2) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  have : IsIntegral a.abelian.X.left := field_isIntegral a.abelian
  have : IsNoetherian a.abelian.X.left := field_isNoetherian a.abelian
  have : a.abelian.X.left.IsSeparated := field_isSeparated a.abelian
  obtain ⟨eB⟩ := Langlands.GroupScheme.fieldSymmetricMultiplicationPullback K
    a.abelian.toGrp inferInstance inferInstance inferInstance a.cubicBundle
    a.nonempty_pullback_neg_cubicBundle_iso n hn0
  let S := torsionBezoutSystem a i eM eB
  have hBs := baseLocus_torsionBezoutSystem a i eM hi eB
  have hfin := torsionPointFibre_finite a.abelian n hn
  have hdim := field_topologicalKrullDim a.dimension
  have hbound := linearSystemBaseLocusBezout K a.abelian.X.left a.abelian.X.hom g hg
    hdim.le a.cubicBundle t (n * n) s S hs (hBs ▸ hfin)
    (fun x hx _ => field_closedPoint_stalk_dimension a.dimension x
      (torsionPointFibre_isClosed_singleton a.abelian n hn (hBs ▸ hx)))
  rw [a.cubicBundle_eulerPolynomial_coeff_of_fibreInputs algClosedFieldAmpleEulerInverseScaling
    algClosedFieldEulerInverseSymmetry cubicFibreCohomology hd] at hbound
  let Z := {x : a.abelian.X.left //
    (∀ q ∈ S, x ∉ a.cubicBundle.sectionOpen q) ∧ x ∉ a.cubicBundle.sectionOpen s}
  have : Finite Z := ((hBs ▸ hfin : Set.Finite {x : a.abelian.X.left |
    ∀ q ∈ S, x ∉ a.cubicBundle.sectionOpen q}).subset fun x hx => hx.1).to_subtype
  let v (r : Fin (2 * g) → ZMod n) :=
    levelToTorsionPointFibre a.abelian n (a.level.fibreCoordinates K (𝟙 _) r)
  have hv : Function.Injective v := (levelToTorsionPointFibre_injective a.abelian n).comp
    (a.level.fibreCoordinates K (𝟙 _)).injective
  have hv' (r : Fin (2 * g) → ZMod n) :
      (v r).val = a.torsionPoint r (IsLocalRing.closedPoint K) := by
    change (Additive.toMul (a.level.fibreCoordinates K (𝟙 _) r)).val.left
        (IsLocalRing.closedPoint K) = _
    exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ a.abelian.X.left =>
      f (IsLocalRing.closedPoint K)) (a.fibreCoordinates_left r)
  let φ : a.TorsionZeros s → Z := fun r =>
    ⟨(v r.val).val, ⟨(Set.ext_iff.mp hBs _).mpr (v r.val).property, hv' _ ▸ r.property⟩⟩
  have hφ : Function.Injective φ := by
    intro r r' h
    have hvv : (v r.val).val = (v r'.val).val := congrArg (fun z : Z => z.val) h
    exact Subtype.ext (hv (Subtype.ext hvv))
  have hcard := Nat.card_le_card_of_injective φ hφ
  have hpow : ((n : ℚ) * n) ^ (g - 1) = (n : ℚ) ^ (2 * g - 2) := by
    rw [← sq, ← pow_mul]
    congr 1
    omega
  have hq : (Nat.card (a.TorsionZeros s) : ℚ) ≤
      ((6 ^ g * d * Nat.factorial g * t * n ^ (2 * g - 2) : ℕ) : ℚ) := by
    calc
      (Nat.card (a.TorsionZeros s) : ℚ) ≤ Nat.card Z := by exact_mod_cast hcard
      _ ≤ _ := hbound
      _ = _ := by push_cast; rw [hpow]; ring
  exact_mod_cast hq

/-- If the square of the level exceeds the bound constant for degree `t`, the labelled
torsion points detect emptiness of the whole generation open. -/
theorem Datum.sectionOpen_eq_bot_of_forall_torsion_notMem
    (a : Datum P (Spec (CommRingCat.of K)) g d n)
    (hg : 0 < g) (hd : 0 < d) (hn : (n : K) ≠ 0)
    (i : a.abelian.X.left ⟶ ProjectiveSpace K m) [IsClosedImmersion i]
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (eM : (Scheme.Modules.pullback i).obj (twistOne K m) ≅ a.cubicBundle.obj)
    {t : ℕ} (s : a.cubicBundle.powSections t)
    (hsize : 6 ^ g * d * Nat.factorial g * t < n ^ 2)
    (h : ∀ r, a.torsionPoint r (IsLocalRing.closedPoint K) ∉ a.cubicBundle.sectionOpen s) :
    a.cubicBundle.sectionOpen s = ⊥ := by
  by_contra hne
  have hne' : (a.cubicBundle.sectionOpen s : Set a.abelian.X.left).Nonempty := by
    rw [← Opens.not_nonempty_iff_eq_bot] at hne
    exact not_not.mp hne
  have hbound := a.card_torsionZeros_le hg hd hn i hi eM s hne'
  let e : (Fin (2 * g) → ZMod n) ≃ a.TorsionZeros s :=
    ⟨fun r => ⟨r, h r⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  have hcard : Nat.card (a.TorsionZeros s) = n ^ (2 * g) := by
    rw [← Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [hcard] at hbound
  have he : n ^ 2 * n ^ (2 * g - 2) = n ^ (2 * g) := by
    rw [← pow_add]; congr 1; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  exact (not_lt_of_ge hbound) ((Nat.mul_lt_mul_of_pos_right hsize (pow_pos hn0 _)).trans_eq he)

end Langlands.AbelianScheme.PolarizedFiniteLevel
