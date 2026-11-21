import Langlands.Geometry.FormalGroup.DrinfeldLubinTateFrobenius
import Langlands.Geometry.FormalGroup.DrinfeldLubinTateTeichmuller
import Langlands.Geometry.FormalGroup.DrinfeldScalarFrobeniusHeight
import Langlands.Geometry.FormalGroup.PointFactorization
import Langlands.GroupScheme.FiniteFieldTorsorPoint.PointDescent

/-! # Dividing commuting endomorphisms of the Lubin–Tate line by the uniformizer -/

noncomputable section

namespace Langlands.FormalGroup

universe u

namespace CommLaw.Hom

variable {R : Type u} [CommRing R] (G : CommLaw R Unit)

/-- The derivative of a one-coordinate endomorphism is a scalar. -/
def lineDerivative : CommLaw.Hom G G →+* R :=
  let eval : Module.End R (Unit → R) →+* R :=
    { toFun := fun f => f (1 : Unit → R) ()
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun f g => by
        change f (g (1 : Unit → R)) () = f 1 () * g 1 ()
        have h : g (1 : Unit → R) = g 1 () • (1 : Unit → R) := by
          funext i
          cases i
          simp
        calc
          _ = f (g 1 () • (1 : Unit → R)) () := congrArg (fun x => f x ()) h
          _ = _ := by rw [map_smul]; exact mul_comm _ _ }
  eval.comp (tangentEnd G)

@[simp]
theorem lineDerivative_apply (f : CommLaw.Hom G G) :
    lineDerivative G f = f.toCoordinateMap.linearCoeff () () := by
  change f.toCoordinateMap.linearPart (1 : Unit → R) () = _
  rw [CoordinateMap.linearPart_apply, Fintype.sum_unique, Pi.one_apply, mul_one]

end CommLaw.Hom

namespace LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing ModuleLaw CategoryTheory MvPowerSeries

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance lineCentralizerLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "C" => SubfieldIntegerRing K D ι
local notation "q" => Nat.card (ResidueField (SubfieldIntegerRing K D ι))

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) {π : 𝒪[K]} (hπ : Irreducible π)

local notation "H" => drinfeldLubinTateLine ι χ hL hπ
local notation "coeffAction" => drinfeldLubinTateCoefficients ι χ hL hπ
local notation "EndH" => ModuleLaw.Hom H H

/-- The embedded integers act by actual homomorphisms of the original scalar formal module. -/
def drinfeldLineCoefficientEnd : C →+* EndH where
  toFun a := ⟨coeffAction a, fun b => by
    change coeffAction a * coeffAction (algebraMap 𝒪[K] C b) = coeffAction (algebraMap 𝒪[K] C b) * coeffAction a
    rw [← map_mul (coeffAction), ← map_mul (coeffAction), mul_comm]⟩
  map_zero' := Hom.ext (map_zero coeffAction)
  map_one' := Hom.ext (map_one coeffAction)
  map_add' _ _ := Hom.ext (map_add coeffAction _ _)
  map_mul' _ _ := Hom.ext (map_mul coeffAction _ _)

local notation "fc" => drinfeldLineCoefficientEnd ι χ hL hπ

variable (p : ℕ) [ExpChar κ p] {e : ℕ} (hcard : Nat.card 𝓀[K] = p ^ e)
variable (σ : L ≃ₐ[K] L)
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "τ" => subfieldIntegerFrobenius ι σ hL
local notation "T" => drinfeldLubinTateFrobenius ι χ hL hπ p hcard σ hσ

include hcard hσ in
/-- Arithmetic Frobenius of the line is linear over the original scalar order. -/
def drinfeldLineFrobeniusEnd : EndH where
  toHom := T
  commutes a := by
    have h := drinfeldLubinTateFrobenius_mul ι χ hL hπ p hcard σ hσ (algebraMap 𝒪[K] C a)
    rw [(τ).commutes] at h
    exact h

local notation "tc" => drinfeldLineFrobeniusEnd ι χ hL hπ p hcard σ hσ
local notation "der" => CommLaw.Hom.lineDerivative (ModuleLaw.groupLaw H)

/-- Commutation with arithmetic Frobenius forces the derivative to come from the original residue field. -/
theorem drinfeldLine_derivative_exists_scalar (z : EndH) (hz : Commute z tc) :
    ∃ a : 𝒪[K], der z.toHom = algebraMap 𝒪[K] κ a := by
  let g := z.toHom.toCoordinateMap
  let P := CoordinateMap.frobeniusPow (R := κ) (σ := Unit) p e
  let φ := iterateFrobenius κ p e
  have hc := congrArg (fun w : EndH => w.toHom.toCoordinateMap) hz.eq
  change g.comp P = P.comp g at hc
  have he : (g.map φ).comp P = g.comp P :=
    (CoordinateMap.frobeniusPow_natural p e g).symm.trans hc.symm
  have hs := congrArg (fun w : CoordinateMap κ Unit Unit => w.series ()) he
  let a := p ^ e
  have ha : a ≠ 0 := pow_ne_zero e (expChar_ne_zero κ p)
  have hP : P.series = fun i => X i ^ a := rfl
  have hExpand : MvPowerSeries.expand a ha ((g.series ()).map φ) = MvPowerSeries.expand a ha (g.series ()) := by
    simpa only [MvPowerSeries.expand, substAlgHom_apply, CoordinateMap.comp_series,
      CoordinateMap.map_series, hP] using hs
  have hcoef := congrArg (coeff (a • Finsupp.single () 1)) hExpand
  rw [coeff_expand_smul, coeff_expand_smul, MvPowerSeries.coeff_map] at hcoef
  change (g.linearCoeff () ()) ^ (p ^ e) = g.linearCoeff () () at hcoef
  let : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]
  have hpow : (g.linearCoeff () ()) ^ Fintype.card 𝓀[K] = g.linearCoeff () () := by
    simpa only [← hcard, Nat.card_eq_fintype_card] using hcoef
  obtain ⟨b, hb⟩ := Langlands.GroupScheme.FiniteFieldTorsorPoint.mem_range_algebraMap_of_pow_card_eq
    (k := 𝓀[K]) hpow
  obtain ⟨c, hc⟩ := residue_surjective b
  refine ⟨c, ?_⟩
  rw [CommLaw.Hom.lineDerivative_apply]
  calc
    _ = algebraMap 𝓀[K] κ b := hb.symm
    _ = _ := by rw [← hc, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

variable [Algebra.IsAlgebraic 𝓀[K] κ]

include hcard in
private theorem drinfeldLine_uniformizer_surjective : ((H).scalarHom π).IsFppfLocallySurjective := by
  let θ := subfieldReductionCharacter ι χ
  have hz : θ (algebraMap 𝒪[K] C π) = 0 := by
    change χ (residue C (algebraMap 𝒪[K] C π)) = 0
    rw [LubinTateStandard.residue_uniformizer _ (subfieldMaximalIdeal_eq_uniformizer ι hL hπ), map_zero]
  have hπzero := (θ.commutes π).symm.trans hz
  exact (hasPiHeight_of_scalarFrobenius H hcard hπzero
    (drinfeldLubinTateLine_uniformizer_frobenius ι χ hL hπ p hcard) (reducedDegree_pos K D)).1.scalar_locallySurjective

omit [Algebra.IsAlgebraic 𝓀[K] κ] in
private theorem drinfeldLine_scalar_division_preserves_commute {z z' b : EndH}
    (hSurj : ((H).scalarHom π).IsFppfLocallySurjective) (he : z'.comp ((H).scalarHom π) = z)
    (hc : Commute z b) : Commute z' b := by
  apply hSurj.comp_right_cancel
  change (z' * b) * (H).scalarHom π = (b * z') * (H).scalarHom π
  have hb : b * (H).scalarHom π = (H).scalarHom π * b := Hom.comp_scalarHom b π
  have he' : z' * (H).scalarHom π = z := he
  rw [mul_assoc z' b, hb, ← mul_assoc z', he', mul_assoc b, he', hc.eq]

/-- A commuting endomorphism with zero derivative factors through the scalar
uniformizer. The factor still commutes with the embedded integers and Frobenius. -/
theorem drinfeldLine_divide_uniformizer (z : EndH)
    (hcoeff : ∀ b : C, Commute z (fc b)) (hFrob : Commute z tc) (hlin : der z.toHom = 0) :
    ∃ z' : EndH, (∀ b : C, Commute z' (fc b)) ∧ Commute z' tc ∧ z = π • z' := by
  have hSurj := drinfeldLine_uniformizer_surjective ι χ hL hπ p hcard
  have hzCoeff (b : C) : Commute z.toHom (coeffAction b) := congrArg Hom.toHom (hcoeff b).eq
  rw [CommLaw.Hom.lineDerivative_apply] at hlin
  obtain ⟨u, hu⟩ := line_uniformizer_degree_dvd ι hL χ hπ z.toHom hzCoeff hlin
  change z.toHom.toCoordinateMap.series () = (X () : MvPowerSeries Unit κ) ^ q * u at hu
  have hker (A : CommAlgCat.{u} κ) (x : (H).AlgebraPoint A)
      (hx : ((H).scalarHom π).onAlgebraPoints x = 0) : z.onAlgebraPoints x = 0 := by
    let y : SeriesPoint A Unit Empty := x
    have hp := congrArg (fun w : SeriesPoint A Unit Empty => w.val ()) hx
    change MvPowerSeries.subst y.val
      ((((H).scalarHom π).toHom.toCoordinateMap.map (algebraMap κ A)).series ()) = 0 at hp
    rw [CoordinateMap.map_series, drinfeldLubinTateLine_uniformizer_series ι χ hL hπ,
      map_pow, map_X, subst_pow y.property, subst_X y.property] at hp
    apply SeriesPoint.ext
    intro i
    cases i
    change MvPowerSeries.subst y.val ((z.toHom.toCoordinateMap.series ()).map (algebraMap κ A)) = 0
    rw [hu, map_mul, map_pow, map_X, subst_mul y.property, subst_pow y.property,
      subst_X y.property, hp, zero_mul]
  obtain ⟨z', he⟩ := Hom.exists_comp_eq (f := (H).scalarHom π) (h := z) hSurj hker
  refine ⟨z', fun b => drinfeldLine_scalar_division_preserves_commute ι χ hL hπ hSurj he (hcoeff b),
    drinfeldLine_scalar_division_preserves_commute ι χ hL hπ hSurj he hFrob, ?_⟩
  rw [← he, Hom.comp_scalarHom, scalarHom, Hom.smul_comp, Hom.id_comp]

/-- Subtract one scalar digit and divide by the uniformizer in the same centralizer. -/
theorem drinfeldLine_scalar_digit (z : EndH) (hcoeff : ∀ b : C, Commute z (fc b)) (hFrob : Commute z tc) :
    ∃ a : 𝒪[K], ∃ z' : EndH, (∀ b : C, Commute z' (fc b)) ∧ Commute z' tc ∧
      z = (H).scalarHom a + π • z' := by
  obtain ⟨a, ha⟩ := drinfeldLine_derivative_exists_scalar ι χ hL hπ p hcard σ hσ z hFrob
  have hScalar (w : EndH) : Commute ((H).scalarHom a) w := (Hom.comp_scalarHom w a).symm
  have hlin : der ((H).scalarHom a).toHom = algebraMap 𝒪[K] κ a := by
    rw [CommLaw.Hom.lineDerivative_apply, scalarHom, Hom.smul_toHom, Hom.id_toHom,
      CommLaw.Hom.comp_id, (H).linear_natural]
    simp [CoordinateMap.scalarLinearCoeff]
  obtain ⟨z', hcoeff', hfrob', he⟩ := drinfeldLine_divide_uniformizer ι χ hL hπ p hcard σ hσ
    (z - (H).scalarHom a) (fun b => (hcoeff b).sub_left (hScalar (fc b))) (hFrob.sub_left (hScalar tc))
    (by
      change der (z.toHom - ((H).scalarHom a).toHom) = 0
      rw [map_sub, ha, hlin, sub_self])
  exact ⟨a, z', hcoeff', hfrob', (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)⟩

end LocalDivision
end Langlands.FormalGroup
