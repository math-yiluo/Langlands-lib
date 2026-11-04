import Langlands.Representation.Aubert.General.RationalLeviCentralCharacterNorms
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Rational.StandardLeviAnnihilatorTransport

/-! # Rank-one logarithmic moduli on the actual Levi center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Evaluation at the common uniformizer maps the selected-root annihilator
into the actual Levi-central torus-point subgroup. -/
def leviCentralUniformizerSection
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    Multiplicative (cocharacterAnnihilator T (rootSet i ν I)) →*
      leviCentralTorusPoints i ν I :=
  ((CocharacterUniformizer.latticeSection k T).comp
    (cocharacterAnnihilator T (rootSet i ν I)).subtype.toAddMonoidHom.toMultiplicative
      ).codRestrict (leviCentralTorusPoints i ν I) (by
        intro x
        rw [leviCentralTorusPoints_eq_comap_centralizer]
        intro m hm
        exact commute_uniformizerPowers i ν hfinite I hexists
          (x.toAdd : cocharacterLattice T)
          (fun β hβ => (mem_cocharacterAnnihilator.mp x.toAdd.property) β.1
            ((val_mem_rootSet i ν I β).mpr hβ)) m hm)

@[simp] theorem leviCentralUniformizerSection_val
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (x : Multiplicative (cocharacterAnnihilator T (rootSet i ν I))) :
    (leviCentralUniformizerSection i ν hfinite I hexists x :
      rationalPoints T.toGrp) =
        CocharacterUniformizer.latticeSection k T
          (.ofAdd (x.toAdd : cocharacterLattice T)) := rfl

/-- The residue-normalized logarithm of the modulus of a full-center character,
restricted to the actual central torus points. -/
def leviCentralTorusCharacterLog
    (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ) :
    leviCentralTorusPoints i ν I →* Multiplicative ℝ where
  toFun t := .ofAdd (Plancherel.normLog (LocalField.residueCardinality k)
    (PositiveCharacter.normCharacter χ (leviCentralTorusPointToCenter i ν I t)))
  map_one' := by
    change Plancherel.normLog (LocalField.residueCardinality k) _ = 0
    rw [map_one, map_one, Plancherel.normLog_one]
  map_mul' a b := by
    change Plancherel.normLog (LocalField.residueCardinality k) _ = _ + _
    rw [map_mul, map_mul, Plancherel.normLog_mul]
    rfl

/-- The same logarithm on the integral selected-root annihilator. -/
def leviCentralLatticeCharacterLog
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ) :
    cocharacterAnnihilator T (rootSet i ν I) →+ ℝ :=
  AddMonoidHom.toMultiplicative.symm
    ((leviCentralTorusCharacterLog i ν I χ).comp
      (leviCentralUniformizerSection i ν hfinite I hexists))

/-- When the full-index Levi is the ambient group, annihilating all simple
roots puts a uniformizer point in the full abstract ambient center. -/
theorem uniformizerPowers_mem_center_of_all_pairings_eq_zero
    [Fintype (SimpleRoot i ν)]
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexistsFull : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν Finset.univ) ζ)
    (hfull : levi i ν Finset.univ = ⊤)
    (x : cocharacterLattice T)
    (hx : ∀ β : SimpleRoot i ν, simpleRootPairing i ν β x = 0) :
    uniformizerPowers i (.ofAdd x) ∈ Subgroup.center (rationalPoints G) := by
  apply Subgroup.mem_center_iff.mpr
  intro m
  exact commute_uniformizerPowers i ν hfinite Finset.univ hexistsFull x
    (fun β _ => hx β) m (by rw [hfull]; trivial)

/-- Ambient unit modulus kills the lattice logarithm on the common
annihilator of all simple roots. -/
theorem leviCentralLatticeCharacterLog_eq_zero_of_all_pairings_eq_zero
    [Fintype (SimpleRoot i ν)]
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hexistsFull : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν Finset.univ) ζ)
    (hfull : levi i ν Finset.univ = ⊤)
    (hZM : Subgroup.center (rationalPoints G) ≤ levi i ν I)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter (levi i ν I) hZM z) : ℂ)‖ = 1)
    (x : cocharacterAnnihilator T (rootSet i ν I))
    (hx : ∀ β : SimpleRoot i ν, simpleRootPairing i ν β x = 0) :
    leviCentralLatticeCharacterLog i ν hfinite I hexists χ x = 0 := by
  let z : Subgroup.center (rationalPoints G) :=
    ⟨uniformizerPowers i (.ofAdd (x : cocharacterLattice T)),
      uniformizerPowers_mem_center_of_all_pairings_eq_zero i ν hfinite
        hexistsFull hfull x hx⟩
  have heq : leviCentralTorusPointToCenter i ν I
      (leviCentralUniformizerSection i ν hfinite I hexists (.ofAdd x)) =
        ambientCenterToLeviCenter (levi i ν I) hZM z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hmod : PositiveCharacter.normCharacter χ
      (leviCentralTorusPointToCenter i ν I
        (leviCentralUniformizerSection i ν hfinite I hexists (.ofAdd x))) = 1 := by
    apply Units.ext
    apply NNReal.eq
    change ‖(χ _ : ℂ)‖ = 1
    rw [heq]
    exact hχambient z
  change Plancherel.normLog (LocalField.residueCardinality k) _ = 0
  rw [hmod, Plancherel.normLog_one]

/-- An additive real-valued function vanishing on the kernel of an integral
coordinate is proportional to that coordinate, with zero coefficient allowed. -/
theorem additiveLog_eq_mul_intCoordinate
    {L : Type*} [AddCommGroup L] (p : L →+ ℤ) (ℓ : L →+ ℝ)
    (hker : ∀ x, p x = 0 → ℓ x = 0) (ζ : L) (hζ : p ζ ≠ 0) (x : L) :
    ℓ x = (ℓ ζ / (p ζ : ℝ)) * (p x : ℝ) := by
  have hp : p ((p ζ) • x - (p x) • ζ) = 0 := by
    simp only [map_sub, map_zsmul, zsmul_eq_mul, Int.cast_id]
    ring
  have hℓ := hker _ hp
  simp only [map_sub, map_zsmul, zsmul_eq_mul] at hℓ
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (Int.cast_ne_zero.mpr hζ)).mpr
  nlinarith

/-- In corank one, ambient unit modulus forces the lattice logarithm to be
a single real multiple of the omitted-root pairing. -/
theorem leviCentralLatticeCharacterLog_eq_mul_omittedRoot
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (α : SimpleRoot i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν
      (rootSet i ν (Finset.univ.erase α)) ζ)
    (hexistsFull : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν Finset.univ) ζ)
    (hfull : levi i ν Finset.univ = ⊤)
    (hZM : Subgroup.center (rationalPoints G) ≤ levi i ν (Finset.univ.erase α))
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ)
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter _ hZM z) : ℂ)‖ = 1)
    (ζ : cocharacterAnnihilator T (rootSet i ν (Finset.univ.erase α)))
    (hζ : simpleRootPairing i ν α ζ ≠ 0)
    (x : cocharacterAnnihilator T (rootSet i ν (Finset.univ.erase α))) :
    leviCentralLatticeCharacterLog i ν hfinite _ hexists χ x =
      (leviCentralLatticeCharacterLog i ν hfinite _ hexists χ ζ /
        (simpleRootPairing i ν α ζ : ℝ)) * (simpleRootPairing i ν α x : ℝ) := by
  let p := (simpleRootPairing i ν α).comp
    (cocharacterAnnihilator T (rootSet i ν (Finset.univ.erase α))).subtype.toAddMonoidHom
  apply additiveLog_eq_mul_intCoordinate p _ ?_ ζ hζ x
  intro y hy
  apply leviCentralLatticeCharacterLog_eq_zero_of_all_pairings_eq_zero
    i ν hfinite _ hexists hexistsFull hfull hZM χ hχambient y
  intro β
  by_cases hβα : β = α
  · subst β
    exact hy
  · exact (mem_cocharacterAnnihilator.mp y.property) β.1
      ((val_mem_rootSet i ν _ β).mpr
        (Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ β⟩))

end Langlands.Aubert.General.RationalPointFamily
