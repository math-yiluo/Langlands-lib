import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket
import Langlands.Representation.Aubert.General.RationalLeviCharacterDensity
import Langlands.Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison

/-! # Wave packets for actual standard parabolic subgroups (Waldspurger VI.1–VI.3)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this
module instantiates the Library's wave packets (`OrbitWavePacket`) on actual rational points:

* circle coordinates on `Im X(M_I)` for the literal Levi subgroup `M_I(F)`
  (`leviRationalUnitaryCoordinates`), transported from the canonical coordinates of the Levi
  scheme, with the Laurent property of evaluation;
* Waldspurger's `C^∞(O, P)` (`rationalInducedSmoothOrbitSections`) and the orbit coefficients
  `ω ↦ E_P^G ψ_ω` (`rationalInducedOrbitCoefficientMap`), which at a representative are the
  coefficient map `rationalInducedCoefficientMap` of `RationalInducedCoefficients`;
* Lemma VI.2.2 on `C^∞(O, P)`;
* the wave packet `f_ψ(g) = ∫_O w(ω) (E_P^G ψ_ω)(g) dω` (`rationalInducedOrbitWavePacket`), with a
  weight `w` in place of the Plancherel density `µ`, and its first properties: the bound by a
  multiple of `Ξ`, bi-invariance, integrability, linearity, and the formula as an integral over
  `Im X(M_I)`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Transport

variable {A : Type*} [Group A] [TopologicalSpace A] {B : Type*} [Group B] [TopologicalSpace B]
  {Ix : Type*}

/-- Transport of unitary unramified characters along a multiplicative homeomorphism
`e : A ≃ₜ* B`: `χ ↦ χ ∘ e⁻¹`, for the norm family `ν` on `A` and its transport `ν ∘ e⁻¹` on `B`. -/
def unitaryUnramifiedCharactersHomeomorph (e : A ≃ₜ* B) (ν : Ix → (A →* ℝ≥0ˣ)) :
    unitaryUnramifiedCharacters ν ≃ₜ*
      unitaryUnramifiedCharacters (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom) where
  toFun χ := ⟨χ.val.comp (e.symm : B →ₜ* A),
    (unramifiedCharactersHomeomorph e ν ⟨χ.val, χ.2.1⟩).2, fun b => χ.2.2 (e.symm b)⟩
  invFun χ := ⟨χ.val.comp (e : A →ₜ* B),
    ((unramifiedCharactersHomeomorph e ν).symm ⟨χ.val, χ.2.1⟩).2, fun a => χ.2.2 (e a)⟩
  left_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro a
    change χ.val (e.symm (e a)) = χ.val a
    rw [e.symm_apply_apply]
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    change χ.val (e (e.symm b)) = χ.val b
    rw [e.apply_symm_apply]
  map_mul' χ₁ χ₂ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    rfl
  continuous_toFun :=
    ((e.symm : B →ₜ* A).continuous_comp_left.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((e : A →ₜ* B).continuous_comp_left.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem unitaryUnramifiedCharactersHomeomorph_apply (e : A ≃ₜ* B) (ν : Ix → (A →* ℝ≥0ˣ))
    (χ : unitaryUnramifiedCharacters ν) (b : B) :
    (unitaryUnramifiedCharactersHomeomorph e ν χ).val b = χ.val (e.symm b) := rfl

/-- Laurent torus coordinates transport along `e`: if evaluation at every point of `A` is a
Laurent character of the coordinates `E`, the same holds on `B` for the transported coordinates. -/
theorem hasLaurentUnitaryCoordinates_transport (e : A ≃ₜ* B) (ν : Ix → (A →* ℝ≥0ˣ))
    {J : Type*} [Fintype J] (E : unitaryUnramifiedCharacters ν ≃* (J → Circle))
    (hE : HasLaurentUnitaryCoordinates ν E) :
    HasLaurentUnitaryCoordinates (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom)
      ((unitaryUnramifiedCharactersHomeomorph e ν).toMulEquiv.symm.trans E) := by
  intro b
  obtain ⟨n, hn⟩ := hE (e.symm b)
  exact ⟨n, fun z => hn z⟩

end Transport

section LeviCoordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance instRationalInducedOrbitWavePacket1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instRationalInducedOrbitWavePacket2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalInducedOrbitWavePacket3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalInducedOrbitWavePacket4 : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology
local instance instRationalInducedOrbitWavePacket5
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- The standard Levi scheme `M_I` is connected reductive. -/
theorem isConnectedReductive_leviScheme_rootSet :
    IsConnectedReductive (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)) :=
  BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν _
    (RationalPointFamily.rootSet_subset i ν I)

/-- **Circle coordinates on `Im X(M_I)`** for the literal Levi subgroup `M_I(F)` of `G(F)`: the
Library's canonical coordinates `rationalCanonicalUnitaryUnramifiedCharacterCoordinates` of the
unitary unramified characters of the Levi scheme, transported along the canonical point
homeomorphism `leviRationalPointHomeomorph` (the unitary analogue of
`leviRationalUnramifiedCharacterCoordinates`). -/
def leviRationalUnitaryCoordinates :
    unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I) ≃ₜ*
      (Fin (rationalImageRank (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) →
        Circle) :=
  (unitaryUnramifiedCharactersHomeomorph (RationalPointFamily.leviRationalPointHomeomorph i ν I)
    (fun χ => (rationalNormCharacters
      (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)) χ).toMul)).symm.trans
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates _
      (isConnectedReductive_leviScheme_rootSet hG hi hν I))

include hG hi hν in
/-- Evaluation of a unitary unramified character of `M_I(F)` at a point is a Laurent monomial of
its circle coordinates. -/
theorem leviRationalUnitaryCoordinates_hasLaurent :
    HasLaurentUnitaryCoordinates (RationalPointFamily.leviRationalNormCharacters i ν I)
      (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv :=
  hasLaurentUnitaryCoordinates_transport (RationalPointFamily.leviRationalPointHomeomorph i ν I)
    _ _ (rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent _
      (isConnectedReductive_leviScheme_rootSet hG hi hν I))

end LeviCoordinates

section WavePacket

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

/-- **Waldspurger's `C^∞(O, P)` for an actual standard parabolic** `P = P_I(F)` (VI.1): the
Library's smooth orbit sections `productInducedSmoothOrbitSections` over the unitary unramified
twist orbit of the irreducible admissible representation `π` of `M_I(F)`, for the actual
decomposition `P_I(F) = M_I(F) ⋉ U_I(F)`, the compact open `K`, the norm characters
`leviRationalNormCharacters i ν I` and the circle coordinates `leviRationalUnitaryCoordinates`. -/
abbrev rationalInducedSmoothOrbitSections :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  productInducedSmoothOrbitSections (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))

variable (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- **The coefficients `ω ↦ E_P^G ψ_ω` on the orbit** for an actual standard parabolic: for
`ψ ∈ C^∞(O, P)` and a class `ω` of the unitary unramified orbit `O` of `π` (discrete series
modulo the central subgroup `C`), the coefficient of `ψ` at a representative of `ω`. This is the
Library's `unitaryOrbitCoefficientMap` on actual data; it does not depend on the representative
(`rationalInducedOrbitCoefficientMap_representative`). -/
abbrev rationalInducedOrbitCoefficientMap :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  unitaryOrbitCoefficientMap (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    C hC mu hsq (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv

/-- At the class of a representative `A` of the orbit, the orbit coefficient of `ψ` is the
coefficient map `E_P^G = rationalInducedCoefficientMap` of `A` applied to the value `ψ_A`. -/
theorem rationalInducedOrbitCoefficientMap_representative
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π) :
    rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit
          (RationalPointFamily.leviRationalNormCharacters i ν I) π C hC mu hsq A) =
      rationalInducedCoefficientMap hG hi hν I hKc hPK A.val.obj A.val.property.2 (q.val A) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := unitaryOrbitCoefficientMap_representative (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    C hC mu hsq (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv q A
  unfold unitaryOrbitRepresentativeCoefficientMap at h
  rewrite [rationalInducedCoefficientMap_eq_coefficientMap]
  with_reducible_and_instances exact h

variable (hM : IsIwasawaPair
  ((standardParabolicPoints i ν ∅).subgroupOf
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
  ((K : Subgroup (rationalPoints G)).subgroupOf
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))

/-- **Waldspurger's Lemma VI.2.2 on actual rational points** (printed p. 298): if every
coefficient of `π` is bounded by a multiple of `Ξ^{M_I}` (`hcoeff`, the conclusion of
Corollary III.1.2 for `π`), then for every `ψ ∈ C^∞(O, P)` there is `c > 0` with
`|(E_P^G ψ_ω)(g)| ≤ c Ξ(g)` for all `ω ∈ O` and `g ∈ G(F)`. -/
theorem exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ω : discreteSeriesOrbit C hC mu
        (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))
        (g : rationalPoints G),
      ‖rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q ω g‖ ≤
        c * rationalXi hKc hPK g := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitCoefficientMap_le_xi (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q
  refine ⟨c, hc, fun ω g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  rewrite [← hx]
  with_reducible_and_instances exact hb ω g

variable [Finite (discreteSeriesStabilizer C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC mu (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC mu π hsq) → ℂ)

/-- **The wave packet `f_ψ` for an actual standard parabolic** (Waldspurger VI.3, printed
p. 302): for `ψ = q ∈ C^∞(O, P)`,
`f_ψ(g) = ∫_O w(ω) (E_P^G ψ_ω)(g) dω`, `g ∈ G(F)`,
for the measure on `O` attached to a measure `ρ` on `Im X(M_I)` (`discreteSeriesOrbitMeasure`,
`|S|⁻¹` times the push-forward of `ρ` along `χ ↦ π ⊗ χ`, `S` the stabilizer of the class of
`π`), with a weight `w` on `O` in place of Waldspurger's Plancherel density `µ`. It is the
Library's `inducedOrbitWavePacket` on the actual data of `P_I(F)`. -/
def rationalInducedOrbitWavePacket (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (g : rationalPoints G) : ℂ :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  inducedOrbitWavePacket (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w q g

/-- `f_ψ(g) = ∫_O w(ω) (E_P^G ψ_ω)(g) dω`. -/
theorem rationalInducedOrbitWavePacket_apply
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (g : rationalPoints G) :
    rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g =
      ∫ ω, w ω * rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q ω g
        ∂discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
          (discreteSeriesClass C hC mu π hsq) ρ :=
  rfl

/-- **The first bound for the wave packet** (proof of Proposition VI.3.1, from Lemma VI.2.2): for
a finite measure `ρ` and a bounded weight `w`, there is `c > 0` with `|f_ψ(g)| ≤ c Ξ(g)` on
`G(F)`. -/
theorem exists_norm_rationalInducedOrbitWavePacket_le_rationalXi [IsFiniteMeasure ρ] {b : ℝ}
    (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : rationalPoints G,
      ‖rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g‖ ≤
        c * rationalXi hKc hPK g := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  obtain ⟨c, hc, hb⟩ := exists_norm_inducedOrbitWavePacket_le_xi (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w hw
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q
  refine ⟨c, hc, fun g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  unfold rationalInducedOrbitWavePacket
  rewrite [← hx]
  with_reducible_and_instances exact hb g

/-- One compact open subgroup `H ≤ K` makes the wave packet `f_ψ` bi-invariant. -/
theorem exists_rationalInducedOrbitWavePacket_biInvariant
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ H : OpenSubgroup (rationalPoints G), H ≤ K ∧ IsCompact (H : Set (rationalPoints G)) ∧
      ∀ (k l : H) (g : rationalPoints G),
        rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q
            ((k : rationalPoints G) * g * (l : rationalPoints G)) =
          rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := exists_inducedOrbitWavePacket_biInvariant (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w q
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

/-- The integrand `ω ↦ w(ω) (E_P^G ψ_ω)(g)` of the wave packet is integrable over `O`, for a
finite `ρ` and a bounded, almost everywhere strongly measurable weight `w`. -/
theorem integrable_rationalInducedOrbitWavePacket_integrand [IsFiniteMeasure ρ]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
        (discreteSeriesClass C hC mu π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) :
    Integrable
      (fun ω => w ω * rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q ω g)
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
        (discreteSeriesClass C hC mu π hsq) ρ) := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := integrable_inducedOrbitWavePacket_integrand (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hwm hw
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q g
  with_reducible_and_instances exact h

/-- `f_{c ψ} = c f_ψ`. -/
theorem rationalInducedOrbitWavePacket_smul (c : ℂ)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (g : rationalPoints G) :
    rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w (c • q) g =
      c * rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := inducedOrbitWavePacket_smul (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w c q g
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

/-- `f_{ψ + ψ'} = f_ψ + f_{ψ'}`, under the hypotheses of
`integrable_rationalInducedOrbitWavePacket_integrand`. -/
theorem rationalInducedOrbitWavePacket_add [IsFiniteMeasure ρ]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
        (discreteSeriesClass C hC mu π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q r : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) :
    rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w (q + r) g =
      rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g +
        rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w r g := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := inducedOrbitWavePacket_add (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hwm hw
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q r g
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

/-- **The wave packet as a linear map** `ψ ↦ f_ψ` on `C^∞(O, P)`, for a finite `ρ` and a
bounded, almost everywhere strongly measurable weight `w`. -/
def rationalInducedOrbitWavePacketLinear [IsFiniteMeasure ρ]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
        (discreteSeriesClass C hC mu π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m) :
    rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π →ₗ[ℂ] (rationalPoints G → ℂ) where
  toFun q := rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q
  map_add' q r := funext fun g =>
    rationalInducedOrbitWavePacket_add hG hi hν I hKc hPK π C hC mu hsq hM ρ w hwm hw hcoeff q r g
  map_smul' c q := funext fun g =>
    rationalInducedOrbitWavePacket_smul hG hi hν I hKc hPK π C hC mu hsq ρ w c q g

/-- **The wave packet as an integral over `Im X(M_I)`**: `f_ψ(g)` is `|S|⁻¹` times the integral
over `ρ` of `w(π ⊗ χ) (E_P^G ψ_{π ⊗ χ})(g)`, `S` the finite stabilizer of the class of `π`. -/
theorem rationalInducedOrbitWavePacket_eq_parameterIntegral
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
        (discreteSeriesClass C hC mu π hsq) ρ))
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) :
    rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g =
      (Nat.card (discreteSeriesStabilizer C hC mu
          (RationalPointFamily.leviRationalNormCharacters i ν I)
          (discreteSeriesClass C hC mu π hsq)) : ℝ)⁻¹ •
        ∫ χ, w (discreteSeriesOrbitMap C hC mu
            (RationalPointFamily.leviRationalNormCharacters i ν I)
            (discreteSeriesClass C hC mu π hsq) χ) *
          rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q
            (discreteSeriesOrbitMap C hC mu
              (RationalPointFamily.leviRationalNormCharacters i ν I)
              (discreteSeriesClass C hC mu π hsq) χ) g ∂ρ := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := inducedOrbitWavePacket_eq_parameterIntegral (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hwm q g
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

end WavePacket

end Langlands.HarishChandraSchwartz
