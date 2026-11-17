import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight

/-! # Plancherel weights on unitary orbits for dynamic parabolics, with explicit density packages

For a connected reductive group `H` over a nonarchimedean local field, a torus `j : T → H` and a
cocharacter `ζ` of `T`, let `χ = ζ ∘ j`. This module descends the published Plancherel weight
`plancherelWeight j ζ …` from `Im X(Z_H(χ))` to the unitary unramified orbit of a discrete series
`π` of the literal Levi `Z_H(χ)(F)`. All analytic inputs of the weight (compact open subgroup,
Iwasawa decompositions, continuations, domains, irreducibility locus and unitary regularity) are
bundled in the explicit structure `DensityPackage`.

**Scope.** For arbitrary `j` this is the Library's expression `plancherelWeight j ζ …`, whose
product of rank-one constants is indexed by the roots of `j` (`rankOneCocharacterSet j ζ`). It is
Waldspurger's density `µ` of V.2 (printed p.292) only when `j` is a maximal split torus of `H`;
for a smaller torus the rank-one factors can merge and the constant differs. This module does
not assume maximality and does not discharge that identification. The intended use is
`H = Standard.leviScheme i ν J` and `j = Standard.leviTorusHom i ν J`, which is maximal split
by `Standard.isMaximalSplitTorus_leviTorusHom` when `i` is.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.DynamicInducedOrbit

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar UnramifiedOperatorFamily
open RationalDynamicSource RationalPlancherelDensity

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-! ### Restriction of unitary unramified characters and self-twists -/

section Restrict

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H)

set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme χ) ψ).toMul)

/-- **`Im X(Z_H(χ)(F)) ≅ Im X(Z_H(χ))`**: a unitary unramified character `z` of the literal Levi
subgroup `Z_H(χ)(F)` of `H(F)` gives the character `z ∘ e` of the points of the centralizer
scheme, where `e = parameterHomeomorph χ`. -/
def leviCharacterRestrict : unitaryUnramifiedCharacters (leviNormCharacters χ) ≃ₜ* UL :=
  (unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ) (normCharacters χ)).symm

omit [LocallyOfFiniteType H.X.hom] in
/-- The restricted character is `z ∘ e`. -/
theorem leviCharacterRestrict_apply (z : unitaryUnramifiedCharacters (leviNormCharacters χ))
    (m : rationalPoints (parameterScheme χ)) :
    (leviCharacterRestrict χ z).val m = z.val (parameterHomeomorph χ m) :=
  rfl

/-- If `B ⊗ ψ ≃ B` and `τ = ψ ∘ e`, then `(B ∘ e) ⊗ τ ≅ B ∘ e`. -/
theorem nonempty_twist_pullback_iso {M₁ M₂ : Type u} [Group M₁] [TopologicalSpace M₁]
    [Group M₂] [TopologicalSpace M₂] (e : M₂ ≃ₜ* M₁)
    (B : SmoothRep.{0, u, uV} ℂ M₁) {ψ : M₁ →* ℂˣ} (hψ : IsOpen (ψ.ker : Set M₁))
    {τ : M₂ →* ℂˣ} (hτ : IsOpen (τ.ker : Set M₂)) (hτψ : ∀ h, τ h = ψ (e h))
    (a : (B.twist ψ hψ).representation.Equiv B.representation) :
    Nonempty ((SmoothRep.pullback e B).twist τ hτ ≅ SmoothRep.pullback e B) :=
  ⟨SmoothRep.mkIso (Representation.Equiv.mk a.toLinearEquiv (fun h => by
    have ha := a.isIntertwining' (e h)
    change a.toLinearMap.comp ((ψ (e h) : ℂ) • B.representation (e h)) =
      (B.representation (e h)).comp a.toLinearMap at ha
    change a.toLinearMap.comp ((τ h : ℂ) • B.representation (e h)) =
      (B.representation (e h)).comp a.toLinearMap
    rw [hτψ]
    exact ha))⟩

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- A unitary unramified character `s` of `Z_H(χ)(F)` with `π ⊗ s ≅ π` restricts to a self-twist
of `π ∘ e`, the representation of the points of the centralizer scheme. -/
theorem leviCharacterRestrict_mem_stabilizer {s : unitaryUnramifiedCharacters (leviNormCharacters χ)}
    (hs : s ∈ discreteSeriesStabilizer C hC mu (leviNormCharacters χ)
      (discreteSeriesClass C hC mu π hsq)) :
    (⟨(leviCharacterRestrict χ s).val, (leviCharacterRestrict χ s).property.1⟩ :
        unramifiedCharacters (normCharacters χ)) ∈
      smoothRepUnramifiedTwistStabilizer (normCharacters χ)
        (SmoothRep.pullback (parameterHomeomorph χ) π.obj) := by
  obtain ⟨a⟩ := nonempty_twistEquiv_of_mem_discreteSeriesStabilizer C hC mu
    (leviNormCharacters χ) π hsq hs
  exact (SmoothRep.isoClass_eq_iff _ _).mpr
    (nonempty_twist_pullback_iso (parameterHomeomorph χ) π.obj
      (ψ := s.val.toMonoidHom) (τ := (leviCharacterRestrict χ s).val.toMonoidHom) _ _
      (leviCharacterRestrict_apply χ s) a)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu (leviNormCharacters χ)
  (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitMapπ" => discreteSeriesOrbitMap C hC mu (leviNormCharacters χ)
  (discreteSeriesClass C hC mu π hsq)

/-- **A weight on the orbit of `π`.** A function `W` on `Im X(Z_H(χ))` invariant under
translation by the unitary self-twists of `π ∘ e` gives the function `π ⊗ z ↦ W(z ∘ e)` on the
orbit `O` of `π`. -/
def orbitWeight (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer (normCharacters χ)
        (SmoothRep.pullback (parameterHomeomorph χ) π.obj))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints (parameterScheme χ)))
      (z : UL), W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) : Oπ → ℂ :=
  discreteSeriesOrbitDescend C hC mu (leviNormCharacters χ) π hsq
    (fun z => W (leviCharacterRestrict χ z))
    (fun s hs z => by
      have h := hW ⟨_, leviCharacterRestrict_mem_stabilizer χ π C hC mu hsq hs⟩
        (leviCharacterRestrict χ s).property.2 (leviCharacterRestrict χ z)
      change W (leviCharacterRestrict χ (z * s)) = W (leviCharacterRestrict χ z)
      rw [map_mul, mul_comm]
      exact h)

/-- The weight at `π ⊗ z` is `W(z ∘ e)`. -/
theorem orbitWeight_orbitMap (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer (normCharacters χ)
        (SmoothRep.pullback (parameterHomeomorph χ) π.obj))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints (parameterScheme χ)))
      (z : UL), W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z)
    (z : unitaryUnramifiedCharacters (leviNormCharacters χ)) :
    orbitWeight χ π C hC mu hsq W hW (orbitMapπ z) = W (leviCharacterRestrict χ z) :=
  discreteSeriesOrbitDescend_orbitMap C hC mu _ π hsq _ _ z

/-- The orbit weight of a continuous `W` is continuous on `O`. -/
theorem continuous_orbitWeight {W : UL → ℂ}
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer (normCharacters χ)
        (SmoothRep.pullback (parameterHomeomorph χ) π.obj))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints (parameterScheme χ)))
      (z : UL), W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) (hWc : Continuous W) :
    Continuous (orbitWeight χ π C hC mu hsq W hW) :=
  continuous_discreteSeriesOrbitDescend C hC mu _ π hsq _
    (hWc.comp (leviCharacterRestrict χ).continuous)

end Restrict

/-! ### Density packages and the Plancherel weight on the orbit -/

section Package

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (j : T.toGrp ⟶ H)
  (ζ : cocharacterLattice T)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hH : IsConnectedReductive H)
  (A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ζ ≫ j)))

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ j
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ j)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ j)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ j) hH

/-- **A Plancherel density package for `A` on `Z_H(χ)(F)`, `χ = ζ ∘ j`.** No maximality
condition is imposed on `j`; see the module docstring for the scope. These are all the
inputs of the published `plancherelWeight j ζ …` besides the two global statements `hRefl`,
`hCST` and the reductivity `hH`: a compact open subgroup `K` of `H(F)` with Iwasawa
decompositions for `P(χ)(F)` and the opposite parabolic, forward and reverse continuations of the
standard intertwining integrals, nonempty open convergence domains inside their full-domain
regions, a nonempty open set of characters on which the induced representations are
irreducible, and regularity of `j_P⁻¹` at every unitary unramified character. -/
structure DensityPackage where
  /-- The compact open subgroup of `H(F)`. -/
  K : OpenSubgroup (RationalPoint F H.X)
  hK : IsCompact (K : Set (RationalPoint F H.X))
  hPK : ∀ g : RationalPoint F H.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F H.X) * (k : RationalPoint F H.X)
  hOppK : ∀ g : RationalPoint F H.X,
    ∃ p : oppositeParabolic χ, ∃ k : K, g = (p : RationalPoint F H.X) * (k : RationalPoint F H.X)
  /-- The continuation of the forward standard intertwining integral. -/
  p : ForwardContinuation χ hRefl hCST hH K hK hPK hOppK A
  /-- The continuation of the reverse standard intertwining integral. -/
  q : ReverseContinuation χ hRefl hCST hH K hK hPK hOppK A
  DForward : Set (unramifiedCharacters νL)
  DReverse : Set (unramifiedCharacters νL)
  hDForward : IsOpen DForward
  hneForward : DForward.Nonempty
  hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A
  hDReverse : IsOpen DReverse
  hneReverse : DReverse.Nonempty
  hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A
  /-- The generic irreducibility domain. -/
  D : Set (unramifiedCharacters νL)
  hD : IsOpen D
  hne : D.Nonempty
  hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible
  /-- Regularity of `j_P⁻¹` at every unitary unramified character. -/
  hreg : RationalFunctionUnitaryRegular MS hMS
    (conditionalCanonicalRationalScalar χ hRefl hCST hH K hK hPK hOppK A
      p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr)⁻¹

namespace DensityPackage

variable {j ζ hRefl hCST hH A}

/-- The canonical scalar `j_P` of the package. -/
abbrev canonicalScalar (P : DensityPackage j ζ hRefl hCST hH A) :=
  conditionalCanonicalRationalScalar χ hRefl hCST hH P.K P.hK P.hPK P.hOppK A
    P.p P.q P.hneForward P.hDForwardΩ P.hneReverse P.hDReverseΩ P.hne P.hirr

/-- **The Plancherel weight of the package** on `Im X(Z_H(χ))`: the published Library
expression `plancherelWeight j ζ …` with the data of the package. When `j` is a maximal split
torus of `H` it is Waldspurger's `z ↦ µ(A ⊗ z)` (V.2, V.2.1, printed p.292); for arbitrary `j`
its rank-one product is indexed by the roots of `j` and need not be the source constant. -/
def weight (P : DensityPackage j ζ hRefl hCST hH A) :
    unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters MS ψ).toMul) → ℂ :=
  plancherelWeight j ζ hRefl hCST hH P.K P.hK P.hPK P.hOppK A P.p P.q P.hneForward
    P.hDForwardΩ P.hneReverse P.hDReverseΩ P.hne P.hirr P.hreg

/-- The weight is invariant under unitary self-twists of `A ∘ e`
(`plancherelWeight_stabilizer_invariant`). -/
theorem weight_stabilizer_invariant (P : DensityPackage j ζ hRefl hCST hH A)
    (τ : smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) A))
    (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS))
    (z : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters MS ψ).toMul)) :
    P.weight (⟨τ.val.val, τ.val.property, hτ⟩ * z) = P.weight z :=
  plancherelWeight_stabilizer_invariant j ζ hRefl hCST hH P.K P.hK P.hPK P.hOppK A P.p P.q
    P.hDForward P.hneForward P.hDForwardΩ P.hDReverse P.hneReverse P.hDReverseΩ P.hD P.hne
    P.hirr P.hreg τ hτ z

end DensityPackage

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
    (G := levi (CommGroupScheme.groupHom ζ ≫ j)))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- **The Plancherel weight on the orbit of `π`**: `π ⊗ z ↦ P.weight (z ∘ e)` on the unitary
unramified orbit `O` of the discrete series `π` of `Z_H(χ)(F)`, for a package `P` with `A = π`.
It is well defined by the invariance of the weight under unitary self-twists. When `j` is a
maximal split torus of `H` this is Waldspurger's `π ⊗ z ↦ µ(π ⊗ z)` (V.2, printed p.292);
this definition does not assume or prove that. -/
def orbitPlancherelWeight (P : DensityPackage j ζ hRefl hCST hH π.obj) :
    discreteSeriesOrbit C hC mu (leviNormCharacters χ) (discreteSeriesClass C hC mu π hsq) → ℂ :=
  orbitWeight χ π C hC mu hsq P.weight P.weight_stabilizer_invariant

/-- The weight at `π ⊗ z` is the package weight at `z ∘ e`. -/
theorem orbitPlancherelWeight_orbitMap (P : DensityPackage j ζ hRefl hCST hH π.obj)
    (z : unitaryUnramifiedCharacters (leviNormCharacters χ)) :
    orbitPlancherelWeight j ζ hRefl hCST hH π C hC mu hsq P
        (discreteSeriesOrbitMap C hC mu (leviNormCharacters χ)
          (discreteSeriesClass C hC mu π hsq) z) =
      P.weight (leviCharacterRestrict χ z) :=
  orbitWeight_orbitMap χ π C hC mu hsq _ _ z

/-- The Plancherel weight on the orbit is continuous. -/
theorem continuous_orbitPlancherelWeight (P : DensityPackage j ζ hRefl hCST hH π.obj) :
    Continuous (orbitPlancherelWeight j ζ hRefl hCST hH π C hC mu hsq P) :=
  continuous_orbitWeight χ π C hC mu hsq _
    (continuous_plancherelWeight j ζ hRefl hCST hH P.K P.hK P.hPK P.hOppK π.obj P.p P.q
      P.hneForward P.hDForwardΩ P.hneReverse P.hDReverseΩ P.hne P.hirr P.hreg)

end Package

end Langlands.HarishChandraSchwartz.DynamicInducedOrbit
