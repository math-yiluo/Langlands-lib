import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCCovariance

/-! # Covariance of the weighted c-family under unramified self-twists -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

/-- Linear equivalences of representations commute with scalars. -/
theorem representationEquiv_smul_apply {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) (c : k) (x : V) : c • e x = e (c • x) :=
  (map_smul e c x).symm

/-! ### Values of translation-fixed rational functions -/

section Translation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : GroupScheme (Spec (CommRingCat.of F))} [TopologicalSpace (rationalPoints S)]
  {hp : Continuous (rationalValuationImageProjection S)} {hS : IsConnectedReductive S}

/-- The value of a rational function at a regular point depends only on the point. -/
theorem rationalValueAt_congr_point {f : rationalUnramifiedFunctionField S hp hS}
    {z z' : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)} (h : z = z')
    (hz : RationalFunctionRegularAt S hp hS f z) (hz' : RationalFunctionRegularAt S hp hS f z') :
    rationalValueAt f hz = rationalValueAt f hz' := by
  subst h
  rfl

/-- Regularity and the value transfer along an equality of points. -/
theorem exists_rationalValueAt_of_eq {f : rationalUnramifiedFunctionField S hp hS}
    {z z' : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)} (h : z = z')
    (hz : RationalFunctionRegularAt S hp hS f z) :
    ∃ hz' : RationalFunctionRegularAt S hp hS f z', rationalValueAt f hz' = rationalValueAt f hz := by
  subst h
  exact ⟨hz, rfl⟩

set_option maxHeartbeats 1600000 in
/-- A rational function fixed by translation by `τ` and regular at `τ z` is regular at `z`, with
the same value. -/
theorem exists_rationalValueAt_eq_of_translation_eq
    {f : rationalUnramifiedFunctionField S hp hS}
    {τ z : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hfix : rationalUnramifiedFunctionFieldTranslation S hp hS τ f = f)
    (hz : RationalFunctionRegularAt S hp hS f (τ * z)) :
    ∃ hz' : RationalFunctionRegularAt S hp hS f z, rationalValueAt f hz' = rationalValueAt f hz := by
  obtain ⟨m, d, hd, hf⟩ := hz
  have hd' : (unramifiedRegularTranslation _ τ d).val z ≠ 0 := by
    rw [unramifiedRegularTranslation_apply]
    exact hd
  have hf' : f = algebraMap _ (rationalUnramifiedFunctionField S hp hS)
        (unramifiedRegularTranslation _ τ m) /
      algebraMap _ (rationalUnramifiedFunctionField S hp hS) (unramifiedRegularTranslation _ τ d) := by
    conv_lhs => rw [← hfix, hf]
    rw [map_div₀, rationalUnramifiedFunctionFieldTranslation_algebraMap,
      rationalUnramifiedFunctionFieldTranslation_algebraMap]
  have hz' : RationalFunctionRegularAt S hp hS f z := ⟨_, _, hd', hf'⟩
  have hz₁ : RationalFunctionRegularAt S hp hS f (τ * z) := ⟨m, d, hd, hf⟩
  exact ⟨hz', (rationalValueAt_eq hz' hd' hf').trans (rationalValueAt_eq hz₁ hd hf).symm⟩

/-- A rational function fixed by translation by `τ` is regular at `τ z` if and only if it is
regular at `z`, and its values there agree. -/
theorem exists_rationalValueAt_mul_eq_of_translation_eq
    {f : rationalUnramifiedFunctionField S hp hS}
    {τ z : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hfix : rationalUnramifiedFunctionFieldTranslation S hp hS τ⁻¹ f = f)
    (hz : RationalFunctionRegularAt S hp hS f z) :
    ∃ hz' : RationalFunctionRegularAt S hp hS f (τ * z),
      rationalValueAt f hz' = rationalValueAt f hz := by
  have hz₀ : RationalFunctionRegularAt S hp hS f (τ⁻¹ * (τ * z)) := by
    rwa [inv_mul_cancel_left]
  obtain ⟨hz', heq⟩ := exists_rationalValueAt_eq_of_translation_eq hfix hz₀
  exact ⟨hz', heq.trans (rationalValueAt_congr_point (inv_mul_cancel_left τ z) hz₀ hz)⟩

/-- A rational function fixed by translation by `τ` is fixed by translation by `τ⁻¹`. -/
theorem translation_inv_eq_of_translation_eq {f : rationalUnramifiedFunctionField S hp hS}
    {τ : unramifiedCharacters (fun ψ => (rationalNormCharacters S ψ).toMul)}
    (hfix : rationalUnramifiedFunctionFieldTranslation S hp hS τ f = f) :
    rationalUnramifiedFunctionFieldTranslation S hp hS τ⁻¹ f = f := by
  calc rationalUnramifiedFunctionFieldTranslation S hp hS τ⁻¹ f
      = rationalUnramifiedFunctionFieldTranslation S hp hS τ⁻¹
          (rationalUnramifiedFunctionFieldTranslation S hp hS τ f) := by rw [hfix]
    _ = rationalUnramifiedFunctionFieldTranslation S hp hS (τ * τ⁻¹) f := by
          rw [rationalUnramifiedFunctionFieldTranslation_mul]
          rfl
    _ = f := by
          rw [mul_inv_cancel, rationalUnramifiedFunctionFieldTranslation_one]
          rfl

end Translation


/-! ### Translation invariance of the package densities -/

section Package

attribute [local instance]
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
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {j : S.toGrp ⟶ H} {ξ : cocharacterLattice S}
  {hRefl : RelativeRootReflectionExistenceStatement.{u}}
  {hCST : CentralSplitTorusCharacterStatement.{u}} {hH : IsConnectedReductive H}
  {A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ξ ≫ j))}

/-- **The package density is fixed by translation by self-twists** of the inducing
representation (V.2.1 for the stabilizer; `plancherelDensity_stabilizer_fixed`). -/
theorem packageDensity_translation_eq (P : DynamicInducedOrbit.DensityPackage j ξ hRefl hCST hH A)
    (τ : smoothRepUnramifiedTwistStabilizer (normCharacters (CommGroupScheme.groupHom ξ ≫ j))
      (SmoothRep.pullback (parameterHomeomorph (CommGroupScheme.groupHom ξ ≫ j)) A)) :
    rationalUnramifiedFunctionFieldTranslation (parameterScheme (CommGroupScheme.groupHom ξ ≫ j))
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
        (parameterScheme_isConnectedReductive _ hH) τ.val (packageDensity P) =
      packageDensity P :=
  RationalPlancherelDensity.plancherelDensity_stabilizer_fixed j ξ hRefl hCST hH P.K P.hK P.hPK
    P.hOppK A P.p P.q P.hDForward P.hneForward P.hDForwardΩ P.hDReverse P.hneReverse
    P.hDReverseΩ P.hD P.hne P.hirr τ

/-- The package density is regular at `τ z` for a self-twist `τ` whenever it is regular at `z`,
with the same value. -/
theorem exists_packageDensity_value_mul_eq
    (P : DynamicInducedOrbit.DensityPackage j ξ hRefl hCST hH A)
    {τ : unramifiedCharacters (normCharacters (CommGroupScheme.groupHom ξ ≫ j))}
    (hτ : τ ∈ smoothRepUnramifiedTwistStabilizer (normCharacters (CommGroupScheme.groupHom ξ ≫ j))
      (SmoothRep.pullback (parameterHomeomorph (CommGroupScheme.groupHom ξ ≫ j)) A))
    {z : unramifiedCharacters (normCharacters (CommGroupScheme.groupHom ξ ≫ j))}
    (hz : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ξ ≫ j))
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ hH) (packageDensity P) z) :
    ∃ hz' : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ξ ≫ j))
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
        (parameterScheme_isConnectedReductive _ hH) (packageDensity P) (τ * z),
      rationalValueAt (packageDensity P) hz' = rationalValueAt (packageDensity P) hz :=
  exists_rationalValueAt_mul_eq_of_translation_eq
    (packageDensity_translation_eq P ⟨τ⁻¹, Subgroup.inv_mem _ hτ⟩) hz

/-- The package density is regular at `w = τ z` for a self-twist `τ` whenever it is regular at
`z`, with the same value. -/
theorem exists_packageDensity_value_eq_of_mul_eq
    (P : DynamicInducedOrbit.DensityPackage j ξ hRefl hCST hH A)
    {τ z w : unramifiedCharacters (normCharacters (CommGroupScheme.groupHom ξ ≫ j))}
    (hτ : τ ∈ smoothRepUnramifiedTwistStabilizer (normCharacters (CommGroupScheme.groupHom ξ ≫ j))
      (SmoothRep.pullback (parameterHomeomorph (CommGroupScheme.groupHom ξ ≫ j)) A))
    (hw : τ * z = w)
    (hz : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ξ ≫ j))
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ hH) (packageDensity P) z) :
    ∃ hw' : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ξ ≫ j))
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
        (parameterScheme_isConnectedReductive _ hH) (packageDensity P) w,
      rationalValueAt (packageDensity P) hw' = rationalValueAt (packageDensity P) hz := by
  obtain ⟨h₁, heq₁⟩ := exists_packageDensity_value_mul_eq P hτ hz
  obtain ⟨h₂, heq₂⟩ := exists_rationalValueAt_of_eq hw h₁
  exact ⟨h₂, heq₂.trans heq₁⟩

end Package

/-! ### The two density parameters along a self-twist -/

section Parameters

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine
  cFamilyLeviFiniteType

attribute [local instance]
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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

omit [LocallyOfFiniteType G.X.hom] in
/-- The complex restriction is `z ∘ e`. -/
theorem standardLeviUnramifiedRestrict_apply (z : unramifiedCharacters νM)
    (m : rationalPoints (parameterScheme (CommGroupScheme.groupHom ζ ≫ i))) :
    (standardLeviUnramifiedRestrict hG hi hν I hζ z).val m =
      z.val (standardLeviDynamicHomeomorph hG hi hν I hζ
        (parameterHomeomorph (CommGroupScheme.groupHom ζ ≫ i) m)) := by
  change z.val (RationalPointFamily.leviRationalPointHomeomorph i ν I
    (rationalPoints.map (standardLeviParameterIso hG hi hν I hζ).hom m)) = _
  rw [leviRationalPointHomeomorph_map_standardLeviParameterIso]

omit [LocallyOfFiniteType G.X.hom] in
theorem standardLeviUnramifiedRestrict_mul (z w : unramifiedCharacters νM) :
    standardLeviUnramifiedRestrict hG hi hν I hζ (z * w) =
      standardLeviUnramifiedRestrict hG hi hν I hζ z * standardLeviUnramifiedRestrict hG hi hν I hζ w := by
  unfold standardLeviUnramifiedRestrict
  exact (congrArg (rationalUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom)
    (map_mul (unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I)
      (fun ψ => (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) ψ).toMul)).symm
      z w)).trans (map_mul _ _ _)

/-- A self-twist of `π` restricts to a self-twist of the inducing representation `π ∘ e` of
`Z_G(ζ ∘ i)(F)`. -/
theorem standardLeviUnramifiedRestrict_mem_stabilizer
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌)) (τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation) :
    standardLeviUnramifiedRestrict hG hi hν I hζ τ ∈
      smoothRepUnramifiedTwistStabilizer (normCharacters (CommGroupScheme.groupHom ζ ≫ i))
        (SmoothRep.pullback (parameterHomeomorph (CommGroupScheme.groupHom ζ ≫ i))
          (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj)) :=
  (SmoothRep.isoClass_eq_iff _ _).mpr
    (nonempty_twist_pullback_pullback_iso (parameterHomeomorph (CommGroupScheme.groupHom ζ ≫ i))
      (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
      (ψ := τ.val.toMonoidHom)
      (τ := (standardLeviUnramifiedRestrict hG hi hν I hζ τ).val.toMonoidHom) _ _
      (standardLeviUnramifiedRestrict_apply hG hi hν I hζ τ) a.symm)

/-- **The parameter of the lower density** at `z`: `sz`, read on the centralizer scheme of
`χ_s`. -/
abbrev lowerDensityParameter (z : unramifiedCharacters νM) :
    unramifiedCharacters (normCharacters χs) :=
  (parameterTransport χs).symm (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)

theorem lowerDensityParameter_apply (z : unramifiedCharacters νM)
    (m : rationalPoints (parameterScheme χs)) :
    (lowerDensityParameter hG hi hν I I' hζ n hn z).val m =
      z.val ((eₛ).symm (parameterHomeomorph χs m)) :=
  rfl

theorem lowerDensityParameter_mul (z w : unramifiedCharacters νM) :
    lowerDensityParameter hG hi hν I I' hζ n hn (z * w) =
      lowerDensityParameter hG hi hν I I' hζ n hn z *
        lowerDensityParameter hG hi hν I I' hζ n hn w := by
  unfold lowerDensityParameter
  exact (congrArg (parameterTransport χs).symm
    (map_mul (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn) z w)).trans
    (map_mul (parameterTransport χs).symm _ _)

/-- A self-twist of `π` gives a self-twist of the inducing representation `sπ` of the lower
density, read on the centralizer scheme of `χ_s`. -/
theorem lowerDensityParameter_mem_stabilizer
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌)) (τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation) :
    lowerDensityParameter hG hi hν I I' hζ n hn τ ∈
      smoothRepUnramifiedTwistStabilizer (normCharacters χs)
        (SmoothRep.pullback (parameterHomeomorph χs)
          (lowerRepresentation hG hi hν I I' hζ n hn π).obj) :=
  (SmoothRep.isoClass_eq_iff _ _).mpr
    (nonempty_twist_pullback_pullback_iso (parameterHomeomorph χs) (eₛ).symm π.obj
      (ψ := τ.val.toMonoidHom)
      (τ := (lowerDensityParameter hG hi hν I I' hζ n hn τ).val.toMonoidHom) _ _
      (lowerDensityParameter_apply hG hi hν I I' hζ n hn τ) a.symm)

end Parameters

/-! ### The weighted family along a self-twist -/

section Weighted

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine
  cFamilyLeviFiniteType

attribute [local instance]
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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

set_option hygiene false in
local notation "Rup" => productInducedCompactEquiv (leviRationalNormCharacters i ν I)
  (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
  (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
  (continuous_leviRationalNormCharacters i ν I)
  (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
  (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
  (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
set_option hygiene false in
local notation "Pup" => productCompactSelfTwistEquiv νM
set_option hygiene false in
local notation "Plow" => productCompactSelfTwistEquiv (leviNormCharacters χs)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Covariance of the c-family under self-twists** on the fixed compact pictures. -/
theorem cCompactFamily_selfTwist [LocallyCompactSpace (standardParabolicPoints i ν (rootSet i ν I))]
    (A : SmoothRep.{0, u, uV} ℂ 𝐌) (z τ : unramifiedCharacters νM)
    (a : A.representation.Equiv
      (A.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A)
    (hzτ : z * τ ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A)
    (Fc : ProductInducedCompactPicture
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K A) :
    cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z * τ, hzτ⟩
        ((Pup) A (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
          (continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a Fc) =
      (Plow) (SmoothRep.pullback (eₛ).symm A)
        (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
        (DynamicInducedOrbit.leviNormCharacters_continuous χs)
        (DynamicOppositeCanonicalScalar.projection_continuous χs)
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
        (lowerSelfTwist hG hi hν I I' hζ n hn A τ a)
        (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z, hz⟩ Fc) :=
  (congrArg (fun Y => cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A
      ⟨z * τ, hzτ⟩ ((Pup) A (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
        (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
        (continuous_leviRationalNormCharacters i ν I)
        (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a Y))
      (Representation.Equiv.apply_symm_apply (Rup z A) Fc).symm).trans
    ((cCompactFamily_selfTwist_aux hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z τ a hz hzτ
      ((Rup z A).symm Fc)).trans
      (congrArg (fun Y => (Plow) (SmoothRep.pullback (eₛ).symm A)
        (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
        (DynamicInducedOrbit.leviNormCharacters_continuous χs)
        (DynamicOppositeCanonicalScalar.projection_continuous χs)
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
        (lowerSelfTwist hG hi hν I I' hζ n hn A τ a)
        (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z, hz⟩ Y))
        (Representation.Equiv.apply_symm_apply (Rup z A) Fc)))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- `cWeightedCompactFamily` unfolded. -/
theorem cWeightedCompactFamily_apply
    (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)
    (z : unramifiedCharacters νM)
    (hz : z ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)
    (Fc : ProductInducedCompactPicture
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj) :
    cWeightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK hK' hPK' π PG PM hN
        ⟨z, hz⟩ Fc =
      (rationalValueAt (packageDensity PG) hz.2.1 *
          (rationalValueAt (packageDensity PM) hz.2.2.fst)⁻¹) •
        cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' π.obj ⟨z, hz.1⟩ Fc :=
  rfl

/-- The density `µ^G` along a self-twist: regular at `zτ` with the value at `z`. -/
theorem exists_upperDensity_value_mul_eq (z τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ζ ≫ i))
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ hG) (packageDensity PG)
      (standardLeviUnramifiedRestrict hG hi hν I hζ z)) :
    ∃ hzτ : RationalFunctionRegularAt (parameterScheme (CommGroupScheme.groupHom ζ ≫ i))
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
        (parameterScheme_isConnectedReductive _ hG) (packageDensity PG)
        (standardLeviUnramifiedRestrict hG hi hν I hζ (z * τ)),
      rationalValueAt (packageDensity PG) hzτ = rationalValueAt (packageDensity PG) hz := by
  obtain ⟨h₁, heq₁⟩ := exists_packageDensity_value_mul_eq PG
    (standardLeviUnramifiedRestrict_mem_stabilizer hG hi hν I hζ π τ a) hz
  have hrz : standardLeviUnramifiedRestrict hG hi hν I hζ τ *
      standardLeviUnramifiedRestrict hG hi hν I hζ z =
        standardLeviUnramifiedRestrict hG hi hν I hζ (z * τ) := by
    rw [standardLeviUnramifiedRestrict_mul, mul_comm]
  obtain ⟨h₂, heq₂⟩ := exists_rationalValueAt_of_eq hrz h₁
  exact ⟨h₂, heq₂.trans heq₁⟩


set_option maxHeartbeats 400000 in
/-- The density `µ^{M'}` along a self-twist: regular at `s(zτ)` with the value at `sz`. -/
theorem exists_lowerDensity_value_mul_eq (z τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : RationalFunctionRegularAt (parameterScheme χs)
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
      (parameterScheme_isConnectedReductive _ (lowerAmbient_isConnectedReductive hG hi hν I'))
      (packageDensity PM) (lowerDensityParameter hG hi hν I I' hζ n hn z)) :
    ∃ hzτ : RationalFunctionRegularAt (parameterScheme χs)
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous _)
        (parameterScheme_isConnectedReductive _ (lowerAmbient_isConnectedReductive hG hi hν I'))
        (packageDensity PM) (lowerDensityParameter hG hi hν I I' hζ n hn (z * τ)),
      rationalValueAt (packageDensity PM) hzτ = rationalValueAt (packageDensity PM) hz := by
  have hmem := lowerDensityParameter_mem_stabilizer hG hi hν I I' hζ n hn π τ a
  have hrz : lowerDensityParameter hG hi hν I I' hζ n hn τ *
      lowerDensityParameter hG hi hν I I' hζ n hn z =
        lowerDensityParameter hG hi hν I I' hζ n hn (z * τ) := by
    rw [lowerDensityParameter_mul, mul_comm]
  exact exists_packageDensity_value_eq_of_mul_eq PM hmem hrz hz

set_option maxHeartbeats 1600000 in
/-- The domain of the weighted c-family is stable under translation by a self-twist. -/
theorem mul_mem_cWeightedDomain_selfTwist (z τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : z ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM) :
    z * τ ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM := by
  have hzc := hz.1
  have hzG := hz.2.1
  have hzM := hz.2.2.fst
  have hne := hz.2.2.snd
  have hG' := (exists_upperDensity_value_mul_eq hG hi hν I hζ hRefl hCST π PG z τ a hzG).fst
  obtain ⟨hM', heqM⟩ := exists_lowerDensity_value_mul_eq hG hi hν I I' hζ n hn hRefl hCST π PM
    z τ a hzM
  have hne' : rationalValueAt (packageDensity PM) hM' ≠ 0 := by
    rw [heqM]
    exact hne
  have hzc' := mul_mem_cDomain_of_selfTwist hG hi hν I I' hζ hζ' n hn K hK π.obj a hzc
  exact ⟨hzc', hG', hM', hne'⟩


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Covariance of the weighted c-family under self-twists.** For a self-twist
`a : π ≃ π ⊗ τ` and `z`, `zτ` in the domain of `c̃` (both densities are invariant under
translation by `τ`), `c̃(s, π ⊗ zτ) ∘ a = (sa) ∘ c̃(s, π ⊗ z)` on the fixed compact pictures. -/
theorem cWeightedCompactFamily_selfTwist (z τ : unramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : z ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)
    (hzτ : z * τ ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)
    (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)
    (Fc : ProductInducedCompactPicture
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj) :
    cWeightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK hK' hPK' π PG PM hN
        ⟨z * τ, hzτ⟩
        ((Pup) π.obj (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
          (continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a Fc) =
      (Plow) (SmoothRep.pullback (eₛ).symm π.obj)
        (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
        (DynamicInducedOrbit.leviNormCharacters_continuous χs)
        (DynamicOppositeCanonicalScalar.projection_continuous χs)
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
        (lowerSelfTwist hG hi hν I I' hζ n hn π.obj τ a)
        (cWeightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK hK' hPK' π PG PM
          hN ⟨z, hz⟩ Fc) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have hG₁ := exists_upperDensity_value_mul_eq hG hi hν I hζ hRefl hCST π PG z τ a hz.2.1
  have hM₁ := exists_lowerDensity_value_mul_eq hG hi hν I I' hζ n hn hRefl hCST π PM
    z τ a hz.2.2.fst
  have hvG : rationalValueAt (packageDensity PG) hzτ.2.1 =
      rationalValueAt (packageDensity PG) hz.2.1 := hG₁.snd
  have hvM : rationalValueAt (packageDensity PM) hzτ.2.2.fst =
      rationalValueAt (packageDensity PM) hz.2.2.fst := hM₁.snd
  have hc := cCompactFamily_selfTwist hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' π.obj z τ a
    hz.1 hzτ.1 Fc
  have e1 := cWeightedCompactFamily_apply hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK hK' hPK' π
    PG PM hN (z * τ) hzτ
    ((Pup) π.obj (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
      (continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a Fc)
  have e2 := cWeightedCompactFamily_apply hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK hK' hPK' π
    PG PM hN z hz Fc
  have e3 := representationEquiv_smul_apply ((Plow) (SmoothRep.pullback (eₛ).symm π.obj)
      (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
      (DynamicInducedOrbit.leviNormCharacters_continuous χs)
      (DynamicOppositeCanonicalScalar.projection_continuous χs)
      (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
      (lowerSelfTwist hG hi hν I I' hζ n hn π.obj τ a))
    (rationalValueAt (packageDensity PG) hz.2.1 *
      (rationalValueAt (packageDensity PM) hz.2.2.fst)⁻¹)
    (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' π.obj ⟨z, hz.1⟩ Fc)
  have hs : rationalValueAt (packageDensity PG) hzτ.2.1 *
        (rationalValueAt (packageDensity PM) hzτ.2.2.fst)⁻¹ =
      rationalValueAt (packageDensity PG) hz.2.1 *
        (rationalValueAt (packageDensity PM) hz.2.2.fst)⁻¹ :=
    congrArg₂ (fun x y : ℂ => x * y⁻¹) hvG hvM
  have e4 := congrArg (fun Y => (Plow) (SmoothRep.pullback (eₛ).symm π.obj)
      (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
      (DynamicInducedOrbit.leviNormCharacters_continuous χs)
      (DynamicOppositeCanonicalScalar.projection_continuous χs)
      (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
      (lowerSelfTwist hG hi hν I I' hζ n hn π.obj τ a) Y) e2.symm
  have e5 := congrArg₂ (fun (c : ℂ) (Y : ProductInducedCompactPicture (decomposition χs) K'
      (SmoothRep.pullback (eₛ).symm π.obj)) => c • Y) hs hc
  have e6 := e1.trans (e5.trans (e3.trans e4))
  exact e6

end Weighted

end WeakExpansion

end Langlands.HarishChandraSchwartz
