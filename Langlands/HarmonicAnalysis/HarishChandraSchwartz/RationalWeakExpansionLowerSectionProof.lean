import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityInputs
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionWeightedCovariance
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLevelControl
import Langlands.Representation.Plancherel.UnitaryRegularOperatorSections

/-! # Lower sections of the weighted c-family

Proof of `WeightedCLowerSectionStatement` (module `RationalWeakExpansionIdentityInputs`): for a
rational extension `E` of `c̃_{P'|P}(s, ·)` and a section `q ∈ C^∞(O, P)`, the family
`sω ↦ c̃_{P'|P}(s, ω) q_ω` is an actual smooth lower section (Waldspurger, printed p.304).

* `lowerCompactFamily E q` is this family on the fixed lower compact picture, in the circle
  coordinates of `Im X(s·M)`;
* `lowerCompactFamily_mem_finiteSmoothFamilies`: it is a finite smooth family, since the inverse
  Weyl transport of the coordinates is an integer monomial and `E` is a regular operator;
* `lowerCompactFamily_mul_stabilizer`: it is covariant under the unitary stabilizer of `sπ`,
  by the stabilizer covariance of `q` and of the values of `E` (`unitaryValue_mul_selfTwist`);
* `exists_isWeightedCSection` and `weightedCLowerSection`: the corresponding lower section. -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily
open Langlands.Induction Langlands.HarmonicAnalysis.TorusFourier

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] targetsAmbientAffine targetsLeviAffineHom targetsLeviAffine
  targetsLeviFiniteType

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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "eM" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv

/-! ### Self-twists along the Weyl conjugation -/

section Twist

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "conjChar" => lowerCharacterConjugation hG hi hν I I' hζ n hn

/-- The inverse conjugation of unitary characters is `σ ↦ σ ∘ e`. -/
theorem lowerCharacterConjugation_symm_apply
    (σ : unitaryUnramifiedCharacters (leviNormCharacters χs)) (m : 𝐌) :
    ((conjChar).symm σ).val m = σ.val (eₛ m) := by
  obtain ⟨y, rfl⟩ := (conjChar).surjective σ
  rw [ContinuousMulEquiv.symm_apply_apply, lowerCharacterConjugation_apply,
    ContinuousMulEquiv.symm_apply_apply]

/-- The Weyl conjugation of complex unramified characters sends the inclusion of
`lowerCharacterConjugation⁻¹ σ` to the inclusion of `σ`. -/
theorem lowerUnramifiedCharacterConjugation_inclusion_symm
    (σ : unitaryUnramifiedCharacters (leviNormCharacters χs)) :
    lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
        (unitaryUnramifiedInclusion νM ((conjChar).symm σ)) =
      unitaryUnramifiedInclusion (leviNormCharacters χs) σ := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro m'
  have h := lowerCharacterConjugation_symm_apply hG hi hν I I' hζ n hn σ ((eₛ).symm m')
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h

/-- **A self-twist of `sπ` by `σ` is a self-twist of `π` by `τ = σ ∘ e`**, with the same linear
map. -/
def upperSelfTwist (A : SmoothRep.{0, u, uV} ℂ 𝐌) (τ : unramifiedCharacters νM)
    (σ : unramifiedCharacters (leviNormCharacters χs)) (hτ : ∀ m, τ.val m = σ.val (eₛ m))
    (b : (SmoothRep.pullback (eₛ).symm A).representation.Equiv
      ((SmoothRep.pullback (eₛ).symm A).twist σ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χs) σ)).representation) :
    A.representation.Equiv
      (A.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation :=
  Representation.Equiv.mk b.toLinearEquiv (fun m => by
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (b.isIntertwining' (eₛ m)) v
    change b (A.representation ((eₛ).symm (eₛ m)) v) =
      ((σ.val (eₛ m) : ℂˣ) : ℂ) • A.representation ((eₛ).symm (eₛ m)) (b v) at h
    rw [ContinuousMulEquiv.symm_apply_apply, ← hτ] at h
    change b (A.representation m v) = ((τ.val m : ℂˣ) : ℂ) • A.representation m (b v)
    exact h)

/-- **The stabilizer along the Weyl conjugation.** If `σ` stabilizes the class of `sπ`, then
`lowerCharacterConjugation⁻¹ σ = σ ∘ e` stabilizes the class of `π`. -/
theorem lowerCharacterConjugation_symm_mem_stabilizer
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (σ : unitaryClassTwistStabilizer (leviNormCharacters χs)
      (Quotient.mk _ (lowerRepresentation hG hi hν I I' hζ n hn π))) :
    (conjChar).symm σ.val ∈ unitaryClassTwistStabilizer νM (Quotient.mk _ π) := by
  let b := stabilizerRepresentationEquiv (leviNormCharacters χs)
    (lowerRepresentation hG hi hν I I' hζ n hn π)
    (unitaryClassStabilizerInclusion (leviNormCharacters χs)
      (Quotient.mk _ (lowerRepresentation hG hi hν I I' hζ n hn π)) σ)
  let a := upperSelfTwist hG hi hν I I' hζ n hn π.obj
    (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val))
    (unitaryUnramifiedInclusion (leviNormCharacters χs) σ.val)
    (fun m => lowerCharacterConjugation_symm_apply hG hi hν I I' hζ n hn σ.val m) b
  exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso a.symm)⟩

end Twist

/-! ### The lower compact family -/

section Sections

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hL" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "conjChar" => lowerCharacterConjugation hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "cL" => DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs
set_option hygiene false in
local notation "eL" => (DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs).toMulEquiv
set_option hygiene false in
local notation "JL" => Fin (rationalImageRank (parameterScheme χs))
set_option hygiene false in
local notation "JU" => Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "Udecomp" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "Uclosed" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "UpClosed" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "Unorm" => continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "Uproj" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) Udecomp
set_option hygiene false in
local notation "Ufactor" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "UpperPicture" => ProductInducedCompactPicture Udecomp K π.obj
set_option hygiene false in
local notation "KL" => lowerK hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "KLc" => lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "Lfactor" => lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "πL" => lowerRepresentation hG hi hν I I' hζ n hn π
set_option hygiene false in
local notation "Ldecomp" => decomposition χs
set_option hygiene false in
local notation "Lclosed" => radical_isClosed χs
set_option hygiene false in
local notation "LpClosed" => parabolic_isClosed χs
set_option hygiene false in
local notation "Lnorm" => DynamicInducedOrbit.leviNormCharacters_continuous χs
set_option hygiene false in
local notation "Lproj" => projection_continuous χs
set_option hygiene false in
local notation "νL" => leviNormCharacters χs
set_option hygiene false in
local notation "LowerPicture" => ProductInducedCompactPicture Ldecomp KL (πL).obj
set_option hygiene false in
local notation "Extension" => WeightedCExtension hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN

set_option maxHeartbeats 1000000 in
/-- The compact picture of `q` is covariant under the unitary stabilizer of `π`. -/
theorem sectionCompactPicture_mul_stabilizer
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (z : unitaryUnramifiedCharacters νM)
    (τ : unitaryClassTwistStabilizer νM (Quotient.mk _ π)) :
    sectionCompactPicture hG hi hν I hKc hPK π q (z * τ.val) =
      unitaryStabilizerCompactRepresentation νM Udecomp K UpClosed hKc Unorm Uproj π τ
        (sectionCompactPicture hG hi hν I hKc hPK π q z) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have hF : productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm Uproj Uclosed Ufactor
      π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val) ∈
        finiteSmoothEquivariantFamilies JU UpperPicture
          (unitaryStabilizerTorusHom νM eM (Quotient.mk _ π))
          (unitaryStabilizerCompactRepresentation νM Udecomp K UpClosed hKc Unorm Uproj π) :=
    (productInducedSmoothOrbitPullback νM π eM Udecomp Uclosed K UpClosed hKc Unorm Uproj
      Ufactor q).property
  have h := hF.2 τ (eM z)
  have he : eM (z * τ.val) = eM z * unitaryStabilizerTorusHom νM eM (Quotient.mk _ π) τ :=
    map_mul eM z τ.val
  have h2 := (congrArg (fun u => productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm
    Uproj Uclosed Ufactor π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val) u)
    he).trans h
  exact h2

set_option hygiene false in
local notation "Pup" => productCompactSelfTwistEquiv νM π.obj Udecomp K UpClosed hKc Unorm Uproj
set_option hygiene false in
local notation "Plow" => productCompactSelfTwistEquiv νL (SmoothRep.pullback (eₛ).symm π.obj)
  Ldecomp KL LpClosed KLc Lnorm Lproj

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Covariance of the unitary values of a rational extension.** For unitary `z`, `τ` and a
self-twist `a : π ≃ π ⊗ τ`, `c̃(s, π ⊗ zτ) ∘ a = (sa) ∘ c̃(s, π ⊗ z)` for the values of any
rational extension `E`: the covariance on the interior of `cWeightedDomain` extends to the
polynomial numerator by the identity theorem. -/
theorem unitaryValue_mul_selfTwist (E : Extension) (z τ : unitaryUnramifiedCharacters νM)
    (a : π.obj.representation.Equiv
      (π.obj.twist (unitaryUnramifiedInclusion νM τ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (unitaryUnramifiedInclusion νM τ))).representation)
    (X : UpperPicture) :
    E.unitaryValue (z * τ) (Pup (unitaryUnramifiedInclusion νM τ) a X) =
      Plow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
          (unitaryUnramifiedInclusion νM τ))
        (lowerSelfTwist hG hi hν I I' hζ n hn π.obj (unitaryUnramifiedInclusion νM τ) a)
        (E.unitaryValue z X) := by
  have hId : ∀ f : unramifiedCharacters νM → ProductInducedCompactPicture Ldecomp KL
      (SmoothRep.pullback (eₛ).symm π.obj),
      UnramifiedOperatorFamily.IsPolynomialOn Set.univ (fun χ => f χ.val) →
      ∀ {D : Set (unramifiedCharacters νM)}, IsOpen D → D.Nonempty → (∀ χ ∈ D, f χ = 0) →
        ∀ χ, f χ = 0 :=
    fun f hf D hD hne hz χ => leviPolynomial_eq_zero_of_isOpen I
      (lowerAmbient_isConnectedReductive hG hi hν I) f hf hD hne hz χ
  have hτD : ∀ w ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM,
      w * unitaryUnramifiedInclusion νM τ ∈
        cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM :=
    fun w hw => mul_mem_cWeightedDomain_selfTwist hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π
      PG PM w _ a hw
  have hint : ∀ w ∈ interior (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM),
      w * unitaryUnramifiedInclusion νM τ ∈
        interior (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM) :=
    fun w hw => mul_mem_interior_of_forall_mul_mem _ hτD hw
  have hcov : ∀ w (hw : w ∈ cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM)
      (hwτ : w * unitaryUnramifiedInclusion νM τ ∈
        cWeightedDomain hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST π PG PM) (Y : UpperPicture),
      weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN
          ⟨w * unitaryUnramifiedInclusion νM τ, hwτ⟩
          ((Pup (unitaryUnramifiedInclusion νM τ) a).toLinearMap Y) =
        (Plow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
            (unitaryUnramifiedInclusion νM τ))
          (lowerSelfTwist hG hi hν I I' hζ n hn π.obj (unitaryUnramifiedInclusion νM τ) a)).toLinearMap
          (weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN
            ⟨w, hw⟩ Y) :=
    fun w hw hwτ Y => cWeightedCompactFamily_selfTwist hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST
      hPK KLc Lfactor π PG PM w _ a hw hwτ hN Y
  have h := regular_inv_smul_mul_eq_of_isOpen hId E.interior_nonempty E.denominator E.numerator
    E.polynomial
    (fun w => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN w)
    E.clears (unitaryUnramifiedInclusion νM τ) hint
    (Pup (unitaryUnramifiedInclusion νM τ) a).toLinearMap
    (Plow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
        (unitaryUnramifiedInclusion νM τ))
      (lowerSelfTwist hG hi hν I I' hζ n hn π.obj (unitaryUnramifiedInclusion νM τ) a)).toLinearMap
    hcov X ⟨z.val, z.property.1⟩ (E.unitary_regular z) (E.unitary_regular (z * τ))
  exact h

/-- The lower self-twist operator of `a : π ≃ π ⊗ σ ∘ e` is the stabilizer operator of `σ` on the
lower compact picture (Schur). -/
theorem lowerSelfTwist_eq_stabilizer
    (σ : unitaryClassTwistStabilizer νL (Quotient.mk _ (πL)))
    (a : π.obj.representation.Equiv
      (π.obj.twist (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM
          (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val)))).representation)
    (Y : LowerPicture) :
    Plow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
        (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val)))
      (lowerSelfTwist hG hi hν I I' hζ n hn π.obj
        (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val)) a) Y =
      unitaryStabilizerCompactRepresentation νL Ldecomp KL LpClosed KLc Lnorm Lproj πL σ Y := by
  have h := productCompactSelfTwistEquiv_eq_of_eq νL (SmoothRep.pullback (eₛ).symm π.obj) Ldecomp
    KL LpClosed KLc Lnorm Lproj (πL).property.2 (πL).property.1
    (lowerUnramifiedCharacterConjugation_inclusion_symm hG hi hν I I' hζ n hn σ.val)
    (lowerSelfTwist hG hi hν I I' hζ n hn π.obj
      (unitaryUnramifiedInclusion νM ((conjChar).symm σ.val)) a)
    (stabilizerRepresentationEquiv νL πL
      (unitaryClassStabilizerInclusion νL (Quotient.mk _ (πL)) σ))
  exact DFunLike.congr_fun h Y

/-- **The lower compact family** `w ↦ c̃(s, π ⊗ z) q_z`, `z = s⁻¹ w`, in the circle coordinates
`w` of `Im X(s·M)`. -/
def lowerCompactFamily (E : Extension)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (w : JL → Circle) :
    LowerPicture :=
  E.unitaryValue ((conjChar).symm ((cL).symm w))
    (sectionCompactPicture hG hi hν I hKc hPK π q ((conjChar).symm ((cL).symm w)))

set_option maxHeartbeats 1600000 in
/-- The lower compact family is a finite smooth family. -/
theorem lowerCompactFamily_mem_finiteSmoothFamilies (E : Extension)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q ∈
      finiteSmoothFamilies JL LowerPicture := by
  obtain ⟨a, ha⟩ := exists_monomial_lowerCharacterConjugation_symm hG hi hν I I' hζ n hn
  have hR : productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm Uproj Uclosed Ufactor
      π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val) ∈
        finiteSmoothFamilies JU UpperPicture :=
    Submodule.mem_comap.mp (Submodule.mem_inf.mp q.property).2
  have hfam : lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q =
      fun w => unitaryRegularOperator νM eM E.denominator E.numerator (finiteTorusMonomial a w)
        (productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm Uproj Uclosed Ufactor
          π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val)
          (finiteTorusMonomial a w)) := by
    funext w
    have hmono : eM ((conjChar).symm ((cL).symm w)) = finiteTorusMonomial a w := ha w
    have hright : unitaryRegularOperator νM eM E.denominator E.numerator
        (eM ((conjChar).symm ((cL).symm w)))
        (productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm Uproj Uclosed Ufactor
          π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val)
          (eM ((conjChar).symm ((cL).symm w)))) =
        lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q w := by
      simp only [unitaryRegularOperator, MulEquiv.symm_apply_apply]
      rfl
    exact hright.symm.trans (congrArg (fun y => unitaryRegularOperator νM eM E.denominator
      E.numerator y (productInducedFamilyRestriction νM eM Udecomp K UpClosed hKc Unorm Uproj
        Uclosed Ufactor π.obj (productInducedOrbitPullback νM π eM Udecomp Uclosed q.val) y))
      hmono)
  rw [hfam]
  exact unitaryRegularOperator_comp_monomial_mem_finiteSmoothFamilies νM eM
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I) E.denominator
    (fun u => E.unitary_regular ((eM).symm u)) E.numerator E.polynomial hR a

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The lower compact family is covariant under the unitary stabilizer of `sπ`. -/
theorem lowerCompactFamily_mul_stabilizer (E : Extension)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (σ : unitaryClassTwistStabilizer νL (Quotient.mk _ (πL))) (w : JL → Circle) :
    lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q
        (w * unitaryStabilizerTorusHom νL eL (Quotient.mk _ (πL)) σ) =
      unitaryStabilizerCompactRepresentation νL Ldecomp KL LpClosed KLc Lnorm Lproj πL σ
        (lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q w) := by
  let τ : unitaryClassTwistStabilizer νM (Quotient.mk _ π) :=
    ⟨(conjChar).symm σ.val, lowerCharacterConjugation_symm_mem_stabilizer hG hi hν I I' hζ n hn π σ⟩
  have hz : (conjChar).symm ((cL).symm (w * unitaryStabilizerTorusHom νL eL (Quotient.mk _ (πL)) σ)) =
      (conjChar).symm ((cL).symm w) * τ.val := by
    change (conjChar).symm ((cL).symm (w * cL σ.val)) =
      (conjChar).symm ((cL).symm w) * (conjChar).symm σ.val
    rw [map_mul, ContinuousMulEquiv.symm_apply_apply, map_mul]
  let a := stabilizerRepresentationEquiv νM π
    (unitaryClassStabilizerInclusion νM (Quotient.mk _ π) τ)
  have h1 := congrArg (fun y => E.unitaryValue y (sectionCompactPicture hG hi hν I hKc hPK π q y)) hz
  have h2 := congrArg (E.unitaryValue ((conjChar).symm ((cL).symm w) * τ.val))
    (sectionCompactPicture_mul_stabilizer hG hi hν I hKc hPK π q ((conjChar).symm ((cL).symm w)) τ)
  have h3 := unitaryValue_mul_selfTwist hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E
    ((conjChar).symm ((cL).symm w)) τ.val a
    (sectionCompactPicture hG hi hν I hKc hPK π q ((conjChar).symm ((cL).symm w)))
  have h4 := lowerSelfTwist_eq_stabilizer hG hi hν I I' hζ π n hn hRefl hCST PM σ a
    (E.unitaryValue ((conjChar).symm ((cL).symm w))
      (sectionCompactPicture hG hi hν I hKc hPK π q ((conjChar).symm ((cL).symm w))))
  exact h1.trans (h2.trans (h3.trans h4))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Every rational extension has a lower section.** For a rational extension `E` of
`c̃_{P'|P}(s, ·)` and a section `q ∈ C^∞(O, P)`, there is a lower smooth section
`Ψ ∈ C^∞(sO, M' ∩ s·P)` with `IsWeightedCSection E q Ψ`. -/
theorem exists_isWeightedCSection (E : Extension)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ Ψ : LowerSectionsAt hG hi hν I I' hζ π n hn hRefl hCST PM,
      IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q Ψ := by
  obtain ⟨Ψ, hΨ⟩ := exists_productInducedSmoothOrbitSection νL πL eL Ldecomp Lclosed KL LpClosed
    KLc Lnorm Lproj Lfactor
    (lowerCompactFamily hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q)
    (lowerCompactFamily_mem_finiteSmoothFamilies hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG
      PM hN E q)
    (lowerCompactFamily_mul_stabilizer hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN E q)
  refine ⟨Ψ, fun z => ?_⟩
  have h := congrFun hΨ (cL (conjChar z))
  have hzz : (conjChar).symm ((cL).symm (cL (conjChar z))) = z := by
    rw [ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply]
  have h' := congrArg (fun y => E.unitaryValue y (sectionCompactPicture hG hi hν I hKc hPK π q y))
    hzz
  have h'' := h.trans h'
  have hd : dynamicSectionCompactPicture (H := 𝐋) hL χs KLc Lfactor πL Ψ (cL (conjChar z)) =
      productInducedFamilyRestriction νL eL Ldecomp KL LpClosed KLc Lnorm Lproj Lclosed Lfactor
        (πL).obj (productInducedOrbitPullback νL πL eL Ldecomp Lclosed Ψ.val) (cL (conjChar z)) :=
    rfl
  exact hd.trans h''

end Sections

/-! ### The lower-section statement -/

section Statement

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

/-- **Lower sections of the weighted c-family** (`WeightedCLowerSectionStatement`): for every
Weyl index `s`, every rational extension `E` of `c̃_{P'|P}(s, ·)` and every section `q`, the
lower section `sω ↦ c̃_{P'|P}(s, ω) q_ω` exists. -/
theorem weightedCLowerSection [BorelSpace (𝐌 ⧸ CM)] :
    WeightedCLowerSectionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST PG R PM := by
  intro _ _ _ hN s E q
  exact exists_isWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π (R.normalizer s) (R.levi_le s)
    hRefl hCST PG (PM s) (hN s) E q

end Statement

end WeakExpansion

end Langlands.HarishChandraSchwartz
