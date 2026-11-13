import Langlands.Weil.Representation.RestrictionDual
import Langlands.Global.Factors.RelativeWeilAssemblyGlobal
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Global.Factors.RelativeWeilFunctionalEquationStatement
import Langlands.ClassField.Global.LocalRelativeWeilTransferStatement
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricStatement
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.RankOneEpsilonFieldTransport
import Langlands.LocalFactor.NonabelianDualityReduction

/-!
# Finite-place factors of twisted relative Weil pairs as Hecke factors
-/

noncomputable section

set_option autoImplicit false

universe u uV uE uG uH uA uB

namespace Langlands.FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- The restriction of a twisted tensor product `χ ⊗ (A ⊗ B)` is the tensor product of the
restricted twist of `A` with the restriction of `B`; the underlying map is the identity. -/
def restrictTwistTensorEquiv (φ : H →* G) (χ : G →* ℂˣ)
    (A : FiniteRepresentation.{0, uG, uA} ℂ G) (B : FiniteRepresentation.{0, uG, uB} ℂ G) :
    Equiv (restrict φ (twist χ (tensor A B)))
      (tensor (restrict φ (twist χ A)) (restrict φ B)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    refine LinearMap.ext (fun v => ?_)
    change (χ (φ g) : ℂ) • TensorProduct.map (A.representation (φ g)) (B.representation (φ g)) v =
      TensorProduct.map ((χ (φ g) : ℂ) • A.representation (φ g)) (B.representation (φ g)) v
    rw [TensorProduct.map_smul_left]
    rfl

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.PadicAbelian

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

/-- A self-dual Haar measure for a realization equal to the canonical one, transported along
the equality of topologies, is self-dual for every canonical-topology additive character with
the same underlying additive character. -/
theorem isSelfDualMeasure_haarMeasureCongr {T : F.TopologicalData}
    (hT : T = F.canonicalTopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (μ : SelfDualHaar T ψ) (ψ' : Correspondence.NontrivialAdditiveCharacter F)
    (hψ : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _
        F.canonicalTopologicalData.topology ψ' =
      @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _ T.topology ψ) :
    Correspondence.IsSelfDualMeasure F ψ'
      (haarMeasureCongr (congrArg PadicField.TopologicalData.topology hT) μ.val) := by
  subst hT
  obtain ⟨ψ₀, _, _⟩ := ψ'
  subst hψ
  exact μ.2

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.Global.CompletionPadic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open LocalFactor

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- A character of `K_vˣ`, continuous for the completion topology, as a quasicharacter of the
canonical package `padicField v`. The underlying homomorphism is unchanged. -/
def quasicharacterBase (χ : (v.adicCompletion K)ˣ →ₜ* ℂˣ) :
    Correspondence.QuasiCharacter (padicField v) :=
  PadicAbelian.quasicharacterCongr
    (congrArg PadicField.TopologicalData.topology (topologicalData_eq_canonicalTopologicalData v))
    χ

/-- Tate's L-factor of `χ` for the completion realization of `K_v` is Tate's L-factor of the
transported quasicharacter for the canonical package. -/
theorem lFactor_quasicharacterBase (χ : (v.adicCompletion K)ˣ →ₜ* ℂˣ) (s : ℂ) :
    PadicAbelian.lFactor (padicField v).canonicalTopologicalData (quasicharacterBase v χ) s =
      PadicAbelian.lFactor (topologicalData v) χ s :=
  PadicAbelian.lFactor_quasicharacterCongr (topologicalData_eq_canonicalTopologicalData v) χ s

/-- The form of `lFactor_quasicharacterBase` for the inverse quasicharacter. -/
theorem lFactor_inv_quasicharacterBase (χ : (v.adicCompletion K)ˣ →ₜ* ℂˣ) (s : ℂ) :
    PadicAbelian.lFactor (padicField v).canonicalTopologicalData (quasicharacterBase v χ)⁻¹ s =
      PadicAbelian.lFactor (topologicalData v) χ⁻¹ s :=
  lFactor_quasicharacterBase v χ⁻¹ s

/-- The form of `lFactor_quasicharacterAt` for the inverse quasicharacter. -/
theorem lFactor_inv_quasicharacterAt {p : ℕ} [Fact p.Prime] (h : residuePrime v = p)
    (χ : (v.adicCompletion K)ˣ →ₜ* ℂˣ) (s : ℂ) :
    PadicAbelian.lFactor (padicFieldAt v h).canonicalTopologicalData (quasicharacterAt v h χ)⁻¹ s =
      PadicAbelian.lFactor (topologicalData v) χ⁻¹ s :=
  lFactor_quasicharacterAt v h χ⁻¹ s

end Langlands.Global.CompletionPadic

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-- Local maps `W_{F_z} → W_{E/F}` continuous for the Krull topology on `Gal(E/F)`, the
topology of `IsLocalRelativeWeilMap`. The name fixes this topology in sections where the
discrete topology is a local instance. -/
abbrev KrullLocalMap (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (z : Langlands.Global.FinitePlace F) :=
  Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E

/-- `localPairClass` at a local map continuous for the Krull topology on `Gal(E/F)`. The
name fixes this topology in sections where the discrete topology is a local instance. -/
abbrev krullLocalPairClass {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {z : Langlands.Global.FinitePlace F}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : KrullLocalMap c F E z) : Correspondence.LocalPairClass.{u, uV} (padicField z) :=
  localPairClass S ι

attribute [local instance] relativeGaloisTopology

variable {c : FundamentalClass.ClassFamily.{u}}

section Characters

variable {K E : Type u} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [IsGalois K E]

/-- A reciprocity character `l ∘ τ_K` composed with a local map whose transfer is inverse
local reciprocity `e` at the finite place `v` is the Weil character of the component of `l`
at `v` along `e`. -/
theorem continuousReciprocityCharacter_comp_eq_weilCharacter (l : HeckeCharacter K)
    (v : Langlands.Global.FinitePlace K) {p : ℕ} [Fact p.Prime] (hv : residuePrime v = p)
    (e : LocalFactor.RankOne.ReciprocityCandidate (padicFieldAt v hv))
    (φ : Weil.Local.localWeilGroup (padicFieldAt v hv) →ₜ* RelativeWeilGroup c K E)
    (hφ : ∀ y, transfer c K E (φ y) = (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v
      (LocalFactor.RankOne.reciprocityUnits (padicFieldAt v hv) e y))⁻¹) :
    (continuousReciprocityCharacter c K E l).comp φ =
      LocalFactor.RankOne.weilCharacter (padicFieldAt v hv) e
        (quasicharacterAt v hv (l.finiteComponent v)) := by
  ext y
  rw [ContinuousMonoidHom.comp_toFun,
    continuousReciprocityCharacter_apply_of_transfer_eq l φ _ hφ y,
    LocalFactor.RankOne.weilCharacter_apply]
  rfl

/-- The base form of `continuousReciprocityCharacter_comp_eq_weilCharacter`, for the
canonical package `padicField v`. -/
theorem continuousReciprocityCharacter_comp_eq_weilCharacter_base (l : HeckeCharacter K)
    (v : Langlands.Global.FinitePlace K)
    (e : LocalFactor.RankOne.ReciprocityCandidate (padicField v))
    (φ : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c K E)
    (hφ : ∀ y, transfer c K E (φ y) = (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v
      (LocalFactor.RankOne.reciprocityUnits (padicField v) e y))⁻¹) :
    (continuousReciprocityCharacter c K E l).comp φ =
      LocalFactor.RankOne.weilCharacter (padicField v) e
        (quasicharacterBase v (l.finiteComponent v)) := by
  ext y
  rw [ContinuousMonoidHom.comp_toFun,
    continuousReciprocityCharacter_apply_of_transfer_eq l φ _ hφ y,
    LocalFactor.RankOne.weilCharacter_apply]
  rfl

end Characters

section Components

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- At the base place: along a local map `ι` for a place `w` of `E` above `z`, the
reciprocity character `l ∘ τ_F` is the Weil character of the component `l_z` along the base
candidate of a normalized family `eC` of `F_z`. Uses the local transfer reciprocity (N3) and
the geometricity of the base candidate. -/
theorem continuousReciprocityCharacter_comp_discreteLocalMap
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (l : HeckeCharacter F) {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC) :
    (continuousReciprocityCharacter c F E l).comp (discreteLocalMap ι) =
      LocalFactor.RankOne.weilCharacter (padicField z)
        (Correspondence.baseReciprocityCandidate (padicField z) eC)
        (quasicharacterBase z (l.finiteComponent z)) :=
  continuousReciprocityCharacter_comp_eq_weilCharacter_base l z _ (discreteLocalMap ι)
    (hN3 c F E z w.1 e ι hι _
      ((hgeo _ _ eC heC).1 _ (Correspondence.baseReciprocityCandidate_spec _ eC)))

/-- At a place `u` above `z` of an intermediate field `K`: along a local map whose transfer
is inverse geometric reciprocity of `K_u`, the character `(χ ∘ τ_F)|_{W_{E/K}} · (θ ∘ τ_K)`
is the Weil character of the component of `(χ ∘ N_{K/F}) θ` at `u`, along the transported
candidate of a normalized family `eC` of `F_z`. Uses the transfer-norm compatibility (N4)
and the geometricity of the transported candidate. -/
theorem continuousReciprocityCharacter_tower_comp_eq_weilCharacter
    (h : FundamentalClass.Restriction c)
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (K : IntermediateField F E) (θh : HeckeCharacter K)
    {z : Langlands.Global.FinitePlace F} (u : FinitePlacesAbove K z)
    (φ : Weil.Local.localWeilGroup (towerPadicField z u.1) →ₜ* RelativeWeilGroup c K E)
    (hφ : ∀ eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z u.1),
      LocalClassField.GeometricWeilReciprocityRelation (towerPadicField z u.1)
          (towerPadicField z u.1).canonicalTopologicalData eu →
        ∀ y, transfer c K E (φ y) =
          (IdeleClassGroup.ofAdicCompletion (𝓞 K) K u.1
            (LocalFactor.RankOne.reciprocityUnits (towerPadicField z u.1) eu y))⁻¹)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC) :
    ((continuousReciprocityCharacter c F E χ).comp (restrictionInclusion c F E K h) *
        continuousReciprocityCharacter c K E θh).comp φ =
      LocalFactor.RankOne.weilCharacter (towerPadicField z u.1)
        (LocalClassField.extensionReciprocityCandidate (padicField z) (towerPadicField z u.1)
          (completionPadicAlgHom z u.1) eC)
        (quasicharacterAt u.1 (residuePrime_eq z u.1)
          ((HeckeCharacter.normComp χ * θh).finiteComponent u.1)) := by
  rw [continuousReciprocityCharacter_comp_restrictionInclusion K h (hN4 c F K E h) χ,
    ← continuousReciprocityCharacter_mul]
  exact continuousReciprocityCharacter_comp_eq_weilCharacter (HeckeCharacter.normComp χ * θh)
    u.1 (residuePrime_eq z u.1) _ φ (hφ _ ((hgeo _ _ eC heC).2 _ _))

end Components

section Identity

open Langlands.VirtualRepresentation

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- The restriction to `W_{F_z}` of a twisted degree-zero decomposition, written with Weil
characters of Hecke components: if `η ⊗ x = deg x · [η] + Σ_i r_i Ind_{W_{E/K_i}}
([η θ_i] - [η θ'_i])` for every continuous `η`, with `θ_i = θh_i ∘ τ_{K_i}`, then the
restriction of `(χ ∘ τ_F) ⊗ x` along a local map `ι` is
`deg x · [χ_z ∘ rec] + Σ_{(i, u)} r_i Ind_{W_{K_{i,u}}}^{W_{F_z}}
([λ_{i,u} ∘ rec] - [λ'_{i,u} ∘ rec])`, with `λ_i = (χ ∘ N_{K_i/F}) θh_i`, the sum over the
places `u` of `K_i` above `z`, and the reciprocity candidates of a normalized family of
`F_z`. -/
theorem continuousRestrict_continuousTwist_eq_weilCharacter
    (h : FundamentalClass.Restriction c)
    (hN2 : LocalInducedRestrictionStatement.{max u uV, u})
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (x : ContinuousVirtual.{u, uV} c F E)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ)
    (hdec : ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.continuousTwist η x =
        ExactGrothendieckGroup.degree _ x •
            ExactGrothendieckGroup.characterClass.{u, max u uV} η +
          ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
            (restrictionInclusion c F E (K i) h)
            (isOpenEmbedding_restrictionInclusion c F E (K i) h)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ' i)))
    (θh θh' : ∀ i, HeckeCharacter (K i))
    (hθh : ∀ i, θ i = continuousReciprocityCharacter c (K i) E (θh i))
    (hθh' : ∀ i, θ' i = continuousReciprocityCharacter c (K i) E (θh' i))
    {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC) :
    ExactGrothendieckGroup.continuousRestrict (discreteLocalMap ι)
        (ExactGrothendieckGroup.continuousTwist (continuousReciprocityCharacter c F E χ) x) =
      ExactGrothendieckGroup.degree _ x •
          ExactGrothendieckGroup.characterClass.{u, max u uV}
            (LocalFactor.RankOne.weilCharacter (padicField z)
              (Correspondence.baseReciprocityCandidate (padicField z) eC)
              (quasicharacterBase z (χ.finiteComponent z))) +
        ∑ j : (Σ i, FinitePlacesAbove (K i) z), r j.1 •
          ExactGrothendieckGroup.continuousInduceAlong
            (Weil.Local.extensionWeilMap (padicField z) (towerPadicField z j.2.1)
              (completionPadicAlgHom z j.2.1))
            (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                  (LocalClassField.extensionReciprocityCandidate (padicField z)
                    (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                  (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                    ((HeckeCharacter.normComp χ * θh j.1).finiteComponent j.2.1))) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                  (LocalClassField.extensionReciprocityCandidate (padicField z)
                    (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                  (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                    ((HeckeCharacter.normComp χ * θh' j.1).finiteComponent j.2.1)))) := by
  have hloc : ∀ i, LocalInducedRestriction.{max u uV, u} c F (K i) E h z
      (discreteLocalMap ι) :=
    fun i => hN2 c F (K i) E h z w.1 e ι hι
  obtain ⟨ιu, hτ, hres⟩ := exists_continuousRestrict_decomposition c F E h
    (discreteLocalMap ι) K hloc
  refine ((congrArg (ExactGrothendieckGroup.continuousRestrict (discreteLocalMap ι))
    (hdec (continuousReciprocityCharacter c F E χ))).trans
      (hres _ r _ (fun i => (continuousReciprocityCharacter c F E χ).comp
          (restrictionInclusion c F E (K i) h) * θ i)
        (fun i => (continuousReciprocityCharacter c F E χ).comp
          (restrictionInclusion c F E (K i) h) * θ' i))).trans ?_
  rw [Fintype.sum_sigma]
  have h0 := continuousReciprocityCharacter_comp_discreteLocalMap hN3 hgeo χ w e ι hι eC heC
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i _ => ?_)
  · exact congrArg (fun a => _ • ExactGrothendieckGroup.characterClass.{u, max u uV} a) h0
  refine Finset.smul_sum.trans (Finset.sum_congr rfl fun u _ => congrArg (r i • ·) ?_)
  have h1 := continuousReciprocityCharacter_tower_comp_eq_weilCharacter h hN4 hgeo χ (K i)
    (θh i) u (ιu i u) (hτ i u) eC heC
  have h2 := continuousReciprocityCharacter_tower_comp_eq_weilCharacter h hN4 hgeo χ (K i)
    (θh' i) u (ιu i u) (hτ i u) eC heC
  rw [← hθh i] at h1
  rw [← hθh' i] at h2
  exact congrArg₂ (fun a b => ExactGrothendieckGroup.continuousInduceAlong
    (completionWeilMap z u.1) (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
    (ExactGrothendieckGroup.characterClass.{u, max u uV} a -
      ExactGrothendieckGroup.characterClass.{u, max u uV} b)) h1 h2

/-- The restricted twist of the class of an actual continuous representation is the class of
the restricted twisted representation. -/
theorem continuousRestrict_continuousTwist_ofRepresentation (χ : HeckeCharacter F)
    (X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E))
    (hX : X.IsContinuous) {z : Langlands.Global.FinitePlace F} (ι : KrullLocalMap c F E z) :
    ExactGrothendieckGroup.continuousRestrict (discreteLocalMap ι)
        (ExactGrothendieckGroup.continuousTwist (continuousReciprocityCharacter c F E χ)
          (ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩)) =
      ExactGrothendieckGroup.ofRepresentation _
        ⟨FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
            (FiniteRepresentation.twist (continuousReciprocityCharacter c F E χ).toMonoidHom X),
          FiniteRepresentation.isContinuous_restrict _ (discreteLocalMap ι).continuous
            (FiniteRepresentation.isContinuous_twist _ hX)⟩ :=
  (congrArg (ExactGrothendieckGroup.continuousRestrict (discreteLocalMap ι))
    (ExactGrothendieckGroup.continuousTwist_ofRepresentation _ _)).trans
    (ExactGrothendieckGroup.restrict_ofRepresentation _ _ _ _ _)

end Identity

section LFactor

open Langlands.VirtualRepresentation
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- The inverse-component form of `lFactor_quasicharacterBase`, as the Hecke L-factor of the
inverse character. -/
theorem lFactor_inv_quasicharacterBase_eq_heckeL {K : Type u} [Field K] [NumberField K]
    (l : HeckeCharacter K) (v : Langlands.Global.FinitePlace K) (s : ℂ) :
    LocalFactor.PadicAbelian.lFactor (padicField v).canonicalTopologicalData
        (quasicharacterBase v (l.finiteComponent v))⁻¹ s = heckeL l⁻¹ v s :=
  lFactor_inv_quasicharacterBase v (l.finiteComponent v) s

/-- The inverse-component form of `lFactor_quasicharacterAt`, as the Hecke L-factor of the
inverse character. -/
theorem lFactor_inv_quasicharacterAt_eq_heckeL {K : Type u} [Field K] [NumberField K]
    (l : HeckeCharacter K) (v : Langlands.Global.FinitePlace K) {p : ℕ} [Fact p.Prime]
    (h : residuePrime v = p) (s : ℂ) :
    LocalFactor.PadicAbelian.lFactor (padicFieldAt v h).canonicalTopologicalData
        (quasicharacterAt v h (l.finiteComponent v))⁻¹ s = heckeL l⁻¹ v s :=
  lFactor_inv_quasicharacterAt v h (l.finiteComponent v) s

omit [IsGalois F E] in
/-- The product over the places `u` of `K` above `z` of the Tate L-factors of the canonical
packages `K_u` is the product over `placesAbove K z` of the Hecke L-factors. -/
theorem prod_lFactor_quasicharacterAt_eq_prod_heckeL (K : IntermediateField F E)
    (l : HeckeCharacter K) (z : Langlands.Global.FinitePlace F) (s : ℂ) :
    ∏ q : FinitePlacesAbove K z,
        LocalFactor.PadicAbelian.lFactor (towerPadicField z q.1).canonicalTopologicalData
          (quasicharacterAt q.1 (residuePrime_eq z q.1) (l.finiteComponent q.1)) s =
      ∏ u ∈ placesAbove K z, heckeL l u s := by
  rw [placesAbove, Finset.prod_map]
  exact Finset.prod_congr rfl fun q _ => lFactor_quasicharacterAt _ _ _ s

omit [IsGalois F E] in
/-- The form of `prod_lFactor_quasicharacterAt_eq_prod_heckeL` with inverse components. -/
theorem prod_lFactor_inv_quasicharacterAt_eq_prod_heckeL (K : IntermediateField F E)
    (l : HeckeCharacter K) (z : Langlands.Global.FinitePlace F) (s : ℂ) :
    ∏ q : FinitePlacesAbove K z,
        LocalFactor.PadicAbelian.lFactor (towerPadicField z q.1).canonicalTopologicalData
          (quasicharacterAt q.1 (residuePrime_eq z q.1) (l.finiteComponent q.1))⁻¹ s =
      ∏ u ∈ placesAbove K z, heckeL l⁻¹ u s :=
  prod_lFactor_quasicharacterAt_eq_prod_heckeL K l⁻¹ z s

/-- Finite-place L-factors of twisted relative Weil pairs: for `x = [X]` with `X ≃ S ⊗ S'`
and a twisted degree-zero decomposition of `x`, the arithmetic pair L-factor of
`((χ ∘ τ_F) ⊗ S, S')` along a local map `ι` at `z`, evaluated at `q_z^{-s}`, is
`L(s, χ_z)^{deg x} Π_i (Π_{u | z} L(s, λ_{i,u}) / Π_{u | z} L(s, λ'_{i,u}))^{r_i}` with
`λ_i = (χ ∘ N_{K_i/F}) θh_i`, wherever these Hecke L-factors are nonzero. -/
theorem eval_arithmeticPairLFactor_eq_heckeL
    (h : FundamentalClass.Restriction c)
    (hN2 : LocalInducedRestrictionStatement.{max u uV, u})
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E))
    (hX : X.IsContinuous) (eX : FiniteRepresentation.Equiv X (FiniteRepresentation.tensor S S'))
    (x : ContinuousVirtual.{u, uV} c F E) (hx : x = ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ)
    (hdec : ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.continuousTwist η x =
        ExactGrothendieckGroup.degree _ x •
            ExactGrothendieckGroup.characterClass.{u, max u uV} η +
          ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
            (restrictionInclusion c F E (K i) h)
            (isOpenEmbedding_restrictionInclusion c F E (K i) h)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ' i)))
    (θh θh' : ∀ i, HeckeCharacter (K i))
    (hθh : ∀ i, θ i = continuousReciprocityCharacter c (K i) E (θh i))
    (hθh' : ∀ i, θ' i = continuousReciprocityCharacter c (K i) E (θh' i))
    {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (s : ℂ) (hs₀ : heckeL χ z s ≠ 0)
    (hs : ∀ i, ∀ u ∈ placesAbove (K i) z,
      heckeL (HeckeCharacter.normComp χ * θh i) u s ≠ 0 ∧
        heckeL (HeckeCharacter.normComp χ * θh' i) u s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (padicField z).canonicalTopologicalData.residueCardinality s)
        (Correspondence.arithmeticPairLFactor (padicField z)
          (krullLocalPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
          (krullLocalPairClass S' ι)) =
      heckeL χ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i) u s)⁻¹) ^
            r i := by
  have hstep := continuousRestrict_continuousTwist_eq_weilCharacter h hN2 hN3 hN4 hgeo χ x r K
    θ θ' hdec θh θh' hθh hθh' w e ι hι eC heC
  subst hx
  have hid := (continuousRestrict_continuousTwist_ofRepresentation χ X hX ι).symm.trans hstep
  have hgeoz := hgeo _ _ eC heC
  have hmem : ∀ j : (Σ i, FinitePlacesAbove (K i) z), j.2.1 ∈ placesAbove (K j.1) z :=
    fun j => Finset.mem_map_of_mem _ (Finset.mem_univ j.2)
  let eT : FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
        (FiniteRepresentation.twist (continuousReciprocityCharacter c F E χ).toMonoidHom X))
      (FiniteRepresentation.tensor
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
          (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S))
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom S')) :=
    (FiniteRepresentation.restrictEquivOfEquiv _
      (FiniteRepresentation.twistEquiv _ eX)).trans
      (FiniteRepresentation.restrictTwistTensorEquiv _ _ S S')
  refine (Weil.Local.InertiaEuler.eval_arithmeticPairLFactor_eq_virtualLValue (padicField z)
    _ _ _ _ eT (fun j : (Σ i, FinitePlacesAbove (K i) z) => towerPadicField z j.2.1)
    (fun j => completionPadicAlgHom z j.2.1)
    (hgeoz.1 _ (Correspondence.baseReciprocityCandidate_spec _ eC)) (fun j => hgeoz.2 _ _)
    _ _ _ _ (fun j => r j.1) hid s
    ((lFactor_quasicharacterBase z _ s).trans_ne hs₀)
    (fun j => (lFactor_quasicharacterAt _ _ _ s).trans_ne (hs j.1 j.2.1 (hmem j)).1)
    (fun j => (lFactor_quasicharacterAt _ _ _ s).trans_ne (hs j.1 j.2.1 (hmem j)).2)).trans ?_
  rw [Weil.Local.InertiaEuler.virtualLValue, lFactor_quasicharacterBase, Fintype.prod_sigma]
  refine congrArg (heckeL χ z s ^ _ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  dsimp only
  rw [Finset.prod_zpow, Finset.prod_div_distrib, div_eq_mul_inv]
  have h1 := prod_lFactor_quasicharacterAt_eq_prod_heckeL (K i)
    (HeckeCharacter.normComp χ * θh i) z s
  have h2 := prod_lFactor_quasicharacterAt_eq_prod_heckeL (K i)
    (HeckeCharacter.normComp χ * θh' i) z s
  rw [h1, h2]

/-- The dual form of `eval_arithmeticPairLFactor_eq_heckeL`: the arithmetic pair L-factor of
the duals of `(χ ∘ τ_F) ⊗ S` and `S'` along `ι`, evaluated at `q_z^{-s}`, is
`L(s, χ_z⁻¹)^{deg x} Π_i (Π_{u | z} L(s, λ_{i,u}⁻¹) / Π_{u | z} L(s, λ'_{i,u}⁻¹))^{r_i}`,
wherever these Hecke L-factors are nonzero. -/
theorem eval_arithmeticPairLFactor_dual_eq_heckeL
    (h : FundamentalClass.Restriction c)
    (hN2 : LocalInducedRestrictionStatement.{max u uV, u})
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E))
    (hX : X.IsContinuous) (eX : FiniteRepresentation.Equiv X (FiniteRepresentation.tensor S S'))
    (x : ContinuousVirtual.{u, uV} c F E) (hx : x = ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ)
    (hdec : ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.continuousTwist η x =
        ExactGrothendieckGroup.degree _ x •
            ExactGrothendieckGroup.characterClass.{u, max u uV} η +
          ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
            (restrictionInclusion c F E (K i) h)
            (isOpenEmbedding_restrictionInclusion c F E (K i) h)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ' i)))
    (θh θh' : ∀ i, HeckeCharacter (K i))
    (hθh : ∀ i, θ i = continuousReciprocityCharacter c (K i) E (θh i))
    (hθh' : ∀ i, θ' i = continuousReciprocityCharacter c (K i) E (θh' i))
    {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (s : ℂ) (hs₀ : heckeL χ⁻¹ z s ≠ 0)
    (hs : ∀ i, ∀ u ∈ placesAbove (K i) z,
      heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s ≠ 0 ∧
        heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (padicField z).canonicalTopologicalData.residueCardinality s)
        (Correspondence.arithmeticPairLFactor (padicField z)
          (krullLocalPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual ι)
          (krullLocalPairClass S'.dual ι)) =
      heckeL χ⁻¹ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s)⁻¹) ^
            r i := by
  have hstep := continuousRestrict_continuousTwist_eq_weilCharacter h hN2 hN3 hN4 hgeo χ x r K
    θ θ' hdec θh θh' hθh hθh' w e ι hι eC heC
  subst hx
  have hid := (continuousRestrict_continuousTwist_ofRepresentation χ X hX ι).symm.trans hstep
  have hgeoz := hgeo _ _ eC heC
  have hmem : ∀ j : (Σ i, FinitePlacesAbove (K i) z), j.2.1 ∈ placesAbove (K j.1) z :=
    fun j => Finset.mem_map_of_mem _ (Finset.mem_univ j.2)
  let eT : FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
        (FiniteRepresentation.twist (continuousReciprocityCharacter c F E χ).toMonoidHom X))
      (FiniteRepresentation.tensor
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
          (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S))
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom S')) :=
    (FiniteRepresentation.restrictEquivOfEquiv _
      (FiniteRepresentation.twistEquiv _ eX)).trans
      (FiniteRepresentation.restrictTwistTensorEquiv _ _ S S')
  have hb := Weil.Local.InertiaEuler.eval_arithmeticPairLFactor_dual_eq_virtualLValue (padicField z)
    _ _ _ _ eT _ _ (FiniteRepresentation.restrictDualEquiv _ _)
    (FiniteRepresentation.restrictDualEquiv _ _)
    (fun j : (Σ i, FinitePlacesAbove (K i) z) => towerPadicField z j.2.1)
    (fun j => completionPadicAlgHom z j.2.1)
    (hgeoz.1 _ (Correspondence.baseReciprocityCandidate_spec _ eC)) (fun j => hgeoz.2 _ _)
    _ _ _ _ (fun j => r j.1) hid s
    ((lFactor_inv_quasicharacterBase_eq_heckeL χ z s).trans_ne hs₀)
    (fun j => (lFactor_inv_quasicharacterAt_eq_heckeL _ j.2.1 _ s).trans_ne
      (hs j.1 j.2.1 (hmem j)).1)
    (fun j => (lFactor_inv_quasicharacterAt_eq_heckeL _ j.2.1 _ s).trans_ne
      (hs j.1 j.2.1 (hmem j)).2)
  refine hb.trans ?_
  rw [Weil.Local.InertiaEuler.virtualLValue, lFactor_inv_quasicharacterBase_eq_heckeL,
    Fintype.prod_sigma]
  refine congrArg (heckeL χ⁻¹ z s ^ _ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  dsimp only
  rw [Finset.prod_zpow, Finset.prod_div_distrib, div_eq_mul_inv]
  have h1 := prod_lFactor_inv_quasicharacterAt_eq_prod_heckeL (K i)
    (HeckeCharacter.normComp χ * θh i) z s
  have h2 := prod_lFactor_inv_quasicharacterAt_eq_prod_heckeL (K i)
    (HeckeCharacter.normComp χ * θh' i) z s
  rw [h1, h2]

end LFactor

section Epsilon

open Langlands.VirtualRepresentation
open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- The trace components of `ψf` at a place `u` above `z` are `ψf_z ∘ Tr_{K_u/F_z}`. -/
theorem traceComponents_apply_of_liesOver {K : Type u} [Field K] [NumberField K] [Algebra F K]
    (ψf : ∀ v : Langlands.Global.FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (z : Langlands.Global.FinitePlace F) (u : Langlands.Global.FinitePlace K)
    [u.asIdeal.LiesOver z.asIdeal] (y : u.adicCompletion K) :
    traceComponents ψf u y = ψf z (FiniteExtension.localTrace z u y) := by
  have hz : u.under (𝓞 F) = z :=
    IsDedekindDomain.HeightOneSpectrum.ext (u.asIdeal.over_def z.asIdeal).symm
  subst hz
  rfl

/-- The base epsilon factor at `z`: for a base additive character `ψ'` of `ψ_z` and a
bottom-field measure `μd` self-dual for `ψ'`, Tate's epsilon factor of `χ_z` at the measure
on `F_z` corresponding to `μd` is the Hecke epsilon factor `finiteEpsilon χ ψf μ z`, when
`ψf_z` is `ψ_z` read in the completion topology. -/
theorem epsilon_baseFieldHaarMeasure_eq_finiteEpsilon (χ : HeckeCharacter F)
    (ψf : ∀ v : Langlands.Global.FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (z : Langlands.Global.FinitePlace F)
    (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
    (hψf : ψf z = ofCanonicalCharacter z ψz)
    (ψ' : LocalFactor.CommonClosure.AdditiveCharacter (padicField z)
      (Correspondence.baseExtension (padicField z)))
    (hψ' : Correspondence.IsBaseCharacter (padicField z) ψz ψ')
    (μd : LocalFactor.CommonClosure.HaarMeasure (padicField z)
      (Correspondence.baseExtension (padicField z)))
    (hμd : LocalFactor.CommonClosureSpectral.IsSelfDual (padicField z)
      (Correspondence.baseExtension (padicField z)) ψ' μd) (s : ℂ) :
    LocalFactor.PadicAbelian.epsilon (padicField z).canonicalTopologicalData
        (quasicharacterBase z (χ.finiteComponent z)) ψz
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
          (padicField z).canonicalTopologicalData.topology
          (@borel _ (padicField z).canonicalTopologicalData.topology)
          ((Correspondence.baseFieldHaarMeasureEquiv (padicField z)).symm μd)) s =
      HeckeFunctionalEquation.finiteEpsilon χ ψf μ z s := by
  have hψa : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
      (padicField z).canonicalTopologicalData.topology ψz = (ψf z).toAddChar := by
    rw [hψf]
    rfl
  have h1 := (Correspondence.isSelfDual_of_isBaseCharacter_iff _ ψz ψ' hψ' μd).1 hμd
  have h2 := LocalFactor.PadicAbelian.isSelfDualMeasure_haarMeasureCongr
    (topologicalData_eq_canonicalTopologicalData z) (ψf z) (μ z) ψz hψa
  rw [Correspondence.eq_localSelfDualHaar _ ψz _ h1,
    ← Correspondence.eq_localSelfDualHaar _ ψz _ h2]
  exact LocalFactor.PadicAbelian.epsilon_quasicharacterCongr
    (topologicalData_eq_canonicalTopologicalData z) _ (ψf z) ψz hψa (μ z).val s

omit [IsGalois F E] in
/-- The product over the places `u` of `K` above `z` of Tate's epsilon factors of the canonical
packages `K_u`, for the standalone trace characters of `ψ_z` and the transported self-dual
measures, is the product over `placesAbove K z` of the Hecke epsilon factors for the trace
components of `ψf`. -/
theorem prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon (K : IntermediateField F E)
    (l : HeckeCharacter K)
    (ψf : ∀ v : Langlands.Global.FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (z : Langlands.Global.FinitePlace F)
    (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
    (hψf : ψf z = ofCanonicalCharacter z ψz)
    (μK : ∀ u : Langlands.Global.FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u))
    (s : ℂ) :
    ∏ q : FinitePlacesAbove K z,
        LocalFactor.PadicAbelian.epsilon (towerPadicField z q.1).canonicalTopologicalData
          (quasicharacterAt q.1 (residuePrime_eq z q.1) (l.finiteComponent q.1))
          (Weil.Local.SystemEpsilon.standaloneTraceCharacter (padicField z)
            (towerPadicField z q.1) (completionPadicAlgHom z q.1) ψz)
          (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
            (towerPadicField z q.1).canonicalTopologicalData.topology
            (@borel _ (towerPadicField z q.1).canonicalTopologicalData.topology)
            (haarMeasureAt q.1 (residuePrime_eq z q.1) (μK q.1).val)) s =
      ∏ u ∈ placesAbove K z, HeckeFunctionalEquation.finiteEpsilon l (traceComponents ψf) μK u s := by
  rw [placesAbove, Finset.prod_map]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hψ : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
      (towerPadicField z q.1).canonicalTopologicalData.topology
      (Weil.Local.SystemEpsilon.standaloneTraceCharacter (padicField z)
        (towerPadicField z q.1) (completionPadicAlgHom z q.1) ψz) =
      (traceComponents ψf q.1).toAddChar := by
    refine DFunLike.ext _ _ fun y => ?_
    have ht := traceComponents_apply_of_liesOver ψf z q.1 y
    rw [hψf] at ht
    exact ht.symm
  exact epsilon_quasicharacterAt q.1 (residuePrime_eq z q.1) (l.finiteComponent q.1) _
    (traceComponents ψf q.1) hψ (μK q.1).val s

/-- Finite-place epsilon factors of twisted relative Weil pairs: in the setting of
`eval_arithmeticPairLFactor_eq_heckeL`, if `c q_z^{-ms}` is the arithmetic pair epsilon factor
of `((χ ∘ τ_F) ⊗ S, S')` along `ι` for a system with reciprocity family `eC` and the additive
character `ψ_z`, then `c q_z^{-ms}` is
`ε(s, χ_z)^{deg x} Π_i (Π_{u | z} ε(s, λ_{i,u}) / Π_{u | z} ε(s, λ'_{i,u}))^{r_i}`. These are the
Hecke epsilon factors `finiteEpsilon` for `ψf` and the trace components of `ψf`, at arbitrary
self-dual measures, where `ψf_z` is `ψ_z` read in the completion topology. -/
theorem epsilonMonomial_eq_finiteEpsilon
    (h : FundamentalClass.Restriction c)
    (hN2 : LocalInducedRestrictionStatement.{max u uV, u})
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E))
    (hX : X.IsContinuous) (eX : FiniteRepresentation.Equiv X (FiniteRepresentation.tensor S S'))
    (x : ContinuousVirtual.{u, uV} c F E) (hx : x = ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ)
    (hdec : ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.continuousTwist η x =
        ExactGrothendieckGroup.degree _ x •
            ExactGrothendieckGroup.characterClass.{u, max u uV} η +
          ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
            (restrictionInclusion c F E (K i) h)
            (isOpenEmbedding_restrictionInclusion c F E (K i) h)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ' i)))
    (θh θh' : ∀ i, HeckeCharacter (K i))
    (hθh : ∀ i, θ i = continuousReciprocityCharacter c (K i) E (θh i))
    (hθh' : ∀ i, θ' i = continuousReciprocityCharacter c (K i) E (θh' i))
    (ψf : ∀ v : Langlands.Global.FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (μK : ∀ i (u : Langlands.Global.FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u))
    {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z))
    (hεz : LocalFactor.NonabelianSystem.IsSystem (padicField z) eC εz)
    (hψf : ψf z = ofCanonicalCharacter z ψz) (cε : ℂˣ) (m : ℤ)
    (hε : Correspondence.IsArithmeticPairEpsilonFactor (padicField z) eC εz hεz ψz
      (krullLocalPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
      (krullLocalPairClass S' ι) cε m) (s : ℂ) :
    RankinSelberg.epsilonMonomial (padicField z).canonicalTopologicalData.residueCardinality
        cε m s =
      HeckeFunctionalEquation.finiteEpsilon χ ψf μ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon
              (HeckeCharacter.normComp χ * θh i) (traceComponents ψf) (μK i) u s) *
          (∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon
              (HeckeCharacter.normComp χ * θh' i) (traceComponents ψf) (μK i) u s)⁻¹) ^
            r i := by
  have hstep := continuousRestrict_continuousTwist_eq_weilCharacter h hN2 hN3 hN4 hgeo χ x r K
    θ θ' hdec θh θh' hθh hθh' w e ι hι eC hεz.1
  subst hx
  have hid := (continuousRestrict_continuousTwist_ofRepresentation χ X hX ι).symm.trans hstep
  let eT : FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
        (FiniteRepresentation.twist (continuousReciprocityCharacter c F E χ).toMonoidHom X))
      (FiniteRepresentation.tensor
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom
          (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S))
        (FiniteRepresentation.restrict (discreteLocalMap ι).toMonoidHom S')) :=
    (FiniteRepresentation.restrictEquivOfEquiv _
      (FiniteRepresentation.twistEquiv _ eX)).trans
      (FiniteRepresentation.restrictTwistTensorEquiv _ _ S S')
  obtain ⟨⟨ψ', μd, A, B, ⟨hψ', hμd, hA, hB⟩, hAc, hBc⟩, ⟨Φ⟩, hval⟩ := hε
  refine (hval ψ' μd A B ⟨hψ', hμd, hA, hB⟩ hAc hBc Φ s).symm.trans ?_
  have hb := Weil.Local.SystemEpsilon.conditionalPairEpsilonValue_eq_epsilon_of_virtualIdentity
    (padicField z) eC εz hεz _ _ _ _ eT
    (fun j : (Σ i, FinitePlacesAbove (K i) z) => towerPadicField z j.2.1)
    (fun j => completionPadicAlgHom z j.2.1) _ _ (fun j => r j.1) _ _ hid ψz ψ' hψ' μd
    (fun j => haarMeasureAt j.2.1 (residuePrime_eq z j.2.1) (μK j.1 j.2.1).val)
    A B hA hB hAc hBc Φ s
  refine hb.trans ?_
  rw [epsilon_baseFieldHaarMeasure_eq_finiteEpsilon χ ψf μ z ψz hψf ψ' hψ' μd hμd s,
    Fintype.prod_sigma]
  refine congrArg (HeckeFunctionalEquation.finiteEpsilon χ ψf μ z s ^ _ * ·)
    (Finset.prod_congr rfl fun i _ => ?_)
  dsimp only
  rw [Finset.prod_zpow, Finset.prod_div_distrib, div_eq_mul_inv]
  have h1 := prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon (K i)
    (HeckeCharacter.normComp χ * θh i) ψf z ψz hψf (μK i) s
  have h2 := prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon (K i)
    (HeckeCharacter.normComp χ * θh' i) ψf z ψz hψf (μK i) s
  rw [h1, h2]

end Epsilon

section Factors

open Langlands.VirtualRepresentation
open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- Finite-place factors of twisted relative Weil pairs as Hecke factors: in the setting of
`eval_arithmeticPairLFactor_eq_heckeL`, if `f` is the factor triple of the twisted pair
`((χ ∘ τ_F) ⊗ S, S')` along `ι` at `z` (`IsArithmeticPairLocalFactors`), then `f.lFactor`,
`f.dualLFactor` and `f.epsilonFactor` are the corresponding products of Hecke factors of `χ`
at `z` and of `λ_i = (χ ∘ N_{K_i/F}) θh_i`, `λ'_i = (χ ∘ N_{K_i/F}) θh'_i` at the places of
`K_i` above `z`; the L-factor identities hold wherever these Hecke L-factors are nonzero. -/
theorem localFactors_eq_heckeFactors
    (h : FundamentalClass.Restriction c)
    (hN2 : LocalInducedRestrictionStatement.{max u uV, u})
    (hN3 : LocalTransferReciprocityStatement.{u})
    (hN4 : TransferNormCompatibilityStatement.{u})
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    (χ : HeckeCharacter F) (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E))
    (hX : X.IsContinuous) (eX : FiniteRepresentation.Equiv X (FiniteRepresentation.tensor S S'))
    (x : ContinuousVirtual.{u, uV} c F E) (hx : x = ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ)
    (hdec : ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.continuousTwist η x =
        ExactGrothendieckGroup.degree _ x •
            ExactGrothendieckGroup.characterClass.{u, max u uV} η +
          ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
            (restrictionInclusion c F E (K i) h)
            (isOpenEmbedding_restrictionInclusion c F E (K i) h)
            (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (η.comp (restrictionInclusion c F E (K i) h) * θ' i)))
    (θh θh' : ∀ i, HeckeCharacter (K i))
    (hθh : ∀ i, θ i = continuousReciprocityCharacter c (K i) E (θh i))
    (hθh' : ∀ i, θ' i = continuousReciprocityCharacter c (K i) E (θh' i))
    (ψf : ∀ v : Langlands.Global.FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (μK : ∀ i (u : Langlands.Global.FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u))
    {z : Langlands.Global.FinitePlace F} (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : KrullLocalMap c F E z) (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z))
    (hεz : LocalFactor.NonabelianSystem.IsSystem (padicField z) eC εz)
    (hψf : ψf z = ofCanonicalCharacter z ψz) (f : LocalFactors)
    (hf : IsArithmeticPairLocalFactors.{u, uV, uE} (padicField z) eC εz hεz ψz
      (krullLocalPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
      (krullLocalPairClass S' ι)
      (krullLocalPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual ι)
      (krullLocalPairClass S'.dual ι) f) :
    (∀ s, heckeL χ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (HeckeCharacter.normComp χ * θh i) u s ≠ 0 ∧
          heckeL (HeckeCharacter.normComp χ * θh' i) u s ≠ 0) →
      f.lFactor s = heckeL χ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i) u s)⁻¹) ^
            r i) ∧
    (∀ s, heckeL χ⁻¹ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s ≠ 0 ∧
          heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s ≠ 0) →
      f.dualLFactor s = heckeL χ⁻¹ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s)⁻¹) ^
            r i) ∧
    (∀ s, f.epsilonFactor s =
      HeckeFunctionalEquation.finiteEpsilon χ ψf μ z s ^ ExactGrothendieckGroup.degree _ x *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon
              (HeckeCharacter.normComp χ * θh i) (traceComponents ψf) (μK i) u s) *
          (∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon
              (HeckeCharacter.normComp χ * θh' i) (traceComponents ψf) (μK i) u s)⁻¹) ^
            r i) := by
  obtain ⟨hL, hLd, cε, m, hε, hεf⟩ := hf
  refine ⟨fun s hs₀ hs => (hL s).trans ?_, fun s hs₀ hs => (hLd s).trans ?_,
    fun s => (hεf s).trans ?_⟩
  · exact eval_arithmeticPairLFactor_eq_heckeL h hN2 hN3 hN4 hgeo χ S S' X hX eX x hx r K θ θ'
      hdec θh θh' hθh hθh' w e ι hι eC hεz.1 s hs₀ hs
  · exact eval_arithmeticPairLFactor_dual_eq_heckeL h hN2 hN3 hN4 hgeo χ S S' X hX eX x hx r K
      θ θ' hdec θh θh' hθh hθh' w e ι hι eC hεz.1 s hs₀ hs
  · exact epsilonMonomial_eq_finiteEpsilon h hN2 hN3 hN4 hgeo χ S S' X hX eX x hx r K θ θ' hdec
      θh θh' hθh hθh' ψf μ μK w e ι hι ψz eC εz hεz hψf cε m hε s

end Factors

end Langlands.ClassField.Global.RelativeWeilGroup
