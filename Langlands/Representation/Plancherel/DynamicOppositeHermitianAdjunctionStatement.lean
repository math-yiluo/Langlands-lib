import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.CompactInducedHermitianForm

/-! # Hermitian adjunction of the opposite standard integrals (target)

Waldspurger 2003, IV.1 (11) (printed p.283) states the adjunction
`⟨J_{P'|P}(π) f, f'⟩ = ⟨f, J_{P|P'}(π̌) f'⟩` of the standard intertwining operators for the
bilinear pairing of `I_P^G V` with `I_P^G V̌`. The proof of IV.3 (6) (printed p.287) uses its
Hermitian form on the compact picture: with a positive definite Hermitian product on `V` and
`(f, f') = ∫_K (f(k), f'(k)) dk`, one has
`(J_{P̄|P}(π ⊗ χ) f, f') = (f, J_{P|P̄}(π ⊗ χ) f')` for unitary `χ`.

On the convergence domains this Hermitian adjunction pairs the parameter `z` with its
conjugate-inverse `z† = z̄⁻¹`. This module constructs `z ↦ z†` on unramified characters, the
compact-picture Hermitian pairing, and states the adjunction for the Library's actual opposite
standard integrals `conditionalForwardCompactFamily` and `conditionalReverseCompactFamily`.
The statement is not proved here.
-/

noncomputable section

universe u uV uG uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### The conjugate-inverse of an unramified character -/

section ConjInv

variable {G : Type uG} [Group G] [TopologicalSpace G] {I : Type uI}

/-- Complex conjugation on `ℂˣ`, as a continuous homomorphism. -/
def unitsConj : ℂˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map (starRingEnd ℂ).toMonoidHom
  continuous_toFun := Continuous.units_map _ Complex.continuous_conj

@[simp]
theorem unitsConj_apply_coe (w : ℂˣ) : ((unitsConj w : ℂˣ) : ℂ) = starRingEnd ℂ (w : ℂ) := rfl

/-- The conjugate-inverse `z† : g ↦ conj(z(g))⁻¹` of a continuous complex character. -/
def characterConjInv (z : G →ₜ* ℂˣ) : G →ₜ* ℂˣ := (unitsConj.comp z)⁻¹

theorem characterConjInv_apply (z : G →ₜ* ℂˣ) (g : G) :
    characterConjInv z g = (unitsConj (z g))⁻¹ := rfl

@[simp]
theorem characterConjInv_apply_coe (z : G →ₜ* ℂˣ) (g : G) :
    ((characterConjInv z g : ℂˣ) : ℂ) = (starRingEnd ℂ (z g : ℂ))⁻¹ := by
  rw [characterConjInv_apply, Units.val_inv_eq_inv_val, unitsConj_apply_coe]

theorem characterConjInv_characterConjInv (z : G →ₜ* ℂˣ) :
    characterConjInv (characterConjInv z) = z := by
  ext g
  simp only [characterConjInv_apply_coe, map_inv₀, Complex.conj_conj, inv_inv]

/-- A unitary character is its own conjugate-inverse. -/
theorem characterConjInv_eq_self_of_mem_unitary {z : G →ₜ* ℂˣ}
    (hz : z ∈ unitaryCharacters G) : characterConjInv z = z := by
  ext g
  rw [characterConjInv_apply_coe]
  have h1 : ‖(z g : ℂ)‖ = 1 := hz g
  have hne : (z g : ℂ) ≠ 0 := (z g).ne_zero
  have hmul : starRingEnd ℂ (z g : ℂ) * (z g : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  exact inv_eq_of_mul_eq_one_right hmul

/-- The conjugate-inverse on the actual unramified characters. -/
def unramifiedConjInv (ν : I → (G →* ℝ≥0ˣ)) (z : unramifiedCharacters ν) :
    unramifiedCharacters ν :=
  ⟨characterConjInv z.val, by
    intro g hg
    have hzg : z.val g = 1 := z.property hg
    change characterConjInv z.val g = 1
    rw [characterConjInv_apply, hzg, map_one, inv_one]⟩

@[simp]
theorem unramifiedConjInv_val (ν : I → (G →* ℝ≥0ˣ)) (z : unramifiedCharacters ν) :
    (unramifiedConjInv ν z).val = characterConjInv z.val := rfl

theorem unramifiedConjInv_unramifiedConjInv (ν : I → (G →* ℝ≥0ˣ))
    (z : unramifiedCharacters ν) : unramifiedConjInv ν (unramifiedConjInv ν z) = z :=
  Subtype.ext (characterConjInv_characterConjInv z.val)

/-- At a unitary unramified character, `z† = z`. -/
theorem unramifiedConjInv_eq_self_of_mem_unitary (ν : I → (G →* ℝ≥0ˣ))
    {z : unramifiedCharacters ν} (hz : z.val ∈ unitaryUnramifiedCharacters ν) :
    unramifiedConjInv ν z = z :=
  Subtype.ext (characterConjInv_eq_self_of_mem_unitary hz.2)

end ConjInv

/-! ### The compact-picture Hermitian pairing -/

section Pairing

open Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The Hermitian pairing `(φ, ψ) = ∫_K b(φ(k), ψ(k)) dk` of two compact-picture sections,
against the Library's Haar probability `CompactInduction.measure K hK` on `K`. The first
argument is conjugate-linear, as for `b`. -/
def compactPictureHermitianPairing (A : SmoothRep.{0, uG, uV} ℂ M)
    (b : InvariantPositiveForm A.representation) (φ ψ : CompactInductionPicture h K A) : ℂ :=
  ∫ k : K, b.inner (Induction.eval _ _ φ k) (Induction.eval _ _ ψ k)
    ∂CompactInduction.measure K hK

end Pairing

/-! ### The target -/

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

/-- The Borel structure on the actual rational points. -/
local instance hermitianAdjunctionPointMeasurable {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    MeasurableSpace (RationalPoint F G.X) :=
  borel _

local instance hermitianAdjunctionPointBorel {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    BorelSpace (RationalPoint F G.X) :=
  ⟨rfl⟩

/-- **Target (Hermitian adjunction of IV.1 (11) on the convergence domains).** Let `χ` be a
cocharacter of `G`, `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `K` be a compact open
subgroup with `G = P K = P̄ K` whose intersections with `P` and `P̄` factor through `M`: the
Levi projections send `P ∩ K` and `P̄ ∩ K` into `K`. Let `A` be a smooth representation of
`M(F)` with an invariant positive definite Hermitian form `b`. Let `z` lie in the full
convergence domain of the forward integral `J_{P̄|P}` and its conjugate-inverse `z†` in that
of the reverse integral `J_{P|P̄}`. Then for compact-picture sections `φ` (for `P`) and `φ'`
(for `P̄`), `(J_{P̄|P}(z) φ, φ') = (φ, J_{P|P̄}(z†) φ')` for the pairing
`∫_K b(·(k), ·(k)) dk`. -/
def ConditionalDynamicOppositeHermitianAdjunctionStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (_hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (_hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation)
    (z : forwardFullDomainRegion χ K hK A)
    (hz : unramifiedConjInv (normCharacters χ) z.val ∈ reverseFullDomainRegion χ K hK A)
    (φ : CompactInductionPicture (decomposition χ) K A)
    (φ' : CompactInductionPicture (oppositeDecomposition χ) K A),
    compactPictureHermitianPairing (oppositeDecomposition χ) K hK A b
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) φ' =
      compactPictureHermitianPairing (decomposition χ) K hK A b φ
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A
          ⟨unramifiedConjInv (normCharacters χ) z.val, hz⟩ φ')

end Langlands.Plancherel
