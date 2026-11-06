import Langlands.Representation.Unitary.CentralUnitarizer
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.Representation.Category.CentralCharacterRegularity
import Langlands.Representation.Category.Twist
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Weil.Representation.ContinuityProof
import Mathlib.Algebra.Category.Grp.Injective

/-! # Positive unramified twists with unitary central character

Renard 2026, VI.8.5 as used in VII.1.3 (printed p.224/PDF p.230): an irreducible smooth
representation becomes one with a unitary central character after a twist by an
unramified character with positive real values.

The construction does not need finite index of the central valuation image. The modulus
`|ω|` of a central character is a positive character of the center `Z` that is trivial
on the compact group `Z ∩ G¹`. It therefore factors through the image of `Z` under the
joint norm map `G → (I → ℝ≥0ˣ)`, whose kernel is `G¹`. The group `ℝ≥0ˣ` is divisible,
hence an injective `ℤ`-module, so this factor extends to `I → ℝ≥0ˣ`. Composing with the
joint norm map and inverting gives the required positive unramified character.
-/

noncomputable section

universe u v uG uI

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.PositiveCharacter

/-- `t ↦ exp t`, from `ℝ` to the positive real units. -/
def expAddHom : ℝ →+ Additive ℝ≥0ˣ where
  toFun t := Additive.ofMul
    (Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne')
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    simp
  map_add' s t := by
    apply Additive.toMul.injective
    apply Units.ext
    simp [Real.exp_add, Real.toNNReal_mul (Real.exp_pos s).le]

theorem expAddHom_surjective : Function.Surjective expAddHom := by
  intro a
  refine ⟨Real.log ((a.toMul : ℝ≥0) : ℝ), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  have hpos : (0 : ℝ) < ((a.toMul : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.toMul.ne_zero)
  change (Real.exp (Real.log ((a.toMul : ℝ≥0) : ℝ))).toNNReal = (a.toMul : ℝ≥0)
  rw [Real.exp_log hpos, Real.toNNReal_coe]

/-- Positive characters extend along injective homomorphisms of commutative groups: the
positive real units form a divisible, hence injective, abelian group. -/
theorem exists_extension {A B : Type*} [CommGroup A] [CommGroup B] (f : A →* B)
    (hf : Function.Injective f) (χ : A →* ℝ≥0ˣ) :
    ∃ ψ : B →* ℝ≥0ˣ, ψ.comp f = χ := by
  let : DivisibleBy (Additive ℝ≥0ˣ) ℤ :=
    Function.Surjective.divisibleBy expAddHom expAddHom_surjective
      (fun x n => map_zsmul expAddHom n x)
  obtain ⟨ψ, hψ⟩ :=
    (Module.Baer.of_divisible (Additive ℝ≥0ˣ)).extension_property_addMonoidHom
      f.toAdditive hf χ.toAdditive
  refine ⟨ψ.toMultiplicative, ?_⟩
  apply MonoidHom.ext
  intro a
  exact DFunLike.congr_fun hψ (Additive.ofMul a)

end Langlands.PositiveCharacter

namespace Langlands.Plancherel

section Abstract

variable {G : Type uG} [Group G] {I : Type uI}

/-- A positive character of a subgroup `A` that is trivial on `A ∩ G¹` is the restriction
of a positive character of `G` trivial on the common norm kernel `G¹`. -/
theorem exists_positiveCharacter_restrict_eq (ν : I → (G →* ℝ≥0ˣ)) (A : Subgroup G)
    (χ : A →* ℝ≥0ˣ) (hχ1 : ∀ a : A, (a : G) ∈ commonNormKernel ν → χ a = 1) :
    ∃ θ : G →* ℝ≥0ˣ, commonNormKernel ν ≤ θ.ker ∧ ∀ a : A, θ a = χ a := by
  let N : G →* (I → ℝ≥0ˣ) := MonoidHom.pi ν
  have hN : ∀ g, N g = 1 ↔ g ∈ commonNormKernel ν := by
    intro g
    rw [mem_commonNormKernel, funext_iff]
    rfl
  let φ : A →* (I → ℝ≥0ˣ) := N.comp A.subtype
  have hker : φ.ker ≤ χ.ker := by
    intro a ha
    exact hχ1 a ((hN a).mp ha)
  let χr : φ.range →* ℝ≥0ˣ :=
    (QuotientGroup.lift φ.ker χ hker).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hχr : ∀ a : A, χr ⟨φ a, ⟨a, rfl⟩⟩ = χ a := by
    intro a
    have hmk : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ a, ⟨a, rfl⟩⟩ =
        (a : A ⧸ φ.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift φ.ker χ hker
      ((QuotientGroup.quotientKerEquivRange φ).symm ⟨φ a, ⟨a, rfl⟩⟩) = χ a
    rw [hmk, QuotientGroup.lift_mk]
  obtain ⟨ψ, hψ⟩ := PositiveCharacter.exists_extension φ.range.subtype
    Subtype.val_injective χr
  refine ⟨ψ.comp N, fun g hg => ?_, fun a => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (hN g).mpr hg, map_one]
  · rw [← hχr a]
    exact DFunLike.congr_fun hψ ⟨φ a, ⟨a, rfl⟩⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Positive unramified correction of a character of a subgroup.** If the common norm
kernel `G¹` is open and `ω` is a character of a subgroup `A` with `|ω| = 1` on `A ∩ G¹`,
then some unramified character `ψ` of `G` with positive real values satisfies
`|ψ ω| = 1` on `A`. -/
theorem exists_positive_unramifiedCharacter_norm_mul_eq_one_of_norm (ν : I → (G →* ℝ≥0ˣ))
    (hG1 : IsOpen (commonNormKernel ν : Set G)) (A : Subgroup G) (ω : A →* ℂˣ)
    (hω1 : ∀ a : A, (a : G) ∈ commonNormKernel ν → ‖(ω a : ℂ)‖ = 1) :
    ∃ ψ : unramifiedCharacters ν,
      (∀ g : G, ∃ t : ℝ, 0 < t ∧ (((ψ : G →ₜ* ℂˣ) g : ℂˣ) : ℂ) = t) ∧
      ∀ a : A, ‖(((ψ : G →ₜ* ℂˣ) a : ℂˣ) : ℂ) * (ω a : ℂ)‖ = 1 := by
  obtain ⟨θ, hθker, hθ⟩ := exists_positiveCharacter_restrict_eq ν A
    (PositiveCharacter.normCharacter ω) (fun a ha => by
      apply Units.ext
      apply NNReal.coe_injective
      rw [PositiveCharacter.normCharacter_apply, coe_nnnorm, hω1 a ha]
      rfl)
  let ψ₀ : G →* ℂˣ := positiveUnitsToComplex.comp θ⁻¹
  have hψ₀ker : commonNormKernel ν ≤ ψ₀.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    change positiveUnitsToComplex (θ g)⁻¹ = 1
    rw [show θ g = 1 from hθker hg, inv_one, map_one]
  let ψ : G →ₜ* ℂˣ :=
    ⟨ψ₀, Langlands.Weil.continuous_of_open_kernel ψ₀ (Subgroup.isOpen_mono hψ₀ker hG1)⟩
  refine ⟨⟨ψ, hψ₀ker⟩, fun g => ⟨(((θ g)⁻¹ : ℝ≥0ˣ) : ℝ≥0), ?_, rfl⟩, fun a => ?_⟩
  · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (θ g)⁻¹.ne_zero)
  · change ‖(positiveUnitsToComplex (θ a)⁻¹ : ℂ) * (ω a : ℂ)‖ = 1
    rw [norm_mul, PositiveCharacter.norm_positiveUnitsToComplex, hθ a,
      Units.val_inv_eq_inv_val, NNReal.coe_inv, PositiveCharacter.normCharacter_apply,
      coe_nnnorm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (ω a).ne_zero)

/-- The same correction when `A ∩ G¹` is compact and `ω` has open kernel: the positive
character `|ω|` is then trivial on `A ∩ G¹`. -/
theorem exists_positive_unramifiedCharacter_norm_mul_eq_one_of_isCompact
    (ν : I → (G →* ℝ≥0ˣ)) (hG1 : IsOpen (commonNormKernel ν : Set G)) (A : Subgroup G)
    (hA1 : IsCompact ((commonNormKernel ν ⊓ A : Subgroup G) : Set G)) (ω : A →* ℂˣ)
    (hω : IsOpen (ω.ker : Set A)) :
    ∃ ψ : unramifiedCharacters ν,
      (∀ g : G, ∃ t : ℝ, 0 < t ∧ (((ψ : G →ₜ* ℂˣ) g : ℂˣ) : ℂ) = t) ∧
      ∀ a : A, ‖(((ψ : G →ₜ* ℂˣ) a : ℂˣ) : ℂ) * (ω a : ℂ)‖ = 1 := by
  refine exists_positive_unramifiedCharacter_norm_mul_eq_one_of_norm ν hG1 A ω ?_
  intro a ha
  have hK : IsCompact ((commonNormKernel ν).subgroupOf A : Set A) := by
    rw [Subtype.isCompact_iff]
    convert hA1 using 1
    ext g
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hb, b.2⟩
    · rintro ⟨hg, hgA⟩
      exact ⟨⟨g, hgA⟩, hg, rfl⟩
  have h := PositiveCharacter.eq_one_on_compact (PositiveCharacter.normCharacter ω)
    (PositiveCharacter.isOpen_ker_normCharacter ω hω) _ hK ⟨a, ha⟩
  have h' := congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) h
  simpa only [PositiveCharacter.normCharacter_apply, coe_nnnorm, Units.val_one,
    NNReal.coe_one] using h'

end Abstract

end Langlands.Plancherel

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]

local instance positiveTwistPointTopology : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

/-- Renard VI.8.5: for a connected reductive `H` and a character `ω` of the center of
`H(F)` with open kernel, some unramified character `ψ` of `H(F)` with positive real
values makes `ψ ω` unitary on the center. -/
theorem exists_positive_unramifiedCharacter_norm_mul_eq_one (hH : IsConnectedReductive H)
    (ω : Subgroup.center (rationalPoints H) →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (Subgroup.center (rationalPoints H)))) :
    ∃ ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul),
      (∀ h : rationalPoints H, ∃ t : ℝ, 0 < t ∧
        (((ψ : rationalPoints H →ₜ* ℂˣ) h : ℂˣ) : ℂ) = t) ∧
      ∀ z : Subgroup.center (rationalPoints H),
        ‖(((ψ : rationalPoints H →ₜ* ℂˣ) z : ℂˣ) : ℂ) * (ω z : ℂ)‖ = 1 := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Smooth H.X.hom := hH.smooth
  have : IsTopologicalGroup (rationalPoints H) := Langlands.AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup k H
  exact Plancherel.exists_positive_unramifiedCharacter_norm_mul_eq_one_of_isCompact _
    (Plancherel.isOpen_rationalCommonNormKernel H) (Subgroup.center (rationalPoints H))
    (Plancherel.isCompact_rationalCommonNormKernel_inf_center H hH) ω hω

/-- A twist by a character `ψ` of a representation with central character `ω` has a
unitary central character as soon as `|ψ ω| = 1` on the center. -/
def twistUnitaryCentralCharacter [IsTopologicalGroup (rationalPoints H)] {V : Type v}
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints H) V) (ψ : rationalPoints H →* ℂˣ)
    (hψ : IsOpen (ψ.ker : Set (rationalPoints H)))
    (ω : Subgroup.center (rationalPoints H) →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (Subgroup.center (rationalPoints H))))
    (hact : ∀ (z : Subgroup.center (rationalPoints H)) (x : V), ρ z x = (ω z : ℂ) • x)
    (hnorm : ∀ z : Subgroup.center (rationalPoints H), ‖(ψ z : ℂ) * (ω z : ℂ)‖ = 1) :
    UnitaryCentralCharacter (Langlands.twist ψ ρ) where
  character := ψ.comp (Subgroup.center (rationalPoints H)).subtype * ω
  isOpen_ker := by
    apply Subgroup.isOpen_mono (H₁ :=
      (ψ.comp (Subgroup.center (rationalPoints H)).subtype).ker ⊓ ω.ker) ?_
      ((hψ.preimage continuous_subtype_val).inter hω)
    intro z hz
    change ψ z * ω z = 1
    have hz1 : ψ z = 1 := hz.1
    have hz2 : ω z = 1 := hz.2
    rw [hz1, hz2, one_mul]
  norm_eq_one z := hnorm z
  acts z x := by
    change (ψ z : ℂ) • ρ z x = ((ψ z : ℂ) * (ω z : ℂ)) • x
    rw [hact, smul_smul]

/-- Renard VI.8.5 for irreducible representations: an irreducible smooth representation
of `H(F)` has a twist by an unramified character with positive real values whose central
character is unitary. The central character is the Schur character
`CuspidalSupport.rationalPointCentralCharacter`. -/
theorem exists_positive_unramifiedTwist_unitaryCentralCharacter
    [NonarchimedeanGroup (rationalPoints H)] (hH : IsConnectedReductive H)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints H)) (hπ : π.IsIrreducible) :
    ∃ ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters H => (Plancherel.rationalNormCharacters H c).toMul),
      (∀ h : rationalPoints H, ∃ t : ℝ, 0 < t ∧
        (((ψ : rationalPoints H →ₜ* ℂˣ) h : ℂˣ) : ℂ) = t) ∧
      Nonempty (UnitaryCentralCharacter
        (π.twist (ψ : rationalPoints H →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Smooth H.X.hom := hH.smooth
  obtain ⟨ω, hact⟩ := CuspidalSupport.rationalPointCentralCharacter k H hH π hπ
  obtain ⟨x, hx⟩ :=
    Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible π.representation hπ
  have : Nontrivial π := ⟨⟨x, 0, hx⟩⟩
  have hω : IsOpen (ω.ker : Set (Subgroup.center (rationalPoints H))) :=
    SmoothRep.HasCentralCharacter.isOpen_ker π hact
  obtain ⟨ψ, hpos, hnorm⟩ := exists_positive_unramifiedCharacter_norm_mul_eq_one hH ω hω
  exact ⟨ψ, hpos, ⟨twistUnitaryCentralCharacter π.representation
    (ψ : rationalPoints H →ₜ* ℂˣ).toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
    ω hω hact hnorm⟩⟩

end Langlands.Aubert.General.RepresentedParabolic
