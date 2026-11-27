import Langlands.Global.AdelicConstantTermSplitFinitenessReduction
import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Global.AdelicAutomorphicExponentDecompositionReductionStatement
import Langlands.Global.FiniteTranslationExponentPolynomials
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation
import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # The exponent decomposition from Harish-Chandra's finiteness theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.InfiniteAdelicGroupPoints
  Langlands.GroupScheme Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- An ideal of the center annihilating every infinite slice of `φ` annihilates every infinite
slice of each left translate `x ↦ φ (a x)`. -/
theorem centerAnnihilation_leftTranslate {φ : AdelicGroupPoints F G → ℂ}
    (hslice : ∀ b, functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G)
    {I : Ideal (AdelicEnvelopingCenter F G hsmooth)}
    (hI : ∀ z ∈ I, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G φ b, h⟩ = 0)
    (a : AdelicGroupPoints F G) :
    ∀ z ∈ I, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ h : functionInfiniteSlice F G (fun x => φ (a * x)) b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z
          ⟨functionInfiniteSlice F G (fun x => φ (a * x)) b, h⟩ = 0 := by
  intro z hz b hb
  let aInf := infinite F G a
  let aFin := finite F G a
  let φslice : InfinitePlotSmoothFunctions F G :=
    ⟨functionInfiniteSlice F G φ (aFin * b), hslice (aFin * b)⟩
  have hsl : functionInfiniteSlice F G (fun x => φ (a * x)) b =
      (plotSmoothLeftTranslation F G aInf φslice).val := by
    funext x
    change φ (a * pair F G x b) = φ (pair F G (aInf * x) (aFin * b))
    conv_lhs => rw [← pair_projections F G a, pair_mul]
  have heq : (⟨functionInfiniteSlice F G (fun x => φ (a * x)) b, hb⟩ :
      InfinitePlotSmoothFunctions F G) = plotSmoothLeftTranslation F G aInf φslice :=
    Subtype.ext hsl
  rw [heq]
  have hzer : plotSmoothEnvelopingAction F G hsmooth hcalc z.val φslice = 0 :=
    hI z hz (aFin * b) (hslice (aFin * b))
  change plotSmoothEnvelopingAction F G hsmooth hcalc z.val
    (plotSmoothLeftTranslation F G aInf φslice) = 0
  rw [plotSmoothEnvelopingAction_leftTranslation hcalc, hzer, map_zero]

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Coordinates

variable {F : Type u} [Field F] {P : GroupScheme (Spec (CommRingCat.of F))}
  {κ : Type*} [Fintype κ] (b : Module.Basis κ ℤ (GroupScheme.rationalCharacters P))

/-- The real dual element with coordinates `t` in the dual basis of a `ℤ`-basis `b` of the
rational characters. -/
def basisCoordinateDual (t : κ → ℝ) : RealCharacterDual F P :=
  (show GroupScheme.rationalCharacters P →+ ℝ from
    { toFun := fun χ => ∑ j, t j * (b.repr χ j : ℝ)
      map_zero' := by simp
      map_add' := fun χ ψ => by
        simp only [map_add, Finsupp.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib] })

theorem basisCoordinateDual_apply (t : κ → ℝ) (χ : GroupScheme.rationalCharacters P) :
    basisCoordinateDual (F := F) b t χ = ∑ j, t j * (b.repr χ j : ℝ) := rfl

theorem basisCoordinateDual_basis [DecidableEq κ] (t : κ → ℝ) (j : κ) :
    basisCoordinateDual (F := F) b t (b j) = t j := by
  rw [basisCoordinateDual_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem basisCoordinateDual_add (s t : κ → ℝ) :
    basisCoordinateDual (F := F) b (s + t) =
      basisCoordinateDual (F := F) b s + basisCoordinateDual (F := F) b t := by
  apply AddMonoidHom.ext
  intro χ
  change basisCoordinateDual (F := F) b (s + t) χ =
    basisCoordinateDual (F := F) b s χ + basisCoordinateDual (F := F) b t χ
  simp only [basisCoordinateDual_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem basisCoordinateDual_eval (H : RealCharacterDual F P) :
    basisCoordinateDual (F := F) b (fun j => H (b j)) = H := by
  apply AddMonoidHom.ext
  intro χ
  change basisCoordinateDual (F := F) b (fun j => H (b j)) χ = H χ
  rw [basisCoordinateDual_apply]
  let H' : GroupScheme.rationalCharacters P →+ ℝ := H
  change ∑ j, H' (b j) * (b.repr χ j : ℝ) = H' χ
  conv_rhs => rw [← b.sum_repr χ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul, mul_comm]

theorem continuous_basisCoordinateDual :
    Continuous (basisCoordinateDual (F := F) b) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro χ
  change Continuous fun t : κ → ℝ => ∑ j, t j * (b.repr χ j : ℝ)
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

/-- The coordinates `H ↦ (H (b j))_j` as a real-linear map. -/
def basisCoordinates : RealCharacterDual F P →ₗ[ℝ] (κ → ℝ) where
  toFun H j := H (b j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complex parameter `∑ j, mu j ⊗ b j`. -/
def basisParameter (mu : κ → ℂ) : ComplexCharacterParameter F P :=
  ∑ j, mu j ⊗ₜ[ℤ] b j

theorem complexParameterPairing_basisParameter (mu : κ → ℂ) (H : RealCharacterDual F P) :
    complexParameterPairing F P (basisParameter (F := F) b mu) H =
      ∑ j, (H (b j) : ℂ) * mu j := by
  simp only [basisParameter, map_sum, LinearMap.sum_apply, complexParameterPairing_tmul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem basisParameter_injective [DecidableEq κ] :
    Function.Injective (basisParameter (F := F) b) := by
  intro mu mu' h
  funext k
  have hk := congrArg (fun lam => complexParameterPairing F P lam
    (basisCoordinateDual (F := F) b (Pi.single k 1))) h
  simp only [complexParameterPairing_basisParameter, basisCoordinateDual_basis] at hk
  simpa [Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hk

end Coordinates

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

omit [NumberField F] in
/-- The Levi and the geometric unipotent radical of a standard parabolic multiply isomorphically
onto it. -/
theorem isIso_subgroupMultiplication_levi_radical (J : StandardIndex F G fam.i fam.ν) :
    IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) := by
  have : Smooth G.X.hom := fam.connectedReductive.smooth
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ fam.a J ≫ fam.l J ≫ fam.p J
  have hP : (Dynamic.parabolic χ).IsRepresentedBy (fam.p J) :=
    ⟨IsClosedSubgroup.mono_overHom r.isCompatible.parabolic.isClosedSubgroup,
      r.parabolic_eq_splitComponentCocharacter⟩
  have hM : (Dynamic.centralizer χ).IsRepresentedBy (fam.l J ≫ fam.p J) :=
    ⟨IsClosedSubgroup.mono_overHom (r.isCompatible.levi.isClosedSubgroup.comp
      r.isCompatible.parabolic.isClosedSubgroup),
      r.levi_eq_splitComponentCocharacter⟩
  have hN : (Dynamic.unipotent χ).IsRepresentedBy (fam.iU J ≫ fam.p J) :=
    ⟨IsClosedSubgroup.mono_overHom ((fam.isUnipotentRadical J).1.isClosedSubgroup.comp
      r.isCompatible.parabolic.isClosedSubgroup),
      r.range_comp_radical_eq (fam.isUnipotentRadical J)⟩
  exact Dynamic.isIso_subgroupMultiplication hP hM hN (fam.l J) (fam.iU J) rfl rfl

/-- A continuous homomorphic section `σ` of the logarithm on the positive split component
`𝔄_J`, with image `𝔄_J`. -/
theorem exists_positiveSplitComponent_section (J : StandardIndex F G fam.i fam.ν) :
    ∃ σ : Multiplicative (RealCharacterDual F (fam.P J)) →ₜ* AdelicGroupPoints F (fam.P J),
      (∀ ℓ, σ ℓ ∈ fam.positiveSplitComponent J) ∧
      ∀ x ∈ fam.positiveSplitComponent J,
        σ (Multiplicative.ofAdd (characterLog F (fam.P J) x)) = x := by
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have hinj := characterRestrict_splitComponent_injective r
  obtain ⟨_, _, proj, -, -, hproj, -⟩ :=
    r.isCompatible.levi.exists_unipotentRadical_retraction
  have hsurj : Function.Surjective (characterRestrict (fam.l J)) := by
    intro χ
    refine ⟨characterRestrict proj χ, ?_⟩
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hproj, characterRestrict_id]
    rfl
  have hrange : (characterRestrict (fam.a J ≫ fam.l J)).range =
      (characterRestrict (fam.a J)).range := by
    ext χ
    change (∃ x, characterRestrict (fam.a J ≫ fam.l J) x = χ) ↔
      ∃ y, characterRestrict (fam.a J) y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict (fam.l J) x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  let : (characterRestrict (fam.a J ≫ fam.l J)).range.FiniteIndex := hrange.symm ▸
    r.isCompatible.splitComponent.finiteIndex_range_characterRestrict
      r.isCompatible.levi.isConnectedReductive
  obtain ⟨I, hI, ⟨e⟩⟩ := r.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let : Fintype I := Fintype.ofFinite I
  have hR := PositiveRealTorus.logSection_range F (fam.P J) (fam.A J) (fam.a J ≫ fam.l J) hinj I e
  refine ⟨PositiveRealTorus.logSection F (fam.P J) (fam.A J) (fam.a J ≫ fam.l J) hinj I e,
    fun ℓ => ?_, fun x hx => ?_⟩
  · change _ ∈ PositiveRealTorus.imageSubgroup F (fam.A J) (fam.P J) (fam.a J ≫ fam.l J)
    rw [← hR]
    exact ⟨ℓ, rfl⟩
  · change x ∈ PositiveRealTorus.imageSubgroup F (fam.A J) (fam.P J) (fam.a J ≫ fam.l J) at hx
    rw [← hR] at hx
    obtain ⟨ℓ, rfl⟩ := hx
    have h := PositiveRealTorus.characterLogHom_logSection F (fam.P J) (fam.A J)
      (fam.a J ≫ fam.l J) hinj I e ℓ
    change PositiveRealTorus.logSection F (fam.P J) (fam.A J) (fam.a J ≫ fam.l J) hinj I e
      (characterLogHom F (fam.P J) (PositiveRealTorus.logSection F (fam.P J) (fam.A J)
        (fam.a J ≫ fam.l J) hinj I e ℓ)) = _
    rw [h]
    rfl

variable {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- **The exponent decomposition from a finite-dimensional orbit.** If `ψ` is automorphic on
`U_J(𝔸) M_J(F) \ G(𝔸)` and its left translates by the positive split component `𝔄_J` span a
finite-dimensional space, then `ψ` is a finite sum of automorphic functions on the same quotient
with generalized unnormalized exponents, which are cuspidal along `J` when `ψ` is. No hypothesis
on a compact subgroup enters. -/
theorem exists_exponentDecomposition_of_finiteDimensional_translates
    {J : StandardIndex F G fam.i fam.ν} {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.IsAutomorphicOn hsmooth Kinf rho J ψ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun a : fam.positiveSplitComponent J => fam.unnormalizedAction J a ψ))) :
    ∃ (s : Finset (ComplexCharacterParameter F (fam.P J)))
      (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
      ψ = ∑ lam ∈ s, c lam ∧
      ∀ lam ∈ s, fam.IsAutomorphicOn hsmooth Kinf rho J (c lam) ∧
        fam.HasUnnormalizedExponent J lam (c lam) ∧
        (fam.IsCuspidalAlong J ψ → fam.IsCuspidalAlong J (c lam)) := by
  classical
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  obtain ⟨hfree, hfinite⟩ := r.rationalCharacters_free_finite fam.connectedReductive
  let κ := Module.Free.ChooseBasisIndex ℤ (GroupScheme.rationalCharacters (fam.P J))
  let bχ : Module.Basis κ ℤ (GroupScheme.rationalCharacters (fam.P J)) :=
    Module.Free.chooseBasis ℤ _
  obtain ⟨σ, hσmem, hσlog⟩ := fam.exists_positiveSplitComponent_section J
  let Hd : (κ → ℝ) →+ RealCharacterDual F (fam.P J) :=
    { toFun := basisCoordinateDual (F := F) bχ
      map_zero' := by
        apply AddMonoidHom.ext
        intro χ
        change basisCoordinateDual (F := F) bχ 0 χ = 0
        simp [basisCoordinateDual_apply]
      map_add' := basisCoordinateDual_add (F := F) bχ }
  let τ : Multiplicative (κ → ℝ) →* fam.positiveSplitComponent J :=
    (σ.toMonoidHom.comp (AddMonoidHom.toMultiplicative Hd)).codRestrict _ fun _ => hσmem _
  let T : Multiplicative (κ → ℝ) →* Module.End ℂ (AdelicGroupPoints F G → ℂ) :=
    (fam.splitComponentRepresentation J).comp τ
  have hT (t : κ → ℝ) (φ : AdelicGroupPoints F G → ℂ) :
      T (Multiplicative.ofAdd t) φ = fam.unnormalizedAction J
        (σ (Multiplicative.ofAdd (basisCoordinateDual (F := F) bχ t))) φ := rfl
  let W := Submodule.span ℂ (Set.range fun t : κ → ℝ => T (Multiplicative.ofAdd t) ψ)
  have hWle : W ≤ Submodule.span ℂ
      (Set.range fun a : fam.positiveSplitComponent J => fam.unnormalizedAction J a ψ) := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨τ (Multiplicative.ofAdd t), rfl⟩
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hW : ∀ t, ∀ w ∈ W, T t w ∈ W := by
    intro t w hw
    have hle : W ≤ W.comap (T t) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨s, rfl⟩
      refine Submodule.subset_span ⟨Multiplicative.toAdd t + s, ?_⟩
      change T (Multiplicative.ofAdd (Multiplicative.toAdd t + s)) ψ =
        T t (T (Multiplicative.ofAdd s) ψ)
      rw [ofAdd_add, ofAdd_toAdd, map_mul, Module.End.mul_apply]
    exact hle hw
  have hσc : Continuous fun t : κ → ℝ => map F (fam.P J) G (fam.p J)
      (σ (Multiplicative.ofAdd (basisCoordinateDual (F := F) bχ t))) :=
    (AdelicGroupPoints.map F (fam.P J) G (fam.p J)).continuous.comp
      (σ.continuous.comp (continuous_ofAdd.comp (continuous_basisCoordinateDual (F := F) bχ)))
  have hWcont : ∀ w ∈ W, Continuous w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, rfl⟩ := hw
      change Continuous (T (Multiplicative.ofAdd t) ψ)
      rw [hT]
      exact hψ.2.1.1.comp (continuous_const.mul continuous_id)
    | zero => exact continuous_const
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_smul c
  have hcont : ∀ w ∈ W, ∀ g, Continuous fun t : κ → ℝ => T (Multiplicative.ofAdd t) w g := by
    intro w hw g
    change Continuous fun t : κ → ℝ => w (map F (fam.P J) G (fam.p J)
      (σ (Multiplicative.ofAdd (basisCoordinateDual (F := F) bχ t))) * g)
    exact (hWcont w hw).comp (hσc.mul continuous_const)
  obtain ⟨n, hdec⟩ := exists_exponentPolynomial_decomposition T W hW hcont
  have hψW : ψ ∈ W := Submodule.subset_span ⟨0, by
    change T (Multiplicative.ofAdd 0) ψ = ψ
    rw [ofAdd_zero, map_one, Module.End.one_apply]⟩
  obtain ⟨s0, u, hsum, hu⟩ := hdec ψ hψW
  have hΛ := basisParameter_injective (F := F) bχ
  let Γ := parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
  let Aut := automorphicFunctionsOn Γ Kinf rho hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth)
  have hWaut : W ≤ Aut := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact IsAutomorphicOn.unnormalizedAction fam hsmooth Kinf rho hψ (τ (Multiplicative.ofAdd t))
  have hrad : fam.IsRadicalInvariant J ψ :=
    (fam.isParabolicGeneratorInvariant_of_isLeftInvariantUnder J hψ.1).1
  refine ⟨s0.image (basisParameter (F := F) bχ),
    fun lam => u (Function.invFun (basisParameter (F := F) bχ) lam), ?_, ?_⟩
  · rw [Finset.sum_image fun x _ y _ h => hΛ h]
    simpa only [Function.leftInverse_invFun hΛ _] using hsum
  · intro lam hlam
    obtain ⟨mu, hmu, rfl⟩ := Finset.mem_image.mp hlam
    simp only [Function.leftInverse_invFun hΛ mu]
    obtain ⟨huW, hpoly⟩ := hu mu hmu
    refine ⟨hWaut huW, ⟨n, fun g => ?_⟩, fun hcusp => ?_⟩
    · refine ⟨_, comp_linearMap_mem_polynomialFunctions (basisCoordinates (F := F) bχ)
        (hpoly g), fun x hx => ?_⟩
      have hxσ : σ (Multiplicative.ofAdd (basisCoordinateDual (F := F) bχ
          (basisCoordinates (F := F) bχ (characterLog F (fam.P J) x)))) = x := by
        rw [show basisCoordinates (F := F) bχ (characterLog F (fam.P J) x) =
          fun j => characterLog F (fam.P J) x (bχ j) from rfl, basisCoordinateDual_eval]
        exact hσlog x hx
      simp only [Function.comp_apply]
      rw [hT, hxσ]
      congr 1
      simp only [parameterPower, map_neg, LinearMap.neg_apply,
        complexParameterPairing_basisParameter]
      rfl
    · intro Q' hQ'
      let L' := fam.constantTermLinear J Q' hsmooth Kinf rho hQ'.le
      have hWc : W ≤ (LinearMap.ker L').map Aut.subtype := by
        apply Submodule.span_le.mpr
        rintro _ ⟨t, rfl⟩
        refine ⟨⟨_, IsAutomorphicOn.unnormalizedAction fam hsmooth Kinf rho hψ
          (τ (Multiplicative.ofAdd t))⟩, ?_, rfl⟩
        change fam.constantTerm Q' (fam.unnormalizedAction J (τ (Multiplicative.ofAdd t)) ψ) = 0
        rw [fam.constantTerm_unnormalizedAction_of_radicalInvariant hQ'.le _ hrad, hcusp Q' hQ']
        rfl
      obtain ⟨y, hy, hyu⟩ := hWc huW
      rw [← hyu]
      exact LinearMap.mem_ker.mp hy

end StandardParabolicFamily

private theorem finiteDimensional_span_of_subset {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A B : Set V} (hB : FiniteDimensional ℂ (Submodule.span ℂ B)) (h : A ⊆ B) :
    FiniteDimensional ℂ (Submodule.span ℂ A) :=
  Submodule.finiteDimensional_of_le (Submodule.span_mono h)

/-- **The exponent decomposition from Harish-Chandra's finiteness theorem, for one function.**
Let `K` be a maximal compact subgroup of `G(𝔸)` with `G(𝔸) = P₀(𝔸) K` for the minimal standard
parabolic `P₀`, and `K_∞` its archimedean part. Harish-Chandra's finiteness theorem on
`U_Q(𝔸) M_Q(F) \ G(𝔸)` makes the span of the `𝔄_Q`-translates of an automorphic function
finite-dimensional, and the decomposition follows from
`StandardParabolicFamily.exists_exponentDecomposition_of_finiteDimensional_translates`. No
hypothesis on the intersections of `K` with the standard Levis enters. -/
theorem StandardParabolicFamily.exists_exponentDecomposition_of_parabolicHarishChandraFiniteness
    (hHC : ParabolicHarishChandraFinitenessStatement.{u})
    {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) {K : Subgroup (AdelicGroupPoints F G)}
    (hKmax : IsMaximalCompactSubgroup F G K)
    (hKiw : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hrho : IsClosedSubgroup rho) (Q : StandardIndex F G fam.i fam.ν)
    {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q ψ) :
    ∃ (s : Finset (ComplexCharacterParameter F (fam.P Q)))
      (c : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
      ψ = ∑ lam ∈ s, c lam ∧
      ∀ lam ∈ s, fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q (c lam) ∧
        fam.HasUnnormalizedExponent Q lam (c lam) ∧
        (fam.IsCuspidalAlong Q ψ → fam.IsCuspidalAlong Q (c lam)) := by
  apply fam.exists_exponentDecomposition_of_finiteDimensional_translates hsmooth _ rho hψ
  let hcalc := adelicDifferentialCommutator_of_smooth F G hsmooth
  let : IsClosedImmersion (fam.p Q).hom.hom.left := (fam.isCompatible Q).parabolic.isClosedSubgroup
  obtain ⟨I, hI, hIann⟩ := hψ.2.2.2.1
  obtain ⟨L, hL, hLfix⟩ := hψ.2.1.2.2
  obtain ⟨E, hE, hEmem⟩ := exists_finiteDimensional_profile hψ.2.2.1
  have hfin := hHC F G (fam.P Q) (fam.M Q) (fam.U Q) (fam.p Q) (fam.iU Q) (fam.l Q)
    fam.connectedReductive (fam.isCompatible Q).parabolic (fam.isUnipotentRadical Q)
    (fam.isCompatible Q).levi (fam.isIso_subgroupMultiplication_levi_radical Q) K hKmax
    (fam.isIwasawaCompact_of_minimal hKiw Q) rho hsmooth hcalc hrho I hI L hL E hE
  refine finiteDimensional_span_of_subset hfin ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨IsAutomorphicOn.unnormalizedAction fam hsmooth _ rho hψ a, ?_, ?_, ?_⟩
  · intro b hb g
    change ψ (map F (fam.P Q) G (fam.p Q) a * (g * ofFinite F G b)) =
      ψ (map F (fam.P Q) G (fam.p Q) a * g)
    rw [← mul_assoc]
    exact hLfix b hb _
  · exact centerAnnihilation_leftTranslate hcalc hψ.2.1.2.1 hIann (map F (fam.P Q) G (fam.p Q) a)
  · intro g
    have h := hEmem (map F (fam.P Q) G (fam.p Q) a * g)
    simp only [mul_assoc] at h
    exact h

/-- **The exponent decomposition from Harish-Chandra's finiteness theorem.** The hypothesis on
the intersections of `K` with the standard Levis is not used. -/
theorem automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness
    (hHC : ParabolicHarishChandraFinitenessStatement.{u}) :
    AutomorphicExponentDecompositionStatement.{u} := by
  intro F _ _ G _ _ _ fam K hKmax hKiw _ N d rho hsmooth hrho _ Q ψ hψ
  exact fam.exists_exponentDecomposition_of_parabolicHarishChandraFiniteness hHC hKmax hKiw rho
    hsmooth hrho Q hψ

/-- **Harish-Chandra's finiteness theorem implies the exponent decomposition**
(`AutomorphicExponentDecompositionReductionStatement`). -/
theorem automorphicExponentDecompositionReduction :
    AutomorphicExponentDecompositionReductionStatement.{u} :=
  automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness

end Langlands.Global
