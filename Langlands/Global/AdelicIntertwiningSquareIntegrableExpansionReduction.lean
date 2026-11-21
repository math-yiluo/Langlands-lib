import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement
import Langlands.Global.AdelicIntertwiningRegularHolomorphy
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement
import Langlands.Global.AdelicSquareIntegrableInducedSubmodule
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.BoundedWavePacketReduction
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.Analysis.Meromorphic.FiniteDimensionalValues
import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Analysis.Meromorphic.CoordinateGluing

/-! # Reduction of square-integrable intertwining expansions -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

private theorem exists_meromorphic_expansion_in_submodule {X Λ : Type*}
    [AddCommGroup Λ] [Module ℂ Λ] {k : ℕ} (B : Submodule ℂ (X → ℂ))
    (ψ : Fin k → X → ℂ) (a : Fin k → Λ → ℂ) {D S : Set Λ} {E : Λ → X → ℂ}
    [FiniteDimensional ℂ Λ] (hD : IsOpenDenseInCoordinates D)
    (ha : ∀ i, IsMeromorphicInCoordinatesOn (a i) D)
    (hE : ∀ lam ∈ S, ∀ x, E lam x = ∑ i, a i lam * ψ i x)
    (hS : ∀ lam ∈ S, E lam ∈ B) :
    ∃ (m : ℕ) (v : Fin m → X → ℂ) (coeff : Fin m → Λ → ℂ),
      (∀ i, v i ∈ B) ∧ (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
      ∀ lam ∈ S, ∀ x, E lam x = ∑ i, coeff i lam * v i x := by
  classical
  let W := Submodule.span ℂ (Set.range ψ)
  let T := W ⊓ B
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
  have : FiniteDimensional ℂ T :=
    FiniteDimensional.of_injective (Submodule.inclusion (inf_le_left : T ≤ W))
      (Submodule.inclusion_injective _)
  let b := Module.finBasis ℂ T
  let v : Fin (Module.finrank ℂ T) → X → ℂ := fun i => (b i : X → ℂ)
  have hv : LinearIndependent ℂ v := b.linearIndependent.map' T.subtype T.ker_subtype
  obtain ⟨L, hL⟩ := exists_continuousLinearMap_leftInverse v hv
  refine ⟨Module.finrank ℂ T, v, fun j lam => L (∑ i, a i lam • ψ i) j,
    fun i => (b i).property.2, fun j => ?_, ?_⟩
  · have hsum : (fun lam => L (∑ i, a i lam • ψ i) j) =
        ∑ i : Fin k, fun lam => a i lam * L (ψ i) j := by
      funext lam
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change IsMeromorphicInCoordinatesOn (fun lam => L (∑ i, a i lam • ψ i) j) D
    rw [hsum]
    exact IsMeromorphicInCoordinatesOn.sum Finset.univ hD fun i _ => by
      change IsMeromorphicInCoordinatesOn (a i * (fun _ : Λ => L (ψ i) j)) D
      simpa only [Set.inter_univ] using
        (ha i).mul (isMeromorphicInCoordinatesOn_const (L (ψ i) j))
  · intro lam hlam x
    have hrepr : E lam = ∑ i, a i lam • ψ i := funext fun y => by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hE lam hlam y
    have hT : E lam ∈ T :=
      ⟨(Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => a i lam, hrepr.symm⟩, hS lam hlam⟩
    let z : T := ⟨E lam, hT⟩
    have hb : (∑ i, b.equivFun z i • v i) = E lam := by
      simpa only [v, Submodule.coe_sum, SetLike.val_smul] using
        congrArg (fun y : T => (y : X → ℂ)) (b.sum_equivFun z)
    have hcoord := congrArg L hb
    rw [hL] at hcoord
    change E lam x = ∑ i, L (∑ j, a j lam • ψ j) i * v i x
    rw [← hrepr, ← hcoord]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hb.symm x

private theorem glue_regular_expansion {X Λ : Type*} [AddCommGroup Λ] [Module ℂ Λ]
    {m : ℕ} (ψ : Fin m → X → ℂ) {E : Λ → X → ℂ} {S D D' : Set Λ}
    (hS : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] Λ), IsOpen (e ⁻¹' S))
    (hE : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] Λ) (x : X),
      ContinuousOn (fun t => E (e t) x) (e ⁻¹' S))
    (hD : IsOpenDenseInCoordinates D) {a b : Fin m → Λ → ℂ}
    (hb : ∀ i, IsMeromorphicInCoordinatesOn (b i) D')
    (haeq : ∀ lam ∈ S, ∀ x, E lam x = ∑ i, a i lam * ψ i x)
    (hbeq : ∀ lam ∈ D ∩ D', ∀ x, ∑ i, b i lam * ψ i x = ∑ i, a i lam * ψ i x) :
    ∃ c : Fin m → Λ → ℂ, (∀ i, IsMeromorphicInCoordinatesOn (c i) D') ∧
      ∀ lam ∈ S, ∀ x, E lam x = ∑ i, c i lam * ψ i x := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hempty | hnonempty
  · exact ⟨a, fun i => isEmptyElim i, haeq⟩
  obtain ⟨i₀⟩ := hnonempty
  let c (i : Fin m) (lam : Λ) := if lam ∈ D' then b i lam else a i lam
  refine ⟨c, fun i => (hb i).congr_mono (hb i).isOpenDenseInCoordinates Set.Subset.rfl
    (fun _ h => ite_eq_left h), fun lam hlam x => ?_⟩
  by_cases hlam' : lam ∈ D'
  · have := (hb i₀).1
    let n := Module.finrank ℂ Λ
    let e : (Fin n → ℂ) ≃ₗ[ℂ] Λ := (Module.finBasis ℂ Λ).equivFun.symm
    let W := e ⁻¹' S ∩ e ⁻¹' D'
    let f (s : Fin n → ℂ) := E (e s) x
    let g (s : Fin n → ℂ) := ∑ i, b i (e s) * ψ i x
    have hWo : IsOpen W := (hS n e).inter ((hb i₀).2 n e).1
    have hfc : ContinuousOn f W := (hE n e x).mono Set.inter_subset_left
    have hgc : ContinuousOn g W := continuousOn_finsetSum _ fun i _ =>
      ((isHolomorphicOn_iff_differentiableOn_scalar.1 ((hb i).2 n e).2.2.1).continuousOn.mul
        continuousOn_const).mono Set.inter_subset_right
    have heq : Set.EqOn f g (W ∩ e ⁻¹' D) := fun s hs =>
      (haeq (e s) hs.1.1 x).trans (hbeq (e s) ⟨hs.2, hs.1.2⟩ x).symm
    have hall := Set.EqOn.of_subset_closure heq hfc hgc Set.inter_subset_left
      ((hD n e).2.open_subset_closure_inter hWo)
    have hs : e.symm lam ∈ W := by simpa [W] using And.intro hlam hlam'
    simpa [c, hlam', f, g] using hall hs
  · simpa [c, hlam'] using haeq lam hlam x

private theorem characterRestrict_rightInverse {F : Type} [Field F]
    {L H : GroupScheme (Spec (CommRingCat.of F))} (j : L ⟶ H) (q : H ⟶ L)
    (hq : j ≫ q = 𝟙 L) : Function.RightInverse (characterRestrict q) (characterRestrict j) := by
  intro χ
  change ((characterRestrict j).comp (characterRestrict q)) χ = χ
  rw [← characterRestrict_comp, hq, characterRestrict_id]
  rfl

private theorem exists_realWeylParameter_equiv {F : Type} [Field F] [NumberField F]
    {P Q M M' : GroupScheme (Spec (CommRingCat.of F))} (l : M ⟶ P) (l' : M' ⟶ Q)
    (hl : IsRationalLeviSubgroup l) (hl' : IsRationalLeviSubgroup l') (c : M' ⟶ M) [IsIso c]
    (π' : Q ⟶ M') (hπ' : l' ≫ π' = 𝟙 M') :
    ∃ e : RealCharacterParameter F P ≃ₗ[ℝ] RealCharacterParameter F Q,
      e.toLinearMap = realWeylParameter l c π' := by
  have hc : Function.Bijective (characterRestrict c) :=
    ⟨(characterRestrict_rightInverse (inv c) c (IsIso.inv_hom_id c)).injective,
      (characterRestrict_rightInverse c (inv c) (IsIso.hom_inv_id c)).surjective⟩
  have hπ := characterRestrict_rightInverse l' π' hπ'
  have hπbij : Function.Bijective (characterRestrict π') :=
    ⟨hπ.injective, fun χ => ⟨characterRestrict l' χ,
      hl'.characterRestrict_bijective.injective (hπ _)⟩⟩
  let eZ := AddEquiv.ofBijective (characterRestrict (π' ≫ c ≫ l)) (by
    rw [characterRestrict_comp, characterRestrict_comp]
    exact hπbij.comp (hc.comp hl.characterRestrict_bijective))
  refine ⟨AlgebraTensorModule.congr (LinearEquiv.refl ℝ ℝ) eZ.toIntLinearEquiv, ?_⟩
  apply AlgebraTensorModule.ext
  intro s χ
  simp [realWeylParameter, eZ]

/-- In the regular region the actual intertwining integral carries `A²_P` into `A²_Q`. -/
def IntertwiningRegularSquareIntegrableStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine Q.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a') (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType Q.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsIso (subgroupMultiplication l' iV) →
    l' ≫ π' = 𝟙 M' → IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc q iV l'
          (hK.intertwiningOperator hK' iU l iV c π' w φ lam)

/-- Regular preservation, meromorphic continuation and imaginary unitarity suffice for the target. -/
def IntertwiningSquareIntegrableExpansionReductionStatement : Prop :=
  IntertwiningRegularSquareIntegrableStatement → IntertwiningMeromorphicContinuationStatement.{0} →
    IntertwiningImaginaryUnitarityStatement → IntertwiningSquareIntegrableExpansionStatement

/-- Refine the continuation to the square-integrable submodule, then extend agreement with the
unitarity expansion by continuity throughout the regular portion of its holomorphy domain. -/
theorem intertwiningSquareIntegrableExpansionReduction :
    IntertwiningSquareIntegrableExpansionReductionStatement := by
  classical
  intro hL2 hM hU F _ _ G P M U Q M' V A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT
    q _ iV l' _ a' r' π' w c hG hUR hVR hMul hπ hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType Q.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
  obtain ⟨k, ψ, coeff, D, -, hcoeff, R₁, hR₁⟩ := hM F G P M U Q M' V A p iU l a r hA hT q
    iV l' π' w c hG hUR r'.isCompatible.parabolic hVR r'.isCompatible.levi hMul hπ hw K hK hK'
    rho hsmooth hcalc φ hmax hrho hφ.1
  rcases isEmpty_or_nonempty (Fin k) with hempty | hnonempty
  · exact ⟨k, ψ, coeff, Set.univ, fun i => isEmptyElim i, Set.subset_univ _,
      fun i => isEmptyElim i, R₁, hR₁⟩
  obtain ⟨i₀⟩ := hnonempty
  obtain ⟨R₂, hR₂⟩ := hL2 F G P M U Q M' V A A' p iU l a r hA hT q iV l' a' r' π' w c
    hG hUR hVR hMul hπ hw K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₃, hR₃⟩ := intertwiningRegularHolomorphy F G P M U Q M' V A p iU l a r hA hT q
    iV l' π' w c hG hUR r'.isCompatible.parabolic hVR r'.isCompatible.levi hMul hw K hK hK'
    rho hsmooth hcalc φ hmax hrho hφ.1
  let R := max R₁ (max R₂ R₃)
  have h₁ : R₁ ≤ R := le_max_left _ _
  have h₂ : R₂ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  let S := {lam | r.IsRegularParameter hA hT R lam}
  let E := hK.intertwiningOperator hK' iU l iV c π' w φ
  let B := squareIntegrableInducedForms q l' hK'.isCompact rho hsmooth hcalc iV
  have := (hcoeff i₀).1
  have hD := (hcoeff i₀).isOpenDenseInCoordinates
  obtain ⟨m, v, vcoeff, hv, ha, hAeq⟩ :=
    exists_meromorphic_expansion_in_submodule B ψ coeff hD hcoeff
      (E := E) (S := S) (fun lam hlam => hR₁ lam fun α hα => h₁.trans_lt (hlam α hα))
      (fun lam hlam => hR₂ lam fun α hα => h₂.trans_lt (hlam α hα))
  obtain ⟨μM, hμM, hμMcomp⟩ :=
    iwasawaCompatibleMeasureExistence F G P M U A p iU l a r hG hUR K hK hmax
  obtain ⟨μM', hμM', hμM'comp⟩ :=
    iwasawaCompatibleMeasureExistence F G Q M' V A' q iV l' a' r' hG hVR K hK' hmax
  have := hw.isIso
  obtain ⟨wR, hwR⟩ := exists_realWeylParameter_equiv l l' r.isCompatible.levi
    r'.isCompatible.levi c π' hπ
  have := (r.rationalCharacters_free_finite hG).2
  have : FiniteDimensional ℝ (RealCharacterParameter F P) := Module.Finite.base_change ℤ ℝ _
  let n := Module.finrank ℝ (RealCharacterParameter F P)
  let e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P :=
    (Module.finBasis ℝ (RealCharacterParameter F P)).equivFun.symm
  obtain ⟨β, hβc, hβcs, hβint⟩ := BoundedWavePacket.exists_weight n
  obtain ⟨vcoeff', D', hImag, ha', hAgree, -⟩ := hU F G P M U Q M' V A p iU l a r hA hT q iV l' π'
    w c hG hUR r'.isCompatible.parabolic hVR r'.isCompatible.levi hMul hπ hw K hK hK'
    rho hsmooth hcalc hmax hrho μM μM' hμMcomp hμM'comp e (e.trans wR)
    (fun x => DFunLike.congr_fun hwR (e x)) β β hβc hβcs hβint hβc hβcs hβint 1 m
    (fun _ => φ) (fun _ => v) (fun _ => vcoeff) D (fun _ => hφ) (fun _ => hv) (fun _ => ha)
    (fun _ => ⟨R, hAeq⟩)
  obtain ⟨b, hb, hBeq⟩ := glue_regular_expansion v (E := E) (S := S)
    (fun _ e => isOpen_setOf_isRegularParameter r hA hT hG R e)
    (fun n e g => (hR₃ n e g).continuousOn.mono fun s hs α hα => h₃.trans_lt (hs α hα))
    hD (ha' 0) hAeq (hAgree 0)
  exact ⟨m, v, b, D', hv, hImag, hb, R, hBeq⟩

end Langlands.Global
