import Langlands.Representation.Exponents.LeviJacquetOppositePairingStatement
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.Representation.Exponents.PresentationConeContractionStatement
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.Representation.Aubert.General.StableLiftDualityPairing

/-! # The opposite-Jacquet pairing from explicit structure statements

Renard 2026, VI.9.6, Proposition (printed p.202/PDF p.208), for represented parabolics
`P = MN` and `P̄ = M N̄` as in `LeviJacquetOppositePairingStatement`. The isomorphism
`E : r_{P̄}^G(π~) ≅ (r_P^G π)~` is the stable-lift duality of
`RationalPointFamily.exists_isStableLiftDuality_of_dynamic`, pulled back to `M(F)`. Its
pairing is evaluated at translates by `exists_compact_forall_stableLiftDualityPairing_translate_eq`,
and the compact subsets of `N(F)` it produces are conjugated into the stabilizer of the
functional by `PresentationConeContractionStatement` (Renard V.5.2 (iii)).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Large powers of an element of `C_A^{++}` lie in `C_A^+(ε)` when `Δ` is finite. -/
theorem exists_pow_mem_CAepsilon {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A : CommGroupScheme (Spec (CommRingCat.of k)))
    {Δ : Set (characterLattice A)} (hΔ : Δ.Finite) {t : rationalPoints A.toGrp}
    (ht : t ∈ CocharacterUniformizer.CAstrict k A Δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → t ^ j ∈ CocharacterUniformizer.CAepsilon k A Δ ε := by
  have hev : ∀ α ∈ Δ, ∀ᶠ j in Filter.atTop,
      CocharacterUniformizer.characterNorm k A α (t ^ j) < ε := by
    intro α hα
    have hpow : ∀ j : ℕ, CocharacterUniformizer.characterNorm k A α (t ^ j) =
        CocharacterUniformizer.characterNorm k A α t ^ j := by
      intro j
      simp [CocharacterUniformizer.characterNorm, map_pow]
    simp only [hpow]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _) (ht.2 α hα)).eventually
      (gt_mem_nhds hε)
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.1 ((Filter.eventually_all_finite hΔ).2 hev)
  exact ⟨j₀, fun j hj => ⟨Subgroup.pow_mem _ ht.1 j, hj₀ j hj⟩⟩

/-- The points of a split component of `M` are central in the literal Levi image. -/
theorem splitComponent_point_comm {k : Type u} [Field k]
    {G P M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {p : P ⟶ G} {m : M ⟶ P}
    {a : A.toGrp ⟶ M} (pres : ParabolicRootPresentation p m a) (t : rationalPoints A.toGrp) :
    ∀ y ∈ pointImage (m ≫ p),
      rationalPoints.map (m ≫ p) (rationalPoints.map a t) * y =
        y * rationalPoints.map (m ≫ p) (rationalPoints.map a t) := by
  rintro _ ⟨y, rfl⟩
  have hc := pres.isCompatible.splitComponent.isCentralSplitTorus.range_le_center ⟨t, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc y]

/-- The parabolic dynamic statement, the VI.9.1 uniform stabilization statement, the relative
root reflection and central split torus character statements, and the contraction statement
`PresentationConeContractionStatement` (Renard V.5.2 (iii)) together imply
`LeviJacquetOppositePairingStatement` (Renard VI.9.6, Proposition). This proposition records
the internal reduction; none of its five antecedents is asserted. -/
def LeviJacquetOppositePairingStructureStatement : Prop :=
  ParabolicDynamicStatement.{u} →
    RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
      RelativeRootReflectionExistenceStatement.{u} →
        CentralSplitTorusCharacterStatement.{u} →
          PresentationConeContractionStatement.{u} →
            LeviJacquetOppositePairingStatement.{u, v}

/-- `LeviJacquetOppositePairingStatement` (Renard VI.9.6, Proposition) follows from the
parabolic dynamic statement, the VI.9.1 uniform stabilization statement, the relative root
reflection and central split torus character statements, and the contraction statement
`PresentationConeContractionStatement` (Renard V.5.2 (iii)). -/
theorem leviJacquetOppositePairing_of_structure :
    LeviJacquetOppositePairingStructureStatement.{u, v} := by
  intro hPD hstab hRefl hCST hGeo k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
  let := leviPointTopology m hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  intro π
  -- The cocharacter of `P` and the dynamic descriptions of `N`, `M` and `N̄`.
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD dynamicGeometricUnipotentRadical hG
      hp hm
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hPχ hn
  have hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hMχ]
  have hNbar := pointImage_opposite_radical_eq_dynamic hPD oppositeDynamicParabolicUniqueness hG
    χ m hPχ hMχ hpbar hmbar hnbar hP hPP
  have hU := isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup hnbar.1.isClosedSubgroup
  have hO := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hMU₁ := pointImage_le_normalizer pbar mbar nbar hnbar
  have hMU : pointImage (m ≫ p) ≤
      Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)) := by
    rw [← hP]
    exact hMU₁
  have hMO := pointImage_le_normalizer p m n hn
  have hrec := fun x => RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    hRefl hCST hG χ _ _ _ hNbar hM hN hU hO hMU hMO x
  have hχ := fun x => closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter
    _ _ _ hU hO hMU hMO x (hrec x)
  obtain ⟨g, -, hB, Ψ, hΨ⟩ := RationalPointFamily.exists_isStableLiftDuality_of_dynamic hstab hG
    χ _ _ _ hNbar hM hN hU hO hMU hMO hrec
  -- The isomorphism `E` on `M(F)` and its pairing on classes.
  obtain ⟨E, hE⟩ := exists_pullback_iso_smoothDualPairing_eq
    (pointImage (nbar ≫ pbar)) (pointImage (n ≫ p)) (congrArg pointImage hP) hU hO hMU₁ hMU hMO
    (leviPointsEquiv pbar mbar hpbar hmbar) (leviPointsEquiv p m hp hm)
    (fun x => by simp only [leviPointsEquiv_apply_coe, hP]) Ψ π
  refine ⟨E, ?_⟩
  intro A a pres Δ rP pairing jN jNbar δ incM incG
  have := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hΔ : Δ.Finite := pres.finite_simpleRoots.sdiff.image _
  -- The identity for every `t ∈ C_A^+(ε)`, for a suitable `ε` depending on `x` and `ℓ`.
  have core : ∀ (x : π) (ℓ : π.contragredient), ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ CocharacterUniformizer.CAepsilon k A Δ ε,
        pairing (rP.representation (incM t) (jN x)) (jNbar ℓ) =
          δ (incM t) * smoothDualPairing π.representation ℓ (π.representation (incG t) x) := by
    intro x ℓ
    obtain ⟨C, hC, hCO, hCt⟩ :=
      exists_compact_forall_stableLiftDualityPairing_translate_eq hB hΨ hχ π x ℓ
    obtain ⟨L, hL⟩ := isSmooth_smoothContragredient π.representation ℓ
    obtain ⟨ε, hε, hεC⟩ := hGeo k G hG P M N p m n hp hm hn hmul A a pres C hC hCO
      (L : Set (rationalPoints G)) (L.isOpen.mem_nhds L.one_mem)
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hincG : incG t = rationalPoints.map (a ≫ m ≫ p) t := by
      simp only [incG, incM, leviPointsEquiv_apply_coe, rationalPoints.map_apply,
        Grp.comp_hom_hom, Category.assoc]
    have hmem : incG t ∈ pointImage (m ≫ p) := ⟨incM t, rfl⟩
    have hcomm : ∀ y ∈ pointImage (m ≫ p), incG t * y = y * incG t :=
      splitComponent_point_comm pres t
    have hfix : ∀ c ∈ C, smoothContragredient π.representation (incG t * c * (incG t)⁻¹) ℓ = ℓ := by
      intro c hc
      rw [hincG]
      exact Jacquet.apply_eq_of_mem_fixedVectors (smoothContragredient π.representation) hL (hεC t ht c hc)
    have hval := hCt (incG t) hmem hcomm hfix
    have hact : rP.representation (incM t) (jN x) = (δ (incM t)) • jN (π.representation (incG t) x) :=
      rfl
    rw [hact]
    let pr : Jacquet.Localization.Coinvariants π.representation (pointImage (n ≫ p)) 1 →ₗ[ℂ] ℂ :=
      smoothDualPairing rP.representation (SmoothRep.hom E.hom (jNbar ℓ))
    change pr ((δ (incM t)) • Jacquet.Localization.mk π.representation (pointImage (n ≫ p)) 1
      (π.representation (incG t) x)) = _
    rw [map_smul, smul_eq_mul]
    congr 1
    exact (hE ℓ _).trans hval
  refine ⟨fun x ℓ t ht => ?_, core⟩
  obtain ⟨ε, hε, h⟩ := core x ℓ
  obtain ⟨j₀, hj₀⟩ := exists_pow_mem_CAepsilon A hΔ ht hε
  exact ⟨j₀, fun j hj => h _ (hj₀ j hj)⟩

end Langlands.Aubert.General.RepresentedParabolic
