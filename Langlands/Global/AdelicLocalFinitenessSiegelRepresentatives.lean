import Langlands.Global.AdelicHeightPowerPolynomialBound
import Langlands.Global.AdelicIwasawaChamberBounds
import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.AdelicLocalFinitenessChamberWeights
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.Global.AdelicSiegelNormOne
import Langlands.Global.AdelicSiegelNormMinimalityProof
import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicPositiveTorusSplitComponentStatement

/-! # Rational representatives in a Siegel set with polynomially bounded height

Every point `x` of `G(𝔸)` has a rational left translate `q x = z s` with `s` in a weak Siegel
product covering the norm-one group and `z` the image of a positive point of the maximal split
torus whose logarithm vanishes on the simple roots: the finite component of `q x` lies in a fixed
compact set, its height is polynomially bounded by that of `x`, and its minimal-parabolic height
has simple-root coordinates bounded below by the Siegel threshold.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

private instance : IsClosedImmersion (𝟙 G : G ⟶ G).hom.hom.left := by
  change IsClosedImmersion (𝟙 G.X.left)
  infer_instance

/-- The trivial subgroup is an Iwasawa subgroup for the identity of `G`. -/
theorem isIwasawaCompact_id : IsIwasawaCompact (𝟙 G) (⊥ : Subgroup (AdelicGroupPoints F G)) := by
  refine ⟨?_, ?_⟩
  · simp
  · ext g
    simp only [Set.mem_mul, Set.mem_range, SetLike.mem_coe, Subgroup.mem_bot, Set.mem_univ,
      iff_true]
    exact ⟨g, ⟨g, by simp⟩, 1, rfl, mul_one g⟩

/-- The Iwasawa height for the identity of `G` is the ambient logarithm `H_G`. -/
theorem height_isIwasawaCompact_id (g : AdelicGroupPoints F G) :
    (isIwasawaCompact_id (F := F) (G := G)).height g = characterLog F G g := by
  have h := (isIwasawaCompact_id (F := F) (G := G)).height_map g
  simpa using h

/-- The ambient logarithm of an inverse is the negative logarithm. -/
theorem characterLog_inv (g : AdelicGroupPoints F G) :
    characterLog F G g⁻¹ = -characterLog F G g := by
  have h := characterLog_mul F G g⁻¹ g
  rw [inv_mul_cancel, characterLog_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

variable [IsAffineHom G.X.hom]

/-- For a connected reductive `G`, a real linear form `φ` on the real character dual satisfies
`exp |φ(H_G(g))| ≤ A · ht(g)^r` for the ambient logarithm `H_G` and the adelic height of a
closed matrix embedding. -/
theorem exists_exp_abs_le_adelicHeight (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (φ : RealCharacterDual F G →ₗ[ℝ] ℝ) :
    ∃ A r : ℝ, 0 < A ∧ 0 ≤ r ∧ ∀ g : AdelicGroupPoints F G,
      Real.exp |φ (characterLog F G g)| ≤ A * adelicHeight F G rho g ^ r := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨hFree, hFin⟩ := rationalCharacters_free_finite_of_smooth G
  let : Module.Free ℤ (rationalCharacters G) := hFree
  let : Module.Finite ℤ (rationalCharacters G) := hFin
  obtain ⟨ν, hν⟩ := realParameterPairing_surjective F G φ
  let hK := isIwasawaCompact_id (F := F) (G := G)
  obtain ⟨-, hexp, -⟩ := hK.iwasawaFiniteMaximumWeight rho (Finset.univ : Finset Bool)
    Finset.univ_nonempty (fun b => if b then ν else -ν)
  obtain ⟨A, r, hA, hr, hb⟩ := hexp hN hrho
  refine ⟨A, r, hA, hr, fun g => (Real.exp_le_exp.mpr ?_).trans (hb g)⟩
  rw [height_isIwasawaCompact_id]
  unfold finiteMaximumLogWeight
  have h1 := Finset.le_sup' (fun b : Bool => realParameterPairing F G (if b then ν else -ν)
    (characterLog F G g)) (Finset.mem_univ true)
  have h2 := Finset.le_sup' (fun b : Bool => realParameterPairing F G (if b then ν else -ν)
    (characterLog F G g)) (Finset.mem_univ false)
  simp only [ite_true, Bool.false_eq_true, ite_false, map_neg, LinearMap.neg_apply, hν] at h1 h2
  exact abs_le'.mpr ⟨h1, h2⟩

/-- **Torus factor with prescribed logarithm.** Let `T` be a split torus with `i : T → G` and
`L` a real linear section of the map of real character duals induced by `i`. There are `A > 0`
and `r ≥ 0` such that every `g ∈ G(𝔸)` is `i(t) · g¹` with `t` in the positive torus `A_T`,
`log t = L(H_G(g))`, `g¹` of norm one and `ht(i(t)) ≤ A ht(g)^r`. -/
theorem exists_torusFactor (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp)
    (L : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F T.toGrp)
    (hL : ∀ l, realCharacterDualMap F T.toGrp G i (L l) = l) :
    ∃ A r : ℝ, 0 < A ∧ 0 ≤ r ∧ ∀ g : AdelicGroupPoints F G,
      ∃ t : PositiveRealTorus.intrinsicSubgroup F T,
        characterLog F T.toGrp t.val = L (characterLog F G g) ∧
        (map F T.toGrp G i t.val)⁻¹ * g ∈ normOneSubgroup F G ∧
        adelicHeight F G rho (map F T.toGrp G i t.val) ≤ A * adelicHeight F G rho g ^ r := by
  obtain ⟨I, _, ⟨e₀⟩⟩ := hT
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨r₀, ⟨σ⟩⟩ : ∃ r₀ : ℕ, Nonempty (ULift.{u} (Fin r₀) ≃ I) :=
    ⟨Fintype.card I, ⟨Equiv.ulift.trans (Fintype.equivFin I).symm⟩⟩
  let e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r₀)) :=
    e₀ ≪≫ LocalSplitCell.exponentEquivGroupIso _ (LinearEquiv.funCongrLeft ℤ ℤ σ)
  obtain ⟨Cb, hCb, kb, hb⟩ := exists_adelicHeight_map_full_le F rho hN T i e
  let φ (k : ULift.{u} (Fin r₀)) : RealCharacterDual F G →ₗ[ℝ] ℝ :=
    (dualEval F T.toGrp (PositiveRealTorus.coordinateCharacter F _ T e k)).comp L
  choose A r hA hr hbd using fun k => exists_exp_abs_le_adelicHeight hG rho hN hrho (φ k)
  let Am : ℝ := 1 + ∑ k, A k
  let rm : ℝ := ∑ k, r k
  have hAm : 1 ≤ Am := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hA k).le)
  have hrm : 0 ≤ rm := Finset.sum_nonneg fun k _ => hr k
  have hbound (k : ULift.{u} (Fin r₀)) (g : AdelicGroupPoints F G) :
      Real.exp |φ k (characterLog F G g)| ≤ Am * adelicHeight F G rho g ^ rm := by
    have hH := one_le_adelicHeight F G rho hN g
    refine (hbd k g).trans (mul_le_mul ?_ ?_ (Real.rpow_nonneg (zero_le_one.trans hH) _)
      (zero_le_one.trans hAm))
    · exact (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ k)).trans
        (le_add_of_nonneg_left zero_le_one)
    · exact Real.rpow_le_rpow_of_exponent_le hH
        (Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ k))
  refine ⟨max Cb 1 * Am ^ (r₀ * kb), rm * ((r₀ * kb : ℕ) : ℝ),
    mul_pos (zero_lt_one.trans_le (le_max_right _ _)) (pow_pos (zero_lt_one.trans_le hAm) _),
    mul_nonneg hrm (Nat.cast_nonneg _), fun g => ?_⟩
  set ℓ := L (characterLog F G g) with hℓ
  let t := PositiveRealTorus.positiveExp F T _ e ℓ
  have htlog : characterLog F T.toGrp t.val = ℓ :=
    PositiveRealTorus.characterLog_full_logParameters F T _ e ℓ
  refine ⟨t, htlog, ?_, ?_⟩
  · apply (characterLog_eq_zero_iff F G _).mp
    rw [characterLog_mul, characterLog_inv, characterLog_map, htlog, hℓ, hL, neg_add_cancel]
  · set H := adelicHeight F G rho g with hHdef
    have hH : 1 ≤ H := one_le_adelicHeight F G rho hN g
    have hsize : ((positiveSize (PositiveRealTorus.logParameters F T _ e ℓ) : ℝ≥0) : ℝ) ≤
        (Am * H ^ rm) ^ r₀ := by
      unfold positiveSize
      rw [NNReal.coe_prod]
      calc ∏ k, ((max ((PositiveRealTorus.logParameters F T _ e ℓ k : ℝ≥0ˣ) : ℝ≥0)
            (((PositiveRealTorus.logParameters F T _ e ℓ k)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ≥0) : ℝ)
          ≤ ∏ _k : ULift.{u} (Fin r₀), Am * H ^ rm := by
            refine Finset.prod_le_prod₀ (fun k _ => NNReal.coe_nonneg _) fun k _ => ?_
            have hd : (1 : ℝ) ≤ (Module.finrank ℚ F : ℝ) := by
              exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
            set a := ℓ (PositiveRealTorus.coordinateCharacter F _ T e k) with ha
            have hφ : φ k (characterLog F G g) = a := rfl
            have habs : |a / (Module.finrank ℚ F : ℝ)| ≤ |a| := by
              rw [abs_div, abs_of_pos (zero_lt_one.trans_le hd)]
              exact div_le_self (abs_nonneg _) hd
            have hexp : Real.exp |a / (Module.finrank ℚ F : ℝ)| ≤ Am * H ^ rm :=
              (Real.exp_le_exp.mpr habs).trans (hφ ▸ hbound k g)
            rw [NNReal.coe_max]
            refine max_le ?_ ?_
            · exact (Real.exp_le_exp.mpr (le_abs_self _)).trans hexp
            · exact (Real.exp_le_exp.mpr (neg_le_abs _)).trans hexp
        _ = (Am * H ^ rm) ^ r₀ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin]
    have hmap : adelicHeight F G rho (map F T.toGrp G i t.val) ≤
        Cb * ((positiveSize (PositiveRealTorus.logParameters F T _ e ℓ) : ℝ≥0) : ℝ) ^ kb :=
      hb _
    have hpos : 0 ≤ Am * H ^ rm :=
      mul_nonneg (zero_le_one.trans hAm) (Real.rpow_nonneg (zero_le_one.trans hH) _)
    calc adelicHeight F G rho (map F T.toGrp G i t.val)
        ≤ Cb * ((positiveSize (PositiveRealTorus.logParameters F T _ e ℓ) : ℝ≥0) : ℝ) ^ kb := hmap
      _ ≤ max Cb 1 * ((Am * H ^ rm) ^ r₀) ^ kb := by
          refine mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) hsize _)
            (pow_nonneg (NNReal.coe_nonneg _) _) (zero_le_one.trans (le_max_right _ _))
      _ = max Cb 1 * Am ^ (r₀ * kb) * H ^ (rm * ((r₀ * kb : ℕ) : ℝ)) := by
          rw [← pow_mul, mul_pow, Real.rpow_mul (zero_le_one.trans hH), Real.rpow_natCast]
          ring

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- Points `z_j` of a torus with `β(z_j) = 1` for every `β` in a set `Δ` of characters, whose
ambient logarithms form a basis of the real character dual of `G`, give a linear section `L` of
the restriction of real duals along `i` whose values vanish on `Δ`. -/
theorem exists_rootTrivialSection {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (Δ : Set (characterLattice T)) {r : ℕ}
    (z : Fin r → AdelicGroupPoints F T.toGrp)
    (hzval : ∀ j, ∀ β ∈ Δ, Lie.characterValue β (z j) = 1)
    (hlin : LinearIndependent ℝ (fun j => characterLog F G (map F T.toGrp G i (z j))))
    (hspan : Submodule.span ℝ (Set.range fun j => characterLog F G (map F T.toGrp G i (z j))) =
      ⊤) :
    ∃ L : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F T.toGrp,
      (∀ l, realCharacterDualMap F T.toGrp G i (L l) = l) ∧ ∀ l, ∀ α ∈ Δ, L l α = 0 := by
  let b := Module.Basis.mk hlin hspan.ge
  let L : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F T.toGrp :=
    b.constr ℝ fun j => characterLog F T.toGrp (z j)
  refine ⟨L, fun l => ?_, fun l α hα => ?_⟩
  · have h : (realCharacterDualMap F T.toGrp G i).comp L = LinearMap.id := by
      refine b.ext fun j => ?_
      have hb : b j = characterLog F G (map F T.toGrp G i (z j)) :=
        Module.Basis.mk_apply hlin hspan.ge j
      rw [LinearMap.comp_apply, LinearMap.id_apply,
        show L (b j) = characterLog F T.toGrp (z j) from b.constr_basis ℝ _ j, hb,
        characterLog_map]
    exact congrArg (fun f : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F G => f l) h
  · have h : (dualEval F T.toGrp α).comp L = 0 := by
      refine b.ext fun j => ?_
      rw [LinearMap.comp_apply, LinearMap.zero_apply,
        show L (b j) = characterLog F T.toGrp (z j) from b.constr_basis ℝ _ j]
      change characterLog F T.toGrp (z j) α = 0
      rw [PositiveRealTorus.characterLog_eq_log_characterValue, hzval j α hα, map_one]
      simp
    exact congrArg (fun f : RealCharacterDual F G →ₗ[ℝ] ℝ => f l) h

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

/-- The minimal-parabolic height of a point `n m a k` of a Siegel product (`n` in the standard
unipotent group, `m` a norm-one point of the standard Levi, `a` in the positive torus `A_{T₀}`,
`k ∈ K`) is the logarithm of the torus point `j(a)`, transported to the parabolic dual. -/
theorem height_siegelProduct (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
    (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    hK.height (map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) (m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) *
        positiveMap F G T i T₀ j a * k) =
      realCharacterDualMap F T.toGrp (Standard.parabolicScheme i ν ∅)
        (torusToStandardParabolic F G T i ν)
        (characterLog F T.toGrp (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val)) := by
  have hU : IsUnipotent (Standard.unipotentScheme i ν ∅) := hS.isUnipotent_standard F G T i ν T₀ j
  have hn : map F _ G (Standard.unipotentHom i ν ∅) n =
      map F _ G (Standard.parabolicHom i ν ∅) (map F _ _ (Standard.unipotentToParabolic i ν ∅) n) := by
    rw [← map_comp_apply_of_hom, Standard.unipotentToParabolic_comp]
  have hm : map F _ G (Standard.leviHom i ν ∅) (m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) =
      map F _ G (Standard.parabolicHom i ν ∅)
        (map F _ _ (Standard.leviToParabolic i ν ∅) (m : AdelicGroupPoints F _)) := by
    rw [← map_comp_apply_of_hom, Standard.leviToParabolic_comp]
  have ha : positiveMap F G T i T₀ j a =
      map F _ G (Standard.parabolicHom i ν ∅) (map F T.toGrp _ (torusToStandardParabolic F G T i ν)
        (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val)) := by
    change map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) a.val = _
    conv_lhs => rw [← torusToStandardParabolic_comp F G T i ν]
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hK.height_mul_right _ hk, hn, hm, ha, ← map_mul, ← map_mul, hK.height_map,
    characterLog_mul, characterLog_mul, characterLog_map, characterLog_map, characterLog_map,
    characterLog_eq_zero_of_isUnipotent hU, (characterLog_eq_zero_iff F _ _).mpr m.property,
    map_zero, map_zero, zero_add, zero_add]

/-- Rational representatives controlled by `Ω`, `M`, `r` and `θ`: every `x ∈ G(𝔸)` has a rational
point `q` such that the finite component of `q x` lies in `Ω`, `ht(q x) ≤ M ht(x)^r`, and the
minimal-parabolic height of `q x` is the image of a functional `h` on the real character dual of
the torus with `θ ≤ h(α)` for every simple root `α`. -/
def HasSiegelRepresentatives {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (Ω : Set (FiniteAdelicGroupPoints F G)) (M r θ : ℝ) : Prop :=
  ∀ x : AdelicGroupPoints F G, ∃ q : RationalGroupPoints F G,
    AdelicGroupPoints.finite F G (rational F G q * x) ∈ Ω ∧
    RepresentationGrowth.adelicHeight F G rho (rational F G q * x) ≤
      M * RepresentationGrowth.adelicHeight F G rho x ^ r ∧
    ∃ h : RealCharacterDual F T.toGrp,
      hK.height (rational F G q * x) = realCharacterDualMap F T.toGrp
        (Standard.parabolicScheme i ν ∅) (torusToStandardParabolic F G T i ν) h ∧
      ∀ α ∈ simpleRelativeRoots i ν, θ ≤ h α

/-- **Rational representatives in a Siegel set with polynomial height.** Let the weak Siegel
product of `C` and threshold `t₀` cover the norm-one group modulo `G(F)`, let `L` be a real linear
section of the restriction of real character duals along `i` whose values vanish on the simple
roots, and let the images of the positive torus points whose logarithms vanish on the simple
roots be central. Then there are a compact `Ω ⊆ G(𝔸_f)` and `M > 0`, `r ≥ 0` such that every
`x ∈ G(𝔸)` has a rational `q` with `q x` having finite component in `Ω`, height at most
`M ht(x)^r`, and minimal-parabolic height the image of a torus functional `h` with
`h(α) ≥ log t₀` for every simple root `α`. -/
theorem exists_siegelRepresentatives {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hrho : IsClosedSubgroup rho) (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t₀ : ℝ≥0ˣ) (hcover : IsSiegelCover F G T i ν T₀ j C t₀)
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) C.compactSubgroup)
    (L : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F T.toGrp)
    (hL : ∀ l, realCharacterDualMap F T.toGrp G i (L l) = l)
    (hLroot : ∀ l, ∀ α ∈ simpleRelativeRoots i ν, L l α = 0)
    (hcentral : ∀ a : PositiveRealTorus.intrinsicSubgroup F T,
      (∀ α ∈ simpleRelativeRoots i ν, characterLog F T.toGrp a.val α = 0) →
        ∀ x : AdelicGroupPoints F G, Commute (map F T.toGrp G i a.val) x) :
    ∃ (Ω : Set (FiniteAdelicGroupPoints F G)) (M r : ℝ), IsCompact Ω ∧ 0 < M ∧ 0 ≤ r ∧
      HasSiegelRepresentatives rho hK Ω M r (Real.log ((t₀ : ℝ≥0) : ℝ)) := by
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus T.toGrp := hS.1.isSplitSubtorus.1
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨cm, em, hm⟩ := siegelNormMinimalityStatement F G rho hG hrho hN T i ν T₀ j hS C t₀
  obtain ⟨A, r, hA, hr, hz⟩ := exists_torusFactor hG rho hN hrho i hT L hL
  obtain ⟨Ω, hΩ, hΩs⟩ := exists_isCompact_finite_weakSiegelProduct F G T i ν T₀ j hT₀
    (canonicalStandardFactors F G T i ν) C t₀
  set H := RepresentationGrowth.adelicHeight F G rho with hHdef
  have hH1 (x : AdelicGroupPoints F G) : 1 ≤ H x :=
    RepresentationGrowth.one_le_adelicHeight F G rho hN x
  have hH0 (x : AdelicGroupPoints F G) : 0 ≤ H x := zero_le_one.trans (hH1 x)
  set cm' : ℝ := max cm 1 with hcm'
  have hcm0 : 0 < cm' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Ω, cm' * A ^ (1 + em), r * (1 + em) + em, hΩ, mul_pos hcm0 (pow_pos hA _),
    add_nonneg (mul_nonneg hr (by positivity)) (Nat.cast_nonneg _), fun x => ?_⟩
  obtain ⟨t, htlog, ht1, htH⟩ := hz x
  set z := map F T.toGrp G i t.val with hzdef
  have hzc : ∀ y, Commute z y := hcentral t fun α hα => by rw [htlog]; exact hLroot _ α hα
  have hmem : z⁻¹ * x ∈ (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
      weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t₀ := by
    rw [hcover.2]
    exact ht1
  obtain ⟨_, ⟨q₀, rfl⟩, s, hs, hrs⟩ := hmem
  replace hrs : rational F G q₀ * s = z⁻¹ * x := hrs
  have hx : rational F G q₀⁻¹ * x = z * s := by
    have hg : x = z * (rational F G q₀ * s) := by rw [hrs, mul_inv_cancel_left]
    calc
      rational F G q₀⁻¹ * x = rational F G q₀⁻¹ * z * (rational F G q₀ * s) := by
        rw [hg, mul_assoc]
      _ = z * rational F G q₀⁻¹ * (rational F G q₀ * s) := by
        rw [← (hzc (rational F G q₀⁻¹)).eq]
      _ = z * s := by rw [map_inv, mul_assoc, inv_mul_cancel_left]
  refine ⟨q₀⁻¹, ?_, ?_, ?_⟩
  · have hzf : AdelicGroupPoints.finite F G z = 1 := by
      have := RepresentationGrowth.finite_positivePointMap F T i hT t
      rwa [PositiveRealTorus.positivePointMap_apply] at this
    rw [hx, map_mul, hzf, one_mul]
    exact hΩs s hs
  · have hHz : H z ≤ A * H x ^ r := htH
    have hHg₁ : H (rational F G q₀ * s) ≤ A * H x ^ r * H x := by
      rw [hrs]
      calc
        H (z⁻¹ * x) ≤ H z⁻¹ * H x := RepresentationGrowth.adelicHeight_mul_le F G rho hN _ _
        _ ≤ A * H x ^ r * H x := by
          rw [show H z⁻¹ = H z from RepresentationGrowth.adelicHeight_inv F G rho z]
          exact mul_le_mul_of_nonneg_right hHz (hH0 x)
    have hHs : H s ≤ cm' * (A * H x ^ r * H x) ^ em := by
      calc
        H s ≤ cm * H (rational F G q₀ * s) ^ em := hm s hs q₀
        _ ≤ cm' * H (rational F G q₀ * s) ^ em :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hH0 _) _)
        _ ≤ cm' * (A * H x ^ r * H x) ^ em :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH0 _) hHg₁ em) hcm0.le
    have hx0 : 0 < H x := zero_lt_one.trans_le (hH1 x)
    calc
      H (rational F G q₀⁻¹ * x) = H (z * s) := by rw [hx]
      _ ≤ H z * H s := RepresentationGrowth.adelicHeight_mul_le F G rho hN _ _
      _ ≤ (A * H x ^ r) * (cm' * (A * H x ^ r * H x) ^ em) :=
        mul_le_mul hHz hHs (hH0 s) (mul_nonneg hA.le (Real.rpow_nonneg (hH0 x) _))
      _ = cm' * A ^ (1 + em) * H x ^ (r * (1 + em) + em) := by
        have e1 : (H x ^ r) ^ em = H x ^ (r * em) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        have e2 : H x ^ (r * (1 + em) + em) = H x ^ r * H x ^ (r * em) * H x ^ em := by
          rw [Real.rpow_add hx0, mul_add, mul_one, Real.rpow_add hx0, Real.rpow_natCast]
        rw [mul_pow, mul_pow, e1, e2, pow_add, pow_one]
        ring
  · obtain ⟨n, -, m, -, a, ha, k, hk, rfl⟩ := (mem_productSet_iff F G T i ν
      (canonicalStandardFactors F G T i ν) C T₀ j
      (PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t₀) s).mp hs
    refine ⟨L (characterLog F G x) +
      characterLog F T.toGrp (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val), ?_, ?_⟩
    · have hzmap : z = map F _ G (Standard.parabolicHom i ν ∅)
          (map F T.toGrp _ (torusToStandardParabolic F G T i ν) t.val) := by
        rw [hzdef]
        conv_lhs => rw [← torusToStandardParabolic_comp F G T i ν]
        simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
          Category.assoc]
      rw [hx, hzmap, mul_assoc, mul_assoc, ← mul_assoc (map F _ G _ n), ← mul_assoc
        (map F _ G _ n * _), hK.height_map_mul, characterLog_map, htlog, map_add]
      congr 1
      exact height_siegelProduct hS hK n m a hk
    · intro α hα
      have hadd : (L (characterLog F G x) + characterLog F T.toGrp
          (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val)) α =
          L (characterLog F G x) α + characterLog F T.toGrp
            (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val) α := rfl
      rw [hadd, hLroot _ α hα, zero_add]
      have hle : t₀ ≤ PositiveRealTorus.normCharacter F T₀ (j ≫ α) a.val := ha α hα
      have hpull := PositiveRealTorus.normCharacter_pullback F T₀ T j α a.val
      change Real.log ((t₀ : ℝ≥0) : ℝ) ≤
        Real.log ((PositiveRealTorus.normCharacter F T α
          (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val) : ℝ≥0) : ℝ)
      rw [← show PositiveRealTorus.normCharacter F T₀ (j ≫ α) a.val =
        PositiveRealTorus.normCharacter F T α
          (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val) from hpull]
      exact Real.log_le_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t₀.ne_zero))
        (by exact_mod_cast hle)

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The image of a point of the positive split component of the top index (the split center
of `G`) commutes with every point of `G(𝔸)`. -/
theorem commute_positiveSplitComponent_top (a : 𝓕.positiveSplitComponent 𝓕.top)
    (x : AdelicGroupPoints F G) : Commute (map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a) x := by
  obtain ⟨a', -, ha'⟩ := a.2
  have hfull := (standardCocharacter F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit 𝓕.ν
    𝓕.generic (simpleRelativeRoots 𝓕.i 𝓕.ν) subset_rfl).2 0
    (isStandardCocharacter_simple_zero 𝓕.i 𝓕.ν)
  have hp : standardParabolic 𝓕.i 𝓕.ν (simpleRelativeRoots 𝓕.i 𝓕.ν) = ⊤ := by
    simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.parabolic_trivialCocharacter] using hfull.1
  have hx : x ∈ (SubgroupFunctor.range (𝓕.p 𝓕.top)).carrier _ := by
    rw [(𝓕.isCompatible 𝓕.top).parabolic_eq]
    change x ∈ (standardParabolic 𝓕.i 𝓕.ν (simpleRelativeRoots 𝓕.i 𝓕.ν)).carrier _
    rw [hp]
    trivial
  have hcomm := 𝓕.commutator_mem_radical_of_splitComponent 𝓕.top _ a' hx
  let b := map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a
  have haG : b = map F (𝓕.A 𝓕.top).toGrp G (𝓕.a 𝓕.top ≫ 𝓕.l 𝓕.top ≫ 𝓕.p 𝓕.top) a' := by
    change map F (𝓕.A 𝓕.top).toGrp (𝓕.P 𝓕.top) (𝓕.a 𝓕.top ≫ 𝓕.l 𝓕.top) a' =
      (a : AdelicGroupPoints F (𝓕.P 𝓕.top)) at ha'
    change map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a = _
    rw [← ha', ← map_comp_apply_of_hom, Category.assoc]
  have hrad : x * b * x⁻¹ * b⁻¹ ∈ (standardUnipotent 𝓕.i 𝓕.ν
      (simpleRelativeRoots 𝓕.i 𝓕.ν)).carrier _ := by
    rw [haG]
    have h := hcomm
    rw [𝓕.range_radical_eq_standardUnipotent] at h
    exact h
  rw [standardUnipotent_simple_eq_bot] at hrad
  have h1 : x * b * x⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hrad
  have h2 : x * b = b * x := by
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h1, one_mul]
  exact h2.symm

/-- A positive point of the maximal split torus whose logarithm vanishes on the simple roots
maps to a central point of `G(𝔸)`, given that such points lie in the positive split component
of the top index (`PositiveTorusSplitComponentStatement`). -/
theorem commute_of_rootTrivial (hsplit : PositiveTorusSplitComponentStatement.{u})
    (t : PositiveRealTorus.intrinsicSubgroup F 𝓕.T)
    (ht : ∀ α ∈ simpleRelativeRoots 𝓕.i 𝓕.ν, characterLog F 𝓕.T.toGrp t.val α = 0)
    (x : AdelicGroupPoints F G) : Commute (map F 𝓕.T.toGrp G 𝓕.i t.val) x := by
  obtain ⟨I, _, ⟨e⟩⟩ := 𝓕.maximalSplit.isSplitSubtorus.1
  let : Fintype I := Fintype.ofFinite I
  have hmem : t.val ∈ PositiveRealTorus.subgroup F I 𝓕.T e := by
    rw [PositiveRealTorus.subgroup_eq_intrinsicSubgroup]
    exact t.property
  obtain ⟨y, hy⟩ := (PositiveRealTorus.mem_subgroup_iff F I 𝓕.T e _).mp hmem
  have hval : ∀ β ∈ (𝓕.top).1, Lie.characterValue β t.val = 1 := by
    intro β hβ
    have hlog := ht β hβ
    rw [← hy, PositiveRealTorus.characterLog_full] at hlog
    have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := ne_of_gt (PositiveRealTorus.degree_pos F)
    have hl : Real.log ((PositiveRealTorus.positiveCharacter F I 𝓕.T e β y : ℝ≥0) : ℝ) = 0 :=
      (mul_eq_zero.mp hlog).resolve_left hd
    have hpos : (0 : ℝ) < ((PositiveRealTorus.positiveCharacter F I 𝓕.T e β y : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have h1 : PositiveRealTorus.positiveCharacter F I 𝓕.T e β y = 1 := by
      apply Units.ext
      apply NNReal.eq
      simpa using Real.eq_one_of_pos_of_log_eq_zero hpos hl
    rw [← hy, PositiveRealTorus.characterValue_full, h1, map_one]
  obtain ⟨a, ha, hmap⟩ := hsplit F G 𝓕 𝓕.top t.val t.property hval
  rw [← hmap]
  exact 𝓕.commute_positiveSplitComponent_top ⟨a, ha⟩ x

end Langlands.Global.StandardParabolicFamily
