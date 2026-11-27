import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.LinearAlgebra.ObtuseBasisCones

/-! # Root and norm estimates on characteristic truncation shells -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra

variable {F : Type*} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)

/-- The convex set `C_T^Q` of Delorme §7 for `J = Δ₀^Q`. The weights of `J` and the roots
outside `J` act on the Levi and split-component projections of `X - T`, respectively. -/
def parabolicCharacteristicChamber (J : Global.StandardIndex F G i ν) (T₀ Tp : V T) : Set (V T) :=
  {X | X ∈ D.realCorootSpan ∧
    (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ eval T α (X - T₀)) ∧
    (∀ α ∈ (J : Set (characterLattice T)), ArthurRelative.weight hG hi ν D J α (X - Tp) ≤ 0) ∧
    (∀ α ∈ simpleRelativeRoots i ν \ (J : Set (characterLattice T)),
      0 < eval T α (ArthurRelative.levelProjection hG hi ν D J (X - Tp)))}

/-- The finite-dimensional shell `C_{T+S,T}^Q` of Delorme (7.13). -/
def characteristicShell (J : Global.StandardIndex F G i ν) (T₀ Tp S : V T) : Set (V T) :=
  characteristicChamber ν hG hi D T₀ (Tp + S) ∩ parabolicCharacteristicChamber hG hi D J T₀ Tp

private theorem sub_levelProjection_eq_sum (J : Set (characterLattice T)) (X : V T) :
    X - ArthurRelative.levelProjection hG hi ν D J X =
      ∑ j : ArthurRelative.standardIndex hG hi ν J,
        ArthurRelative.weight hG hi ν D J j.1 X • D.realCoroot ⟨j.1.1, j.1.2.1⟩ := by
  simp only [ArthurRelative.levelProjection, LinearMap.sub_apply, LinearMap.id_apply,
    sub_sub_cancel, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    ArthurRelative.weight_coe]

private theorem eq_sum_simpleCoroots (hν : IsGenericCocharacter i ν)
    {X : V T} (hX : X ∈ D.realCorootSpan) :
    X = ∑ j : ArthurRelative.standardIndex hG hi ν (simpleRelativeRoots i ν),
        ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) j.1 X •
          D.realCoroot ⟨j.1.1, j.1.2.1⟩ := by
  let J := simpleRelativeRoots i ν
  let p := ArthurRelative.levelProjection hG hi ν D J X
  have hd : X - p ∈ D.realCorootSpan := by
    apply (Submodule.span_mono (s := D.realCorootsOf J) (t := Set.range D.realCoroot) ?_)
      (ArthurRelative.sub_levelProjection_mem_span hG hi D J X)
    rintro _ ⟨α, _, rfl⟩
    exact ⟨α, rfl⟩
  have hp : p ∈ D.realCorootSpan := by
    simpa only [sub_sub_cancel] using D.realCorootSpan.sub_mem hX hd
  have hpc : p ∈ relativeCentralDirections i := by
    rw [← ArthurRelative.aSpace_simpleRelativeRoots hG hi hν]
    exact ArthurRelative.levelProjection_mem_rootAnnihilator hG hi D hν (fun _ h => h) X
  have hp0 : p = 0 :=
    Submodule.disjoint_def.mp (ArthurRelative.isCompl_relativeCentralDirections hG hi D).disjoint
      p hpc hp
  have he := sub_levelProjection_eq_sum (ν := ν) hG hi D J X
  change X - p = _ at he
  simpa only [hp0, sub_zero] using he

/-- Roots outside the Levi are larger at a point of `C_T^Q` than at the truncation
parameter, as in (7.15). -/
theorem eval_lt_of_mem_parabolicCharacteristicChamber (hν : IsGenericCocharacter i ν)
    {J : Global.StandardIndex F G i ν} {T₀ Tp X : V T}
    (hX : X ∈ parabolicCharacteristicChamber hG hi D J T₀ Tp)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν \ (J : Set (characterLattice T))) :
    eval T α Tp < eval T α X := by
  let H := X - Tp
  let p := ArthurRelative.levelProjection hG hi ν D J H
  have hp : 0 < eval T α p := hX.2.2.2 α hα
  have hsum : 0 ≤ eval T α (H - p) := by
    change 0 ≤ eval T α (H - ArthurRelative.levelProjection hG hi ν D J H)
    rw [sub_levelProjection_eq_sum hG hi D, map_sum]
    apply Finset.sum_nonneg
    intro j _
    have hj := (ArthurRelative.mem_standardIndex hG hi ν).mp j.2
    have hw : ArthurRelative.weight hG hi ν D J j.1 H ≤ 0 := hX.2.2.1 j.1 hj.2
    rw [map_smul, smul_eq_mul]
    apply mul_nonneg_of_nonpos_of_nonpos hw
    have hne : (⟨α, hα.1⟩ : simpleRelativeRoots i ν) ≠ ⟨j.1.1, hj.1⟩ := by
      intro he
      have he' : α = j.1.1 := congrArg Subtype.val he
      exact hα.2 (he' ▸ hj.2)
    rw [eval_eq_pair, D.pair_tmul_realCoroot, one_mul]
    exact_mod_cast D.simple_pairing_nonpos i ν hi.isSplitSubtorus.1
      (ArthurRelative.finite_relativeRoots hG hi) hν
      ⟨α, hα.1⟩ ⟨j.1.1, hj.1⟩ hne
  simp only [map_sub, H] at hsum
  linarith

variable {B : LinearMap.BilinForm ℝ (V T)} (hB : IsWeylInvariantCocharacterInnerProduct i B)

/-- The Euclidean norm from the chosen Weyl-invariant scalar product. -/
def cocharacterNorm (B : LinearMap.BilinForm ℝ (V T)) (X : V T) : ℝ := Real.sqrt (B X X)

include hi hB in
private theorem two_mul_form_realCoroot (α : relativeRoots i) (v : V T) :
    2 * B v (D.realCoroot α) = eval T α.1 v * B (D.realCoroot α) (D.realCoroot α) := by
  let w : relativeWeylGroup i := QuotientGroup.mk (D.representative α)
  have he (x : V T) : relativeWeylRealAction i w x = x - eval T α.1 x • D.realCoroot α := by
    simpa only [eval_eq_pair] using D.real_coreflection hi.isSplitSubtorus.1 α x
  have hn : relativeWeylRealAction i w (D.realCoroot α) = -D.realCoroot α := by
    rw [he, eval_eq_pair, D.pair_root_realCoroot]
    module
  have h := hB.2.2 w v (D.realCoroot α)
  rw [he v, hn] at h
  simp only [map_sub, map_neg, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  linarith

include hB in
private theorem form_nonneg_of_mem_characteristicChamber (hν : IsGenericCocharacter i ν)
    {T₀ U X : V T} (hU : U ∈ D.realCorootSpan)
    (hX : X ∈ characteristicChamber ν hG hi D T₀ U) :
    0 ≤ B (X - T₀) (U - X) := by
  rw [eq_sum_simpleCoroots hG hi D hν (D.realCorootSpan.sub_mem hU hX.1), map_sum]
  apply Finset.sum_nonneg
  intro j _
  have hj := (ArthurRelative.mem_standardIndex hG hi ν).mp j.2
  have hmem := (mem_simpleFinset (i := i) (ν := ν) (hG := hG) (hi := hi)).mpr hj.1
  have hw := (hX.2 _ hmem).2
  have hset : (simpleFinset ν hG hi : Set (characterLattice T)) = simpleRelativeRoots i ν :=
    Set.ext fun _ => mem_simpleFinset hG hi
  have hweight : 0 ≤ ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) j.1 (U - X) := by
    rw [show U - X = -(X - U) by abel, map_neg, neg_nonneg]
    simpa only [hset] using hw
  have hroot := (hX.2 _ hmem).1
  have hcoroot : 0 ≤ B (X - T₀) (D.realCoroot ⟨j.1.1, j.1.2.1⟩) := by
    have he := two_mul_form_realCoroot hi D hB ⟨j.1.1, j.1.2.1⟩ (X - T₀)
    have hn := form_self_nonneg B hB.2.1 (D.realCoroot ⟨j.1.1, j.1.2.1⟩)
    linarith [mul_nonneg hroot hn]
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg hweight hcoroot

omit [IsAffineHom G.X.hom] in
include hB in
private theorem cocharacterNorm_triangle (X Y : V T) :
    cocharacterNorm B (X + Y) ≤ cocharacterNorm B X + cocharacterNorm B Y := by
  let := positiveFormCore B hB.1 hB.2.1
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := V T)
  exact norm_add_le X Y

include hB in
/-- The ball with diameter `[T₀,U]` containing the characteristic chamber gives
norm bounds both at `T₀` and at the origin. -/
theorem cocharacterNorm_le_of_mem_characteristicChamber (hν : IsGenericCocharacter i ν)
    {T₀ U X : V T} (hU : U ∈ D.realCorootSpan)
    (hX : X ∈ characteristicChamber ν hG hi D T₀ U) :
    cocharacterNorm B (X - T₀) ≤ cocharacterNorm B (U - T₀) ∧
      cocharacterNorm B X ≤ cocharacterNorm B U + cocharacterNorm B T₀ := by
  let := positiveFormCore B hB.1 hB.2.1
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := V T)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (V T))
  have hn (v : V T) : cocharacterNorm B v = ‖v‖ := rfl
  have hiB (v w : V T) : B v w = inner ℝ v w := rfl
  have hangle := form_nonneg_of_mem_characteristicChamber hG hi D hB hν hU hX
  constructor
  · have hp : B (X - T₀) (X - T₀) ≤ B (X - T₀) (U - T₀) := by
      rw [← sub_nonneg, ← map_sub, show U - T₀ - (X - T₀) = U - X by abel]
      exact hangle
    have hp' : ‖X - T₀‖ * ‖X - T₀‖ ≤ ‖X - T₀‖ * ‖U - T₀‖ := by
      rw [hiB, real_inner_self_eq_norm_mul_norm, hiB] at hp
      exact hp.trans (real_inner_le_norm _ _)
    simp only [hn]
    by_cases hz : X - T₀ = 0
    · rw [hz, norm_zero]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_left hp' (norm_pos_iff.mpr hz)
  · let c := (1 / 2 : ℝ) • (U + T₀)
    let r := (1 / 2 : ℝ) • (U - T₀)
    have hidentity : B r r - B (X - c) (X - c) = B (X - T₀) (U - X) := by
      simp only [c, r, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, hB.1 U X, hB.1 U T₀, hB.1 X T₀]
      ring
    have hrad : ‖X - c‖ ≤ ‖r‖ := by
      rw [← hn, ← hn]
      exact Real.sqrt_le_sqrt (sub_nonneg.mp (hidentity.ge.trans' hangle))
    have hXc : X = (X - c) + c := by abel
    simp only [hn]
    calc
      ‖X‖ = ‖(X - c) + c‖ := congrArg (fun v : V T => ‖v‖) hXc
      _ ≤ ‖X - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖r‖ + ‖c‖ := add_le_add hrad le_rfl
      _ = (‖U - T₀‖ + ‖U + T₀‖) / 2 := by
        change ‖(1 / 2 : ℝ) • (U - T₀)‖ + ‖(1 / 2 : ℝ) • (U + T₀)‖ = _
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show 0 < (1 / 2 : ℝ) by norm_num)]
        ring
      _ ≤ ‖U‖ + ‖T₀‖ := by linarith [norm_sub_le U T₀, norm_add_le U T₀]

/-- With comparable increments on a sector, (7.14) and the upper norm bound on
`C_{T+S,T}^Q` hold with the constant `δ / (2 + k₀)`. -/
def CharacteristicShellBoundsStatement : Prop :=
  ∀ {B : LinearMap.BilinForm ℝ (V T)}, IsWeylInvariantCocharacterInnerProduct i B →
    IsGenericCocharacter i ν →
    ∀ {J : Global.StandardIndex F G i ν} {T₀ Tp S X : V T},
    Tp ∈ D.realCorootSpan → S ∈ D.realCorootSpan →
    X ∈ characteristicShell hG hi D J T₀ Tp S →
    ∀ {δ k₀ : ℝ}, 0 ≤ δ → 0 ≤ k₀ →
    cocharacterNorm B T₀ ≤ cocharacterNorm B Tp →
    cocharacterNorm B S ≤ k₀ * cocharacterNorm B Tp →
    (∀ α ∈ simpleRelativeRoots i ν, δ * cocharacterNorm B Tp ≤ eval T α Tp) →
    cocharacterNorm B X ≤ (2 + k₀) * cocharacterNorm B Tp ∧
      ∀ α ∈ simpleRelativeRoots i ν \ (J : Set (characterLattice T)),
        δ / (2 + k₀) * cocharacterNorm B X ≤ eval T α X

/-- The shell bounds follow from the characteristic chamber's norm bound
and the strict root comparison on the parabolic chamber. -/
theorem characteristicShell_bounds : CharacteristicShellBoundsStatement (ν := ν) hG hi D := by
  intro B hB hν J T₀ Tp S X hT hS hX δ k₀ hδ hk₀ hT₀ hstep hsector
  have hupper :=
    (cocharacterNorm_le_of_mem_characteristicChamber hG hi D hB hν
      (D.realCorootSpan.add_mem hT hS) hX.1).2
  have hsum := cocharacterNorm_triangle hB Tp S
  have hx : cocharacterNorm B X ≤ (2 + k₀) * cocharacterNorm B Tp := by linarith
  refine ⟨hx, fun α hα => ?_⟩
  have hp : 0 < 2 + k₀ := by linarith
  calc
    δ / (2 + k₀) * cocharacterNorm B X
        ≤ δ / (2 + k₀) * ((2 + k₀) * cocharacterNorm B Tp) :=
      mul_le_mul_of_nonneg_left hx (div_nonneg hδ hp.le)
    _ = δ * cocharacterNorm B Tp := by field_simp
    _ ≤ eval T α Tp := hsector α hα.1
    _ ≤ eval T α X := (eval_lt_of_mem_parabolicCharacteristicChamber hG hi D hν hX.2 hα).le

end Langlands.Global.ArthurTruncation
