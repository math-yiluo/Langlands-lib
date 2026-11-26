import Langlands.Global.AdelicIntertwiningCommonCocharacters
import Langlands.Global.AdelicEisensteinConjugateParabolicHeight
import Langlands.Global.AdelicWeylPositiveTransport
import Langlands.Global.AdelicRepresentationHeightDominationProof
import Langlands.Global.AdelicLocalFinitenessSiegelRepresentatives
import Langlands.GroupScheme.Dynamic.CommutingOppositeFactorization
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # Comparison of the reflected height with a point of the opposite target radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
  {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a')
  {π' : Q ⟶ M'} {c : M' ⟶ M} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (hK' : IsIwasawaCompact q K)

local notation "W" => innerAdelicPoint F G w
local notation "χP" => CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
local notation "χQ" => CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a' ≫ l' ≫ q
local notation "χW" => χP ≫ Iso.hom (G.innerIso w)

omit [IsAffine Q.X.left] in
private theorem heightPower_eq_of_levi_radical_factor
    (iV : V ⟶ Q) (l' : M' ⟶ Q) (hV : IsUnipotent V) (lam : ComplexCharacterParameter F Q)
    (m : AdelicGroupPoints F M') (v₁ v₂ : AdelicGroupPoints F V) :
    parameterPower F Q lam (map F V Q iV v₁ * map F M' Q l' m * map F V Q iV v₂) =
      parameterPower F Q lam (map F M' Q l' m) := by
  unfold parameterPower
  rw [characterLog_mul, characterLog_mul, characterLog_map F V Q iV,
    characterLog_map F V Q iV, characterLog_eq_zero_of_isUnipotent hV v₁,
    characterLog_eq_zero_of_isUnipotent hV v₂, map_zero, zero_add, add_zero]

include r in
set_option maxHeartbeats 1200000 in
/-- After removing a left source-radical factor, the target-radical argument
has polynomial height in an opposite target point. The source height power
equals its reflected target height power up to a scalar independent of the
radical argument. -/
theorem exists_intertwiningReflectedHeightComparison (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hπ' : l' ≫ π' = 𝟙 M') (hw : IsWeylConjugation p l q l' w c)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ (C : ℝ) (d : ℕ) (b : ComplexCharacterParameter F P → ℝ),
      0 < C ∧ (∀ lam, 0 < b lam) ∧
      ∀ v : AdelicGroupPoints F G,
        v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) →
        ∃ v' y : AdelicGroupPoints F G,
          W⁻¹ * v * (W⁻¹ * v')⁻¹ ∈ parabolicUnipotentImage F p iU ∧
          y ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χQ)).carrier _ ∧
          adelicHeight F G rho v' ≤ C * adelicHeight F G rho y ^ d ∧
          ∀ lam, ‖hK.heightPower lam (W⁻¹ * v)‖ =
            b lam * ‖hK'.heightPower (-weylParameter l c π' lam) y‖ := by
  let : Smooth G.X.hom := hG.smooth
  let : IsIso c := hw.isIso
  let : Smooth M'.X.hom := r'.isCompatible.levi.isConnectedReductive.smooth
  let : LocallyOfFiniteType M'.X.hom := inferInstance
  let : IsAffineHom M'.X.hom := r'.isCompatible.levi.isConnectedReductive.isAffineHom
  let : IsAffine M'.X.left := isAffine_of_isAffineHom M'.X.hom
  let : IsIso (subgroupMultiplication l iU) := r.isIso_subgroupMultiplication_of_radical hU
  let : IsIso (subgroupMultiplication l' iV) := r'.isIso_subgroupMultiplication_of_radical hV
  let pW := p ≫ (G.innerIso w).hom
  let : IsIso (G.innerIso w).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso w))).hom)
  let : IsClosedImmersion pW.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (p.hom.hom.left ≫ (G.innerIso w).hom.hom.hom.left))
  have hpW (z : AdelicGroupPoints F P) : map F P G pW z = W * map F P G p z * W⁻¹ := by
    rw [show pW = p ≫ (G.innerIso w).hom from rfl, map_comp_apply_of_hom]
    exact affinePointsTarget_innerIso_hom F G w _
  let hKW := hK.of_conjugate_map hpW
  obtain ⟨ζ, ξ, _, hζ, hξ, _, _⟩ := exists_commonIntertwiningCocharacters r r' hw
  have hZ : Dynamic.centralizer χQ = SubgroupFunctor.range (l' ≫ q) :=
    r'.levi_eq_splitComponentCocharacter.symm
  have hZW : Dynamic.centralizer χW = SubgroupFunctor.range (l' ≫ q) :=
    centralizer_conjugate_sourceCocharacter r hw
  have hUmap := range_conjugate_sourceRadical r (w := w) hU
  have hVmap := r'.range_comp_radical_eq hV
  let π₀ := leviRetraction l' iV hV.1.isNormal
  have hl₀ : l' ≫ π₀ = 𝟙 M' := levi_comp_leviRetraction l' iV hV.1.isNormal
  have h₀ (z : AdelicGroupPoints F V) : map F Q M' π₀ (map F V Q iV z) = 1 := by
    change (z ≫ iV.hom.hom) ≫ π₀.hom.hom = 1
    exact (comp_leviRetraction_eq_one_iff l' iV hV.1.isNormal _).2 ⟨z, rfl⟩
  let σ := rho.restrict q
  let σ₀ := rho.restrict (π₀ ≫ l' ≫ q)
  have hσ : IsClosedSubgroup σ := by
    let : IsClosedImmersion rho.hom.hom.left := hrho
    exact inferInstanceAs (IsClosedImmersion (q.hom.hom.left ≫ rho.hom.hom.left))
  obtain ⟨D, hD, e, hBound⟩ := closedImmersionAdelicHeightDomination F Q N N σ σ₀ hN hN hσ
  obtain ⟨L₀, hL₀⟩ := (hK.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  let L := max L₀ 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  let b := fun lam => ‖hKW.heightPower lam W‖⁻¹
  have hb (lam) : 0 < ‖hKW.heightPower lam W‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  refine ⟨D * L ^ (e + 1), e + 1, b, by positivity, fun lam => inv_pos.mpr (hb lam), ?_⟩
  intro v hv
  obtain ⟨v₀, hv₀⟩ := SubgroupFunctor.mem_range.mp hv
  obtain ⟨p₀, k, hk, hp₀⟩ := hKW.exists_eq v
  let m₀ : AdelicGroupPoints F M := leviComponent l iU p₀
  let u₀ : AdelicGroupPoints F U := radicalComponent l iU p₀
  have hpFact : map F M P l m₀ * map F U P iU u₀ = p₀ :=
    leviComponent_mul_radicalComponent l iU p₀
  let m' := map F M M' (inv c) m₀
  have hmc : map F M' M c m' = m₀ := by
    dsimp only [m']
    rw [← map_comp_apply_of_hom, IsIso.inv_hom_id]
    rfl
  let m := map F M' G (l' ≫ q) m'
  let u := map F U G (iU ≫ pW) u₀
  have hm : map F P G pW (map F M P l m₀) = m := by
    dsimp only [pW, m, m']
    rw [← map_comp_apply_of_hom, ← Category.assoc, hw.comp_inner_hom, map_comp_apply_of_hom]
  have hu : u ∈ (Dynamic.unipotent χW).carrier _ := by
    rw [← hUmap]
    exact ⟨u₀, rfl⟩
  obtain ⟨n, y, hn, hy, hsplit⟩ := Dynamic.exists_factors_unipotent_opposite_of_centralizer_le
    r'.data.i (CommGroupScheme.groupHom ζ) (CommGroupScheme.groupHom ξ)
    (by rw [hξ, hζ, hZ, hZW]) (g := u) (by rw [hζ]; exact hu)
  rw [hζ, hξ] at hn
  rw [hξ] at hy
  have hnU : n ∈ (Dynamic.unipotent χW).carrier _ := hn.1
  have hnV : n ∈ (SubgroupFunctor.range (iV ≫ q)).carrier _ := hVmap.symm ▸ hn.2
  obtain ⟨n₀, hn₀⟩ := SubgroupFunctor.mem_range.mp hnV
  have hvEq : v = m * n * (y * k) := by
    rw [← hp₀, ← hpFact, map_mul, hm, ← map_comp_apply_of_hom, show
      map F U G (iU ≫ pW) u₀ = u from rfl, hsplit]
    group
  let xQ := (map F V Q iV n₀)⁻¹ * (map F M' Q l' m')⁻¹ * map F V Q iV v₀
  let x := map F Q G q xQ
  have hx : x = y * k := by
    dsimp only [x, xQ, m]
    simp only [map_mul, map_inv, ← map_comp_apply_of_hom]
    rw [show map F V G (iV ≫ q) n₀ = n from hn₀, show map F V G (iV ≫ q) v₀ = v from hv₀]
    change n⁻¹ * m⁻¹ * v = _
    rw [hvEq]
    group
  have hxπ : map F Q M' π₀ xQ = (m')⁻¹ := by
    dsimp only [xQ]
    rw [map_mul, map_mul, map_inv, map_inv, h₀, h₀, ← map_comp_apply_of_hom, hl₀]
    change (1 : AdelicGroupPoints F M')⁻¹ * (m')⁻¹ * 1 = _
    simp
  have hmNorm : adelicHeight F G rho m ≤ D * adelicHeight F G rho x ^ e := by
    have key : map F Q G (π₀ ≫ l' ≫ q) xQ = m⁻¹ := by
      rw [map_comp_apply_of_hom, hxπ, map_inv]
    have hB := hBound xQ
    change adelicHeight F G rho (map F Q G (π₀ ≫ l' ≫ q) xQ) ≤
      D * adelicHeight F G rho x ^ e at hB
    rwa [key, adelicHeight_inv] at hB
  have hkNorm : adelicHeight F G rho k ≤ L :=
    (hL₀ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hxNorm : adelicHeight F G rho x ≤ L * adelicHeight F G rho y := by
    rw [hx, mul_comm L]
    exact (adelicHeight_mul_le F G rho hN _ _).trans
      (mul_le_mul_of_nonneg_left hkNorm (zero_le_one.trans (one_le_adelicHeight F G rho hN _)))
  let v' := m * x
  have hv'Norm : adelicHeight F G rho v' ≤ (D * L ^ (e + 1)) *
      adelicHeight F G rho y ^ (e + 1) := by
    calc
      _ ≤ (D * adelicHeight F G rho x ^ e) * adelicHeight F G rho x :=
        (adelicHeight_mul_le F G rho hN _ _).trans
          (mul_le_mul_of_nonneg_right hmNorm (zero_le_one.trans (one_le_adelicHeight F G rho hN _)))
      _ = D * adelicHeight F G rho x ^ (e + 1) := by rw [pow_succ, mul_assoc]
      _ ≤ D * (L * adelicHeight F G rho y) ^ (e + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) hxNorm _) (zero_le_one.trans hD)
      _ = _ := by rw [mul_pow, mul_assoc]
  have hleft : W⁻¹ * v * (W⁻¹ * v')⁻¹ ∈ parabolicUnipotentImage F p iU := by
    have hmZ : m ∈ (Dynamic.centralizer χW).carrier _ := by rw [hZW]; exact ⟨m', rfl⟩
    have hmu : m * n * m⁻¹ ∈ (Dynamic.unipotent χW).carrier _ :=
      Dynamic.conj_mem_unipotent χW (Dynamic.centralizer_le_parabolic χW _ hmZ) hnU
    rw [← hUmap] at hmu
    obtain ⟨u', hu'⟩ := SubgroupFunctor.mem_range.mp hmu
    have hu'val : map F U G (iU ≫ pW) u' = m * n * m⁻¹ := hu'
    have hconj : map F U G (iU ≫ p) u' = W⁻¹ * (m * n * m⁻¹) * W := by
      rw [← hu'val, map_comp_apply_of_hom (p := pW) iU, hpW, map_comp_apply_of_hom (p := p) iU]
      group
    refine ⟨u', ?_⟩
    change map F U G (iU ≫ p) u' = _
    rw [hconj, hvEq, ← hx]
    dsimp only [v']
    group
  refine ⟨v', y, hleft, hy, hv'Norm, fun lam => ?_⟩
  have hpPow : hKW.heightPower lam v = parameterPower F P lam (map F M P l m₀) := by
    unfold IsIwasawaCompact.heightPower parameterPower
    rw [hKW.height_eq hk hp₀, ← hpFact, characterLog_mul, characterLog_map F U P iU,
      characterLog_eq_zero_of_isUnipotent hU.1.isUnipotent u₀, map_zero, add_zero]
  have hyEq : map F Q G q xQ * k⁻¹ = y := by change x * k⁻¹ = y; rw [hx, mul_inv_cancel_right]
  have hyPow : hK'.heightPower (-weylParameter l c π' lam) y = hKW.heightPower lam v := by
    have h1 : hK'.heightPower (-weylParameter l c π' lam) y =
        parameterPower F Q (-weylParameter l c π' lam) xQ := by
      unfold IsIwasawaCompact.heightPower parameterPower
      rw [hK'.height_eq (K.inv_mem hk) hyEq]
    rw [h1, hpPow]
    have hxQ : xQ = map F V Q iV n₀⁻¹ * map F M' Q l' (m')⁻¹ * map F V Q iV v₀ := by
      simp only [xQ, map_inv]
    rw [hxQ, heightPower_eq_of_levi_radical_factor iV l' hV.1.isUnipotent, ← map_neg,
      weylParameter_power, ← map_comp_apply_of_hom, ← Category.assoc l' π', hπ',
      Category.id_comp, map_comp_apply_of_hom, map_inv, hmc, map_inv]
    simp [parameterPower, characterLog_inv]
  have hmul := hK.heightPower_mul_of_conjugate_map hKW hpW lam (W⁻¹ * v)
  rw [mul_inv_cancel_left] at hmul
  rw [hyPow, hmul, norm_mul, show b lam = ‖hKW.heightPower lam W‖⁻¹ from rfl,
    mul_comm ‖hK.heightPower lam (W⁻¹ * v)‖, ← mul_assoc, inv_mul_cancel₀ (hb lam).ne', one_mul]

end Langlands.Global.AdelicGroupPoints
