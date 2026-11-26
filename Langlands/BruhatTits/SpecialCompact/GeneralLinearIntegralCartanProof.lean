import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralCartanStatement
import Langlands.Group.GL.CartanProof
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer
import Langlands.GroupScheme.Rational.GeneralLinearSimpleRootsProof
import Langlands.GroupScheme.Reductive.GeneralLinearWeyl
import Mathlib.Data.Fin.Tuple.Sort

/-! # Cartan decomposition at the standard integral points of `GL_N` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel.RenardCartan
open Langlands.GeneralLinear

namespace Langlands.BruhatTits.SpecialCompact

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {N : ℕ}

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
local notation "iD" => GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
local notation "π" => SplitTorusValuation.uniformizerUnit F
local notation "v" => ValuativeRel.valuation F
local notation "weights" => GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F
local notation "toMatrix" => GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
local notation "K₀" => IntegralModel.integralPoints (GroupScheme.GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N))

/-- The uniformizer of the shared section satisfies the matrix Cartan
decomposition's value-group condition. -/
theorem uniformizerUnit_isUniformizingElement : Iwasawa.IsUniformizingElement v π := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hπ : e (v (π : F)) = WithZero.exp (-1) := by
    have h := LocalField.ord_uniformizer F
    rw [FML.ord_of_ne_zero F (LocalField.uniformizer_ne_zero F), ← WithTop.coe_one,
      WithTop.coe_inj] at h
    change -WithZero.log (e (v (π : F))) = 1 at h
    have hv : e (v (π : F)) ≠ 0 := by
      simpa [e] using LocalField.uniformizer_ne_zero F
    rw [← WithZero.exp_log hv, show WithZero.log (e (v (π : F))) = -1 by omega]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← e.strictMono.lt_iff_lt, hπ, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hv : e (v x) ≠ 0 := by simpa [e] using hx
    refine ⟨-WithZero.log (e (v x)), e.injective ?_⟩
    change e (v x) = e (v (π : F) ^ (-WithZero.log (e (v x))))
    have hk : e (v x) = e (v (π : F)) ^ (-WithZero.log (e (v x))) := by
      rw [hπ, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
        WithZero.exp_log hv]
    simpa only [map_zpow₀] using hk

/-- Under the actual matrix equivalence, a diagonal uniformizer point is the
matrix of uniformizer powers with the same cocharacter weights. -/
theorem rationalPointsEquiv_diagonalUniformizerSection (c : cocharacterLattice 𝕋) :
    toMatrix (rationalPoints.map iD (uniformizerSection 𝕋 (Multiplicative.ofAdd c))) =
      Iwasawa.torus π (weights c) := by
  rw [uniformizerSection_splitTorus]
  let t := SplitTorusValuation.cocharacterPoints F (ULift (Fin N)) c π
  change GroupScheme.GeneralLinear.glRingEquiv
    (GroupScheme.GeneralLinear.globalSectionsEquiv (CommRingCat.of F))
      (GroupScheme.GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) _
        (t ≫ (iD).hom.hom)) = _
  rw [GroupScheme.GeneralLinear.pointsEquiv_diagonalTorus]
  apply Units.ext
  ext i j
  rw [GroupScheme.GeneralLinear.glRingEquiv_apply,
    GroupScheme.GeneralLinear.coe_diagonalTorusUnits, Iwasawa.torus_val]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    exact congrArg Units.val
      (SplitTorusValuation.coords_cocharacterPoints F (ULift (Fin N)) c π (ULift.up i))
  · simp [Matrix.diagonal_apply_ne _ hij]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem nonnegative_iff_antitone (ν c : cocharacterLattice 𝕋)
    (p : Equiv.Perm (Fin N)) (hp : StrictAnti (weights ν ∘ p)) :
    (∀ α ∈ positiveRelativeRoots iD ν, 0 ≤ latticePairing 𝕋 α c) ↔
      Antitone (weights c ∘ p) := by
  let R := GroupScheme.GeneralLinear.rootDatum (Fin N) F
  have hr := (GroupScheme.GeneralLinear.isRootDatumOf_rootDatum (n := Fin N) F).2.1
  constructor
  · intro hc i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    let α := R.root ⟨(p i, p j), fun h => hij.ne (p.injective h)⟩
    have hα : α ∈ positiveRelativeRoots iD ν := by
      constructor
      · change α ∈ roots iD
        rw [← hr]
        exact Set.mem_range_self _
      · change 0 < latticePairing 𝕋 (R.root _) ν
        rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root]
        exact sub_pos.mpr (hp hij)
    have h := hc α hα
    change 0 ≤ latticePairing 𝕋 (R.root _) c at h
    rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root] at h
    exact sub_nonneg.mp h
  · intro hc α hα
    have hroot : α ∈ roots iD := hα.1
    rw [← hr] at hroot
    obtain ⟨q, rfl⟩ := hroot
    obtain ⟨i, hi⟩ := p.surjective q.val.1
    obtain ⟨j, hj⟩ := p.surjective q.val.2
    have hlt : weights ν (p j) < weights ν (p i) := by
      have h := hα.2
      rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root] at h
      rw [hi, hj]
      exact sub_pos.mp h
    have hij : i < j := hp.lt_iff_gt.mp hlt
    rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root, ← hi, ← hj]
    exact sub_nonneg.mpr (hc hij.le)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem permGL_mem_integralRange (p : Equiv.Perm (Fin N)) :
    GroupScheme.GeneralLinear.permGL F p ∈ Iwasawa.integralRange v N := by
  refine ⟨GroupScheme.GeneralLinear.permGL 𝒪[F] p, ?_⟩
  exact GroupScheme.GeneralLinear.map_permGL (algebraMap 𝒪[F] F) p

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem permGL_conj_torus (uniformizer : Fˣ) (p : Equiv.Perm (Fin N))
    (c : Fin N → ℤ) :
    let P := GroupScheme.GeneralLinear.permGL F p.symm
    P * Iwasawa.torus uniformizer c * P⁻¹ = Iwasawa.torus uniformizer (c ∘ p) := by
  exact GroupScheme.GeneralLinear.permGL_conj_diagonalTorusUnits F p.symm
    (fun i : ULift.{u} (Fin N) => uniformizer ^ c i.down)

private theorem cartan_bijective (ν : cocharacterLattice 𝕋)
    (hν : IsGenericCocharacter iD ν) :
    Function.Bijective (fun a : C0Plus 𝕋 iD (positiveRelativeRoots iD ν) =>
      DoubleCoset.mk K₀ K₀ a.val) := by
  let p := Tuple.sort (fun i => -weights ν i)
  have hp : StrictAnti (weights ν ∘ p) := by
    have hmono := Tuple.monotone_sort (fun i => -weights ν i)
    have hant : Antitone (weights ν ∘ p) := fun _ _ hij => neg_le_neg_iff.mp (hmono hij)
    exact hant.strictAnti_iff_injective.mpr
      (((GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mp
        hν).comp p.injective)
  let P := GroupScheme.GeneralLinear.permGL F p.symm
  let E := (toMatrix).trans (MulAut.conj P)
  have hP : P ∈ Iwasawa.integralRange v N := permGL_mem_integralRange F p.symm
  have hK (g : rationalPoints (GroupScheme.GeneralLinear.groupScheme
      (Fin N) (CommRingCat.of F))) :
      g ∈ K₀ ↔ toMatrix g ∈ Iwasawa.integralRange v N :=
    GroupScheme.GeneralLinear.mem_standardIntegralModel_integralPoints_iff 𝒪[F] F g
  have hE (g : rationalPoints (GroupScheme.GeneralLinear.groupScheme
      (Fin N) (CommRingCat.of F))) :
      E g ∈ Iwasawa.integralRange v N ↔ g ∈ K₀ := by
    constructor
    · intro hg
      apply (hK g).mpr
      have h : toMatrix g = P⁻¹ * E g * P := by
        change toMatrix g = P⁻¹ * (P * toMatrix g * P⁻¹) * P
        group
      rw [h]
      exact mul_mem (mul_mem (inv_mem hP) hg) hP
    · intro hg
      exact mul_mem (mul_mem hP ((hK g).mp hg)) (inv_mem hP)
  let point (c : cocharacterLattice 𝕋) :=
    rationalPoints.map iD (uniformizerSection 𝕋 (Multiplicative.ofAdd c))
  have hpoint (c : cocharacterLattice 𝕋) :
      E (point c) = Iwasawa.torus π (weights c ∘ p) := by
    change P * toMatrix (point c) * P⁻¹ = _
    rw [rationalPointsEquiv_diagonalUniformizerSection F c]
    exact permGL_conj_torus F π p (weights c)
  have hπ := uniformizerUnit_isUniformizingElement F
  constructor
  · intro a b hab
    obtain ⟨c, hc, hca⟩ := (mem_C0Plus 𝕋 iD _ a.val).mp a.property
    obtain ⟨d, hd, hdb⟩ := (mem_C0Plus 𝕋 iD _ b.val).mp b.property
    obtain ⟨k, hk, l, hl, h⟩ := DoubleCoset.eq.mp hab
    have he : Iwasawa.torus π (weights d ∘ p) =
        E k * Iwasawa.torus π (weights c ∘ p) * E l := by
      rw [← hpoint d, ← hpoint c, show point c = a.val from hca,
        show point d = b.val from hdb, h, map_mul, map_mul]
    have hweights := Cartan.exponent_unique hπ
      ((nonnegative_iff_antitone F ν c p hp).mp hc)
      ((nonnegative_iff_antitone F ν d p hp).mp hd)
      ((hE k).mpr hk) ((hE l).mpr hl) (one_mem _) (one_mem _) (by simpa using he.symm)
    have hcd : c = d := (weights).injective (funext fun i => by
      obtain ⟨j, rfl⟩ := p.surjective i
      exact congrFun hweights j)
    exact Subtype.ext (hca.symm.trans ((congrArg point hcd).trans hdb))
  · intro q
    induction q using _root_.Quotient.inductionOn with
    | h g =>
      obtain ⟨a, ha, k, hk, l, hl, hg⟩ := Cartan.exists_cartan hπ N (E g)
      let c := GroupScheme.GeneralLinear.cocharacterOfWeights F (a ∘ p.symm)
      have hw : weights c ∘ p = a := by
        dsimp [c]
        rw [GroupScheme.GeneralLinear.cocharacterCoordEquiv_cocharacterOfWeights]
        funext i
        simp
      refine ⟨⟨point c, (mem_C0Plus 𝕋 iD _ _).mpr ⟨c,
        (nonnegative_iff_antitone F ν c p hp).mpr (hw ▸ ha), rfl⟩⟩,
        DoubleCoset.eq.mpr ⟨E.symm k, (hE _).mp (by rwa [MulEquiv.apply_symm_apply]),
          E.symm l, (hE _).mp (by rwa [MulEquiv.apply_symm_apply]), ?_⟩⟩
      apply E.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, hpoint, hw] using hg

/-- The matrix Cartan decomposition in the chamber of the actual diagonal torus. -/
theorem generalLinearIntegralCartan : GeneralLinearIntegralCartanStatement.{u} := by
  intro F _ _ _ _ N ν
  exact cartan_bijective F ν

end Langlands.BruhatTits.SpecialCompact
