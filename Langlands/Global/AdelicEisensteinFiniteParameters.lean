import Langlands.Global.AdelicEisensteinRightTranslation
import Langlands.Global.AdelicGroupProduct
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Finite holomorphic expansions of deformed finite translations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set Filter
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

local notation "Adeles" => AdelicGroupPoints F G
local notation "FinitePoints" => FiniteAdelicGroupPoints F G

/-- The change in the Iwasawa height under one fixed finite right translation. -/
def finiteHeightDisplacement (d : FinitePoints) (g : Adeles) : RealCharacterDual F P :=
  hK.height (g * ofFinite F G d) - hK.height g

private theorem finiteHeightDisplacement_parabolic_mul (d : FinitePoints)
    (q : AdelicGroupPoints F P) (g : Adeles) :
    hK.finiteHeightDisplacement d (map F P G p q * g) = hK.finiteHeightDisplacement d g := by
  simp only [finiteHeightDisplacement, mul_assoc, hK.height_map_mul, add_sub_add_left_eq_sub]

private theorem finiteHeightDisplacement_infinite_mul (d : FinitePoints) (g : Adeles)
    {x : InfiniteAdelicGroupPoints F G} (hx : ofInfinite F G x ∈ K) :
    hK.finiteHeightDisplacement d (g * ofInfinite F G x) = hK.finiteHeightDisplacement d g := by
  rw [finiteHeightDisplacement, mul_assoc, (factors_commute F G x d).eq, ← mul_assoc,
    hK.height_mul_right _ hx, hK.height_mul_right _ hx]
  rfl

private theorem locallyConstant_finiteHeightDisplacement
    (L : Subgroup FinitePoints) (hLo : IsOpen (L : Set FinitePoints))
    (hL : ∀ l : L, ofFinite F G l.val ∈ K) (d : FinitePoints) :
    IsLocallyConstant (X := (L : Set FinitePoints))
      (fun l => hK.finiteHeightDisplacement d (ofFinite F G l.val)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro l
  let conjugated (b : L) := d⁻¹ * (l.val⁻¹ * b.val) * d
  have hval : Continuous (fun b : L => b.val) := continuous_subtype_val
  have hc : Continuous conjugated :=
    (continuous_const.mul (continuous_const.mul hval)).mul continuous_const
  have ho := hLo.preimage hc
  have hl : conjugated l ∈ L := by simp [conjugated]
  refine Filter.eventually_of_mem (ho.mem_nhds hl) fun b hb => ?_
  have heq : ofFinite F G b.val * ofFinite F G d =
      (ofFinite F G l.val * ofFinite F G d) * ofFinite F G (conjugated b) := by
    simp only [← map_mul]
    apply congrArg (ofFinite F G)
    dsimp only [conjugated]
    group
  change hK.finiteHeightDisplacement d (ofFinite F G b.val) =
    hK.finiteHeightDisplacement d (ofFinite F G l.val)
  rw [finiteHeightDisplacement, finiteHeightDisplacement, heq,
    hK.height_mul_right _ (hL ⟨conjugated b, hb⟩), hK.height_of_mem (hL b), hK.height_of_mem (hL l)]

/-- In a product Iwasawa compact with a compact open finite factor, a finite
translation changes the height by only finitely many functionals. -/
theorem finite_range_finiteHeightDisplacement
    (L : Subgroup FinitePoints) (hLo : IsOpen (L : Set FinitePoints))
    (hLc : IsCompact (L : Set FinitePoints)) (hL : ∀ l : L, ofFinite F G l.val ∈ K)
    (hFin : ∀ k ∈ K, finite F G k ∈ L) (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (d : FinitePoints) :
    (Set.range (hK.finiteHeightDisplacement d)).Finite := by
  let _ : CompactSpace (L : Set FinitePoints) := isCompact_iff_compactSpace.mp hLc
  refine (locallyConstant_finiteHeightDisplacement hK L hLo hL d).range_finite.subset ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
  refine ⟨⟨finite F G k, hFin k hk⟩, ?_⟩
  have hsplit : ofFinite F G (finite F G k) * ofInfinite F G (infinite F G k) = k := by
    rw [ofFinite_eq_pair, ofInfinite_eq_pair, pair_mul, one_mul, mul_one, pair_projections]
  change hK.finiteHeightDisplacement d (ofFinite F G (finite F G k)) =
    hK.finiteHeightDisplacement d (map F P G p q * k)
  rw [hK.finiteHeightDisplacement_parabolic_mul]
  exact (hK.finiteHeightDisplacement_infinite_mul d _ (hInf k hk)).symm.trans
    (congrArg (hK.finiteHeightDisplacement d) hsplit)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
private theorem parameterRightAction_eq_heightDisplacement (lam : ComplexCharacterParameter F P)
    (d : FinitePoints) (f : Adeles → ℂ) (g : Adeles) :
    hK.parameterRightAction lam (ofFinite F G d) f g =
      f (g * ofFinite F G d) * Complex.exp
        (complexParameterPairing F P lam (hK.finiteHeightDisplacement d g)) := by
  rw [hK.parameterRightAction_apply, mul_div_assoc, heightPower, heightPower,
    finiteHeightDisplacement, map_sub, Complex.exp_sub]

/-- A deformed finite translate is a finite sum of fixed scalar functions
with entire scalar coefficients in any finite-dimensional linear coordinates. -/
theorem finiteExpansion_parameterRightAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (L : Subgroup FinitePoints) (hLo : IsOpen (L : Set FinitePoints))
    (hLc : IsCompact (L : Set FinitePoints)) (hL : ∀ l : L, ofFinite F G l.val ∈ K)
    (hFin : ∀ k ∈ K, finite F G k ∈ L) (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (e : E →ₗ[ℂ] ComplexCharacterParameter F P)
    (d : FinitePoints) (f : Adeles → ℂ) :
    ∃ (m : ℕ) (a : Fin m → E → ℂ) (v : Fin m → Adeles → ℂ),
      (∀ j, Differentiable ℂ (a j)) ∧ ∀ t,
        hK.parameterRightAction (e t) (ofFinite F G d) f = ∑ j, a j t • v j := by
  classical
  let S := Set.range (hK.finiteHeightDisplacement d)
  let _ : Finite S := (hK.finite_range_finiteHeightDisplacement L hLo hLc hL hFin hInf d).to_subtype
  let _ := Fintype.ofFinite S
  let idx := Fintype.equivFin S
  let a (j : Fin (Fintype.card S)) (t : E) :=
    Complex.exp (complexParameterPairing F P (e t) (idx.symm j).val)
  let v (j : Fin (Fintype.card S)) (g : Adeles) :=
    if hK.finiteHeightDisplacement d g = (idx.symm j).val then f (g * ofFinite F G d) else 0
  refine ⟨_, a, v, fun j => ?_, fun t => ?_⟩
  · let l : E →ₗ[ℂ] ℂ :=
      { toFun t := complexParameterPairing F P (e t) (idx.symm j).val
        map_add' t s := by rw [map_add, map_add, LinearMap.add_apply]
        map_smul' c t := by rw [map_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
    have hd : Differentiable ℂ l := l.toContinuousLinearMap.differentiable
    exact hd.cexp
  · funext g
    let i := idx ⟨hK.finiteHeightDisplacement d g, g, rfl⟩
    have hei : (idx.symm i).val = hK.finiteHeightDisplacement d g := by simp [i]
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hK.parameterRightAction_eq_heightDisplacement]
      change _ = Complex.exp (complexParameterPairing F P (e t) (idx.symm i).val) *
        (if hK.finiteHeightDisplacement d g = (idx.symm i).val then f (g * ofFinite F G d) else 0)
      simp [hei, mul_comm]
    · intro j _ hji
      have hne : hK.finiteHeightDisplacement d g ≠ (idx.symm j).val := by
        intro h
        exact hji (idx.symm.injective (Subtype.ext (h.symm.trans hei.symm)))
      simp [v, hne]
    · simp

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
