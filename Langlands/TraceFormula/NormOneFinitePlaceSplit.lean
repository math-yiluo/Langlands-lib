import Langlands.TraceFormula.PositiveAverageOrbitSupport
import Langlands.TraceFormula.AdelicGroupAutomorphism

/-! # Separating a finite factor of the actual norm-one group -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Filter Topology
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme
open AdelicGroupAutomorphism

universe u

section Insertion

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  (v : Langlands.Global.FinitePlace K)

local instance : DecidableEq (Place K) := Classical.decEq _

private def singlePlaceFamily (x : PlaceGroupPoints K G (.inr v)) (i : Place K) :
    PlaceGroupPoints K G i :=
  Pi.mulSingle (M := PlaceGroupPoints K G) (Sum.inr v) x i

omit [IsAffine G.X.left] in
private theorem singlePlaceFamily_isAdelic (x : PlaceGroupPoints K G (.inr v)) :
    IsAdelicFamily K G (singlePlaceFamily K G v x) := by
  apply isAdelicFamily_of_eventually_eq K G _ 1
  filter_upwards [eventually_cofinite_ne v] with w hw
  rw [singlePlaceFamily, Pi.mulSingle_eq_of_ne (fun h ↦ hw (Sum.inr.inj h)), map_one]

private theorem continuous_glue_singlePlaceFamily :
    Continuous (fun x : PlaceGroupPoints K G (.inr v) ↦
      glue K G (singlePlaceFamily K G v x) (singlePlaceFamily_isAdelic K G v x)) := by
  apply (G.continuous_affinePoints_iff (CommAlgCat.of K (Adeles K)) _).mpr
  intro a
  let eval (x : PlaceGroupPoints K G (.inr v)) : Adeles K :=
    G.affinePointEvaluation (CommAlgCat.of K (Adeles K))
      (glue K G (singlePlaceFamily K G v x) (singlePlaceFamily_isAdelic K G v x)) a
  have he (x : PlaceGroupPoints K G (.inr v)) (i : Place K) :
      adeleProjection K i (eval x) =
        G.affinePointEvaluation (placeCompletion K i) (singlePlaceFamily K G v x i) a :=
    glue_evaluation K G _ _ a i
  have hArch : Continuous fun x ↦ (eval x).1 := by
    apply continuous_pi
    intro w
    have hconst (x : PlaceGroupPoints K G (.inr v)) :
        (eval x).1 w = G.affinePointEvaluation (placeCompletion K (.inl w)) 1 a := by
      change adeleProjection K (.inl w) (eval x) = _
      rw [he, singlePlaceFamily, Pi.mulSingle_eq_of_ne (Sum.inl_ne_inr)]
    exact continuous_const.congr (fun x ↦ (hconst x).symm)
  let S : Set (Langlands.Global.FinitePlace K) := {w | w ≠ v ∧
    G.affinePointEvaluation (placeCompletion K (.inr w)) 1 a ∈ w.adicCompletionIntegers K}
  have hIntegral : ∀ᶠ w : Langlands.Global.FinitePlace K in cofinite,
      G.affinePointEvaluation (placeCompletion K (.inr w)) 1 a ∈ w.adicCompletionIntegers K :=
    (eventually_atPlace_evaluation_mem K G 1 a).mono (fun w hw ↦ by
      simpa only [map_one] using hw)
  have hS : cofinite ≤ principal S :=
    le_principal_iff.mpr ((eventually_cofinite_ne v).and hIntegral)
  let f : PlaceGroupPoints K G (.inr v) →
      Πʳ w : Langlands.Global.FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]_[principal S] :=
    fun x ↦ ⟨fun w ↦ G.affinePointEvaluation (placeCompletion K (.inr w))
        (singlePlaceFamily K G v x (.inr w)) a,
      fun w hw ↦ by
        change G.affinePointEvaluation (placeCompletion K (.inr w))
          (singlePlaceFamily K G v x (.inr w)) a ∈ w.adicCompletionIntegers K
        rw [singlePlaceFamily, Pi.mulSingle_eq_of_ne (fun h ↦ hw.1 (Sum.inr.inj h))]
        exact hw.2⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun x : PlaceGroupPoints K G (.inr v) ↦
      G.affinePointEvaluation (placeCompletion K (.inr w)) (singlePlaceFamily K G v x (.inr w)) a)
    by_cases hw : w = v
    · subst w
      simpa only [singlePlaceFamily, Pi.mulSingle_eq_same] using
        (G.continuous_affinePointEvaluation (placeCompletion K (.inr v)) a)
    · simpa only [singlePlaceFamily, Pi.mulSingle_eq_of_ne (fun h ↦ hw (Sum.inr.inj h))] using
        (continuous_const : Continuous (fun _ : PlaceGroupPoints K G (.inr v) ↦
          G.affinePointEvaluation (placeCompletion K (.inr w)) 1 a))
  have hfin : Continuous (fun x ↦ (eval x).2) := by
    apply ((RestrictedProduct.continuous_inclusion hS).comp hf).congr
    intro x
    apply FiniteAdeleRing.ext
    intro w
    exact (he x (.inr w)).symm
  change Continuous eval
  exact hArch.prodMk hfin

/-- Insert a finite local point as an adelic point with identity at every
other place. -/
def finitePlacePointInclusion :
    PlaceGroupPoints K G (.inr v) →ₜ* AdelicGroupPoints K G where
  toFun x := glue K G (singlePlaceFamily K G v x) (singlePlaceFamily_isAdelic K G v x)
  map_one' := by
    apply ext_atPlace K G
    intro i
    rw [atPlace_glue, map_one]
    exact congrFun (Pi.mulSingle_one (M := PlaceGroupPoints K G) (Sum.inr v)) i
  map_mul' x y := by
    apply ext_atPlace K G
    intro i
    rw [map_mul (atPlace K G i), atPlace_glue, atPlace_glue, atPlace_glue]
    exact congrFun (Pi.mulSingle_mul (f := PlaceGroupPoints K G) (Sum.inr v) x y) i
  continuous_toFun := continuous_glue_singlePlaceFamily K G v

@[simp] theorem atPlace_finitePlacePointInclusion
    (x : PlaceGroupPoints K G (.inr v)) :
    atPlace K G (.inr v) (finitePlacePointInclusion K G v x) = x := by
  change atPlace K G (.inr v) (glue K G _ (singlePlaceFamily_isAdelic K G v x)) = x
  rw [atPlace_glue, singlePlaceFamily, Pi.mulSingle_eq_same]

theorem atPlace_finitePlacePointInclusion_of_ne
    (i : Place K) (hi : i ≠ .inr v) (x : PlaceGroupPoints K G (.inr v)) :
    atPlace K G i (finitePlacePointInclusion K G v x) = 1 := by
  change atPlace K G i (glue K G _ (singlePlaceFamily_isAdelic K G v x)) = 1
  rw [atPlace_glue, singlePlaceFamily, Pi.mulSingle_eq_of_ne hi]

/-- Finite-place insertion is natural for morphisms of affine groups. -/
theorem finitePlacePointInclusion_map
    {J : GroupScheme (Spec (CommRingCat.of K))} [IsAffine J.X.left] (f : G ⟶ J)
    (x : PlaceGroupPoints K G (.inr v)) :
    AdelicGroupPoints.map K G J f (finitePlacePointInclusion K G v x) =
      finitePlacePointInclusion K J v (G.affinePointsTarget f (placeCompletion K (.inr v)) x) := by
  apply ext_atPlace K J
  intro j
  rw [atPlace_map]
  by_cases hj : j = .inr v
  · subst j
    rw [atPlace_finitePlacePointInclusion, atPlace_finitePlacePointInclusion]
  · rw [atPlace_finitePlacePointInclusion_of_ne K G v j hj,
      atPlace_finitePlacePointInclusion_of_ne K J v j hj, map_one]

end Insertion

private def splitProjectionMulHomeomorph
    {H M : Type u} [Group H] [Group M] [TopologicalSpace H] [TopologicalSpace M]
    [IsTopologicalGroup H]
    (p : H →ₜ* M) (s : M →ₜ* H) (hps : ∀ x, p (s x) = x)
    (hcomm : ∀ (x : M) (y : p.toMonoidHom.ker), Commute (s x) (y : H)) :
    (M × p.toMonoidHom.ker) ≃ₜ* H where
  toFun a := s a.1 * (a.2 : H)
  invFun x := (p x, ⟨(s (p x))⁻¹ * x, by
    change p ((s (p x))⁻¹ * x) = 1
    rw [map_mul, map_inv, hps, inv_mul_cancel]⟩)
  left_inv a := by
    have hp : p (s a.1 * (a.2 : H)) = a.1 := by
      rw [map_mul, hps, show p a.2 = 1 from a.2.property, mul_one]
    apply Prod.ext hp
    apply Subtype.ext
    change (s (p (s a.1 * (a.2 : H))))⁻¹ * (s a.1 * (a.2 : H)) = a.2
    rw [hp, inv_mul_cancel_left]
  right_inv x := mul_inv_cancel_left _ _
  map_mul' a b := by
    change s (a.1 * b.1) * ((a.2 : H) * (b.2 : H)) =
      (s a.1 * (a.2 : H)) * (s b.1 * (b.2 : H))
    rw [map_mul]
    exact (hcomm b.1 a.2).mul_mul_mul_comm (s a.1) (b.2 : H)
  continuous_toFun := (s.continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := p.continuous.prodMk
    ((((s.continuous.comp p.continuous).inv).mul continuous_id).subtype_mk _)

section NormOne

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  (v : Langlands.Global.FinitePlace K)

/-- The actual finite-place projection restricted to the norm-one group. -/
def normOneFinitePlaceProjection :
    normOneSubgroup K G →ₜ* PlaceGroupPoints K G (.inr v) :=
  (atPlace K G (.inr v)).comp ⟨(normOneSubgroup K G).subtype, continuous_subtype_val⟩

variable (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

/-- The continuous section obtained by inserting the local point and removing
its positive torus factor. -/
def normOneFinitePlaceInclusion :
    PlaceGroupPoints K G (.inr v) →ₜ* normOneSubgroup K G :=
  (ContinuousMonoidHom.snd (intrinsicSubgroup K T) (normOneSubgroup K G)).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
      (normOneDecompositionMulEquiv K G T i hi I e hc).symm).comp (finitePlacePointInclusion K G v))

@[simp] theorem normOneFinitePlaceProjection_inclusion
    (x : PlaceGroupPoints K G (.inr v)) :
    normOneFinitePlaceProjection K G v (normOneFinitePlaceInclusion K G v T i hi I e hc x) = x := by
  change atPlace K G (.inr v)
    (normOneFactor K G T i hi I e (finitePlacePointInclusion K G v x)) = x
  rw [atPlace_normOneFactor, atPlace_finitePlacePointInclusion]

private theorem normOneFinitePlaceInclusion_commute_ker
    (x : PlaceGroupPoints K G (.inr v))
    (y : (normOneFinitePlaceProjection K G v).toMonoidHom.ker) :
    Commute (normOneFinitePlaceInclusion K G v T i hi I e hc x) (y.val : normOneSubgroup K G) := by
  let a := finitePlacePointInclusion K G v x
  let b : AdelicGroupPoints K G := y.val
  have hab : Commute a b := by
    apply ext_atPlace K G
    intro j
    rw [map_mul, map_mul]
    by_cases hj : j = .inr v
    · subst j
      have hb : atPlace K G (.inr v) b = 1 := y.property
      rw [hb, mul_one, one_mul]
    · have ha : atPlace K G j a = 1 := atPlace_finitePlacePointInclusion_of_ne K G v j hj x
      rw [ha, one_mul, mul_one]
  apply Subtype.ext
  change Commute (normOneFactor K G T i hi I e a : AdelicGroupPoints K G) b
  rw [normOneFactor_val]
  exact (positivePointMap_commute K G T i hc _ b).inv_left.mul_left hab

/-- The norm-one group splits as the actual finite local group times the
kernel of its projection. -/
def normOneFinitePlaceDecomposition :
    (PlaceGroupPoints K G (.inr v) × (normOneFinitePlaceProjection K G v).toMonoidHom.ker)
      ≃ₜ* normOneSubgroup K G :=
  splitProjectionMulHomeomorph (normOneFinitePlaceProjection K G v)
    (normOneFinitePlaceInclusion K G v T i hi I e hc)
    (normOneFinitePlaceProjection_inclusion K G v T i hi I e hc)
    (normOneFinitePlaceInclusion_commute_ker K G v T i hi I e hc)

@[simp] theorem normOneFinitePlaceDecomposition_symm_fst (x : normOneSubgroup K G) :
    ((normOneFinitePlaceDecomposition K G v T i hi I e hc).symm x).1 =
      normOneFinitePlaceProjection K G v x := rfl

variable (a : Aut G) (ha : i ≫ a.asIso.hom = i)

omit [IsAffine G.X.left] [(characterRestrict i).range.FiniteIndex] in
include ha in
private theorem adelicAut_positivePointMap (x : intrinsicSubgroup K T) :
    adelicAut K a (positivePointMap K G T i x) = positivePointMap K G T i x := by
  change AdelicGroupPoints.map K G G a.asIso.hom (AdelicGroupPoints.map K T.toGrp G i x.val) =
    AdelicGroupPoints.map K T.toGrp G i x.val
  rw [map_comp_apply, ha]

omit [IsAffine G.X.left] in
include ha in
private theorem normOneFactor_adelicAut (x : AdelicGroupPoints K G) :
    normOneFactor K G T i hi I e (adelicAut K a x) =
      normOneAut K a (normOneFactor K G T i hi I e x) := by
  let D := normOneDecompositionEquiv K G T i hi I e
  let p := positiveFactor K G T i hi I e x
  let y := normOneFactor K G T i hi I e x
  have h : D (p, normOneAut K a y) = adelicAut K a x := by
    have hx : (positivePointMap K G T i p) * (y : AdelicGroupPoints K G) = x :=
      positivePointMap_mul_normOneFactor K G T i hi I e x
    rw [← hx, map_mul (adelicAut K a), adelicAut_positivePointMap K G T i a ha]
    rfl
  exact congrArg Prod.snd ((congrArg D.symm h.symm).trans (D.symm_apply_apply _))

omit [IsAffine G.X.left] [(characterRestrict i).range.FiniteIndex] in
private theorem normOneFinitePlaceProjection_twist (x : normOneSubgroup K G) :
    normOneFinitePlaceProjection K G v (normOneAut K a x) =
      G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) (normOneFinitePlaceProjection K G v x) := by
  change atPlace K G (.inr v) (AdelicGroupPoints.map K G G a.asIso.hom x) = _
  rw [atPlace_map]
  rfl

include ha in
private theorem normOneFinitePlaceInclusion_twist (x : PlaceGroupPoints K G (.inr v)) :
    normOneAut K a (normOneFinitePlaceInclusion K G v T i hi I e hc x) =
      normOneFinitePlaceInclusion K G v T i hi I e hc
        (G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) x) := by
  change normOneAut K a (normOneFactor K G T i hi I e (finitePlacePointInclusion K G v x)) =
    normOneFactor K G T i hi I e
      (finitePlacePointInclusion K G v (G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) x))
  rw [← finitePlacePointInclusion_map, ← adelicAut_apply, normOneFactor_adelicAut K G T i hi I e a ha]

/-- The Galois or other algebraic twist restricts to the kernel of the
finite-place projection. -/
def normOneFinitePlaceKernelTwist (aut : Aut G) :
    (normOneFinitePlaceProjection K G v).toMonoidHom.ker →ₜ*
      (normOneFinitePlaceProjection K G v).toMonoidHom.ker := by
  let proj := normOneFinitePlaceProjection K G v
  let twist := normOneAut K aut
  let g (y : proj.toMonoidHom.ker) : proj.toMonoidHom.ker := ⟨twist y.val, by
    change normOneFinitePlaceProjection K G v (normOneAut K aut y.val) = 1
    have hy : normOneFinitePlaceProjection K G v y.val = 1 := y.property
    rw [normOneFinitePlaceProjection_twist K G v aut, hy, map_one]⟩
  exact
    { toFun := g
      map_one' := Subtype.ext (map_one twist)
      map_mul' x y := Subtype.ext (map_mul twist x.val y.val)
      continuous_toFun := (twist.continuous.comp continuous_subtype_val).subtype_mk _ }

set_option maxRecDepth 1800 in
include ha in
/-- The norm-one product decomposition intertwines an automorphism fixing the
positive torus with the product of its local and kernel actions. -/
theorem normOneFinitePlaceDecomposition_twist
    (p : PlaceGroupPoints K G (.inr v) × (normOneFinitePlaceProjection K G v).toMonoidHom.ker) :
    normOneAut K a (normOneFinitePlaceDecomposition K G v T i hi I e hc p) =
      normOneFinitePlaceDecomposition K G v T i hi I e hc
        (G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) p.1,
          normOneFinitePlaceKernelTwist K G v a p.2) := by
  change normOneAut K a (normOneFinitePlaceInclusion K G v T i hi I e hc p.1 * p.2.val) =
    normOneFinitePlaceInclusion K G v T i hi I e hc
      (G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) p.1) * normOneAut K a p.2.val
  rw [map_mul (normOneAut K a), normOneFinitePlaceInclusion_twist K G v T i hi I e hc a ha]

end NormOne

/-- A finite local group is a direct factor in the actual norm-one group
and the factorization commutes with automorphisms fixing the positive torus. -/
def NormOneFinitePlaceSplitStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
    (v : Langlands.Global.FinitePlace K)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
    (_hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (_hc : IsCentral i),
    let p := normOneFinitePlaceProjection K G v
    let J := p.toMonoidHom.ker
    ∃ D : (PlaceGroupPoints K G (.inr v) × J) ≃ₜ* normOneSubgroup K G,
      (∀ x, (D.symm x).1 = p x) ∧
      ∀ (a : Aut G), i ≫ a.asIso.hom = i →
        ∀ z, normOneAut K a (D z) =
          D (G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v)) z.1,
            normOneFinitePlaceKernelTwist K G v a z.2)

set_option maxRecDepth 1800 in
theorem normOneFinitePlaceSplit : NormOneFinitePlaceSplitStatement.{u} := by
  intro K _ _ G _ v T i hi _ I _ e hc p J
  exact ⟨normOneFinitePlaceDecomposition K G v T i hi I e hc,
    normOneFinitePlaceDecomposition_symm_fst K G v T i hi I e hc,
    normOneFinitePlaceDecomposition_twist K G v T i hi I e hc⟩

end Langlands.TraceFormula
