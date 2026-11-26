import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.PlaceTensorSliceNonzero
import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.InfiniteWhittakerSmoothSlice
import Langlands.Global.RankinSelberg.WhittakerIdentityEmbeddings
import Langlands.Representation.Category.CentralCharacterRegularity

/-! # Archimedean Whittaker slice comparison for a cuspidal tensor presentation -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000
set_option Elab.async false

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic ArchimedeanGL InfinitePlaceFamily InfiniteWhittakerSlice
open ArchimedeanWhittakerRegularity Langlands.Archimedean Langlands.HarishChandraSchwartz
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.ClassFieldTheory.Global.RelativeWeilGroup

universe u uQ

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

section Twist

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

private theorem unitarizingCharacter_adelic_compact (central : HeckeCharacter F)
    (k : standardInfiniteCompact F (r + 1)) :
    (unitarizingCharacter r central).adelicDeterminant (r + 1)
      (AdelicGL.ofInfinite F (r + 1) k.val) = 1 := by
  let n := r + 1
  let f : standardInfiniteCompact F n →* ℂˣ :=
    (central.adelicDeterminant n).toMonoidHom.comp
      ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)
  have hf : Continuous f := (central.adelicDeterminant n).continuous.comp
    ((AdelicGL.ofInfinite F n).continuous.comp continuous_subtype_val)
  have hk := Langlands.norm_eq_one_of_compact_quotient f hf ⊥ (by
    intro z hz
    rw [Subgroup.mem_bot.mp hz, map_one, Units.val_one, norm_one]) k
  apply Units.ext
  change ((‖(f k : ℂ)‖ ^ (-1 / ((r : ℝ) + 1)) : ℝ) : ℂ) = (1 : ℂ)
  rw [hk, Real.one_rpow, Complex.ofReal_one]

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
private theorem whittaker_one_congr (χ : AddChar (Adeles F) ℂ)
    {f f' : Points F (r + 1) → ℂ}
    (h : ∀ x : unipotentAdelic F (r + 1), f x.val = f' x.val) :
    generalLinearWhittakerFunction F r χ (fun _ => 1) f 1 =
      generalLinearWhittakerFunction F r χ (fun _ => 1) f' 1 := by
  simp only [generalLinearWhittakerFunction, subgroupCharacterCoefficient, mul_one]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
    congrArg (· * _) (h (Quotient.out x)))

private theorem cuspWhittaker_heckeDeterminantTwist_one (T : CuspidalOperatorRealization F r)
    (ν : HeckeCharacter F) (χ : AddChar (Adeles F) ℂ) (v : T.Space) :
    cuspWhittaker F (T.heckeDeterminantTwist ν) χ (T.realization.heckeDeterminantTwistEquiv ν v) 1 =
      cuspWhittaker F T χ v 1 := by
  let m := r + 1
  let S := T.heckeDeterminantTwist ν
  let w : S.Space := T.realization.heckeDeterminantTwistEquiv ν v
  have h (x : unipotentAdelic F m) : cuspFunction F S w x.val = cuspFunction F T v x.val := by
    let g := GeneralLinearGroupPoints.adelicEquiv F m x.val
    have hdet : AdelicGL.determinant F m g = 1 := by
      apply Units.ext
      exact (Unfolding.isUnitriangular_of_mem_unipotentAdelic F x).det_eq_one
    have hν : ν.adelicDeterminant m g = 1 := by
      change ν.onIdeles (AdelicGL.determinant F m g) = 1
      rw [hdet, map_one]
    have he := T.realization.evaluate_heckeDeterminantTwistEquiv ν v g
    let fx := ContinuousRationalFunctions.evaluate F m (T.realization.toContinuous v) g
    have ht : (ν.adelicDeterminant m g : ℂ) * fx = fx :=
      (congrArg (fun z : ℂˣ => (z : ℂ) * fx) hν).trans (one_mul fx)
    exact (RealPlaceWhittaker.cuspFunction_eq_evaluate F S w x.val).trans
      (he.trans (ht.trans (RealPlaceWhittaker.cuspFunction_eq_evaluate F T v x.val).symm))
  exact whittaker_one_congr χ h

end Twist

section ScalarShift

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V] [Module ℂ V]

private def shiftLieAction (d : L →ₗ⁅ℂ⁆ Module.End ℂ V) (scalar : L →ₗ[ℂ] ℂ)
    (hscalar : ∀ X Y : L, scalar ⁅X, Y⁆ = 0) : L →ₗ⁅ℂ⁆ Module.End ℂ V :=
  { d.toLinearMap + (Algebra.linearMap ℂ (Module.End ℂ V)).comp scalar with
    map_lie' := by
      intro X Y
      change d ⁅X, Y⁆ + algebraMap ℂ (Module.End ℂ V) (scalar ⁅X, Y⁆) =
        (d X + algebraMap ℂ (Module.End ℂ V) (scalar X)) * (d Y + algebraMap ℂ (Module.End ℂ V) (scalar Y)) -
        (d Y + algebraMap ℂ (Module.End ℂ V) (scalar Y)) * (d X + algebraMap ℂ (Module.End ℂ V) (scalar X))
      rw [hscalar, map_zero, add_zero, LieHom.map_lie]
      have hX := Algebra.commutes (scalar X) (d Y)
      have hY := Algebra.commutes (scalar Y) (d X)
      have hXY := (Commute.all (scalar X) (scalar Y)).map (algebraMap ℂ (Module.End ℂ V))
      rw [LieRing.of_associative_ring_bracket, add_mul, add_mul, mul_add, mul_add, mul_add, mul_add,
        hX, hY, hXY.eq]
      abel }

private theorem shiftLieAction_apply (d : L →ₗ⁅ℂ⁆ Module.End ℂ V) (scalar : L →ₗ[ℂ] ℂ)
    (hscalar : ∀ X Y : L, scalar ⁅X, Y⁆ = 0) (X : L) (v : V) :
    shiftLieAction d scalar hscalar X v = d X v + scalar X • v := rfl

private theorem shiftLieAction_irreducible {K : Type*} [Group K]
    (k : Representation ℂ K V) (d : L →ₗ⁅ℂ⁆ Module.End ℂ V) (scalar : L →ₗ[ℂ] ℂ)
    (hscalar : ∀ X Y : L, scalar ⁅X, Y⁆ = 0) (hirr : IsIrreducibleGKModule k d) :
    IsIrreducibleGKModule k (shiftLieAction d scalar hscalar) := by
  refine ⟨hirr.1, fun W hK hD => hirr.2 W hK ?_⟩
  intro X v hv
  have h := W.sub_mem (hD X v hv) (W.smul_mem (scalar X) hv)
  simpa only [shiftLieAction_apply, add_sub_cancel_right] using h

private theorem algAction_add_scalar {A : Type*} [Ring A] [Algebra ℂ A]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (a : A) (c : ℂ) (v : V) :
    ρ (a + algebraMap ℂ A c) v = ρ a v + c • v := by
  calc
    _ = (ρ a + ρ (algebraMap ℂ A c)) v := congrArg (fun m : Module.End ℂ V => m v) (map_add ρ _ _)
    _ = (ρ a + algebraMap ℂ (Module.End ℂ V) c) v :=
      congrArg (fun m : Module.End ℂ V => (ρ a + m) v) (ρ.commutes c)
    _ = _ := rfl

private theorem finiteVector_of_stable {K : Type*} [Group K] (k : Representation ℂ K V) (v : V)
    (h : ∃ W : Submodule ℂ V, v ∈ W ∧ FiniteDimensional ℂ W ∧
      ∀ g w, w ∈ W → k g w ∈ W) : FiniteVectors.IsFiniteVector k v := by
  obtain ⟨W, hv, hdim, hW⟩ := h
  exact (FiniteVectors.isFiniteVector_iff k v).mpr
    ⟨{ toSubmodule := W, apply_mem_toSubmodule := fun g _ hw => hW g _ hw }, hdim, hv⟩

end ScalarShift

section Slices

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u,uQ} T) (hP : HasIrreducibleAdmissibleComponents P)
  (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)

local notation "n" => r + 1
local notation "V" => T.placeDensityModels.subspace

private theorem sliceMap_identity (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j) (v : V i) :
    sliceMap P hP χ hχ a i b 1 v 1 = cuspWhittaker F T χ (sliceVector P hP a i b v) 1 := by
  have hg : Function.update (1 : PlaceTuple (F := F) n) i 1 = 1 :=
    Function.update_eq_self_iff.mpr rfl
  exact congrArg (cuspWhittaker F T χ (sliceVector P hP a i b v))
    ((congrArg (placeTuplePoint n) hg).trans (placeTuplePoint_one (F := F) (r := r)))

include hχ in
private theorem sliceVector_reference_ne_zero (a₀ : FiniteTensor P) (b₀ : ∀ j, V j)
    (h₀ : tensorWhittaker P hP χ a₀ b₀ 1 ≠ 0) (i : Index F) :
    cuspWhittaker F T χ (sliceVector P hP a₀ i b₀ (b₀ i)) 1 ≠ 0 := by
  have hb : Function.update b₀ i (b₀ i) = b₀ := Function.update_eq_self_iff.mpr rfl
  have hg : Function.update (1 : PlaceTuple (F := F) n) i 1 = 1 :=
    Function.update_eq_self_iff.mpr rfl
  intro hz
  apply h₀
  exact (congrArg₂ (tensorWhittaker P hP χ a₀) hb hg).symm.trans
    ((sliceMap_apply P hP χ hχ a₀ i b₀ 1 (b₀ i) 1).symm.trans
      ((sliceMap_identity P hP χ hχ a₀ i b₀ (b₀ i)).trans hz))

set_option maxHeartbeats 75000 in
private theorem sliceIdentity_proportional_of_center (a₀ : FiniteTensor P) (b₀ : ∀ j, V j)
    (h₀ : tensorWhittaker P hP χ a₀ b₀ 1 ≠ 0)
    (central : HeckeCharacter F) (hcentral : T.HasCentralCharacter central)
    (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j) :
    ∃ s : ℂ, ∀ v : V i, sliceMap P hP χ hχ a i b 1 v 1 =
      s * sliceMap P hP χ hχ a₀ i b₀ 1 v 1 := by
  let twistChar := unitarizingCharacter r central
  let S := T.heckeDeterminantTwist twistChar
  let E : T.Space ≃ₗ[ℂ] S.Space := (T.realization.heckeDeterminantTwistEquiv twistChar).toLinearEquiv
  let A := T.finiteInfiniteDecomposition
  let D := T.placeDensityModels
  let tailFinite : Bool → FiniteTensor P := fun t => if t then a else a₀
  let tailInfinite : Bool → ∀ j, V j := fun t => if t then b else b₀
  let J (t : Bool) := sliceVector P hP (tailFinite t) i (tailInfinite t)
  let J' (t : Bool) : V i →ₗ[ℂ] S.Space := E.toLinearMap.comp (J t)
  have href := sliceVector_reference_ne_zero P hP χ hχ a₀ b₀ h₀ i
  let evalOne := UnramifiedWhittaker.whittakerFunctional F χ hχ T 1
  have hJ₀ : evalOne.comp (J false) ≠ 0 := by
    intro h
    exact href (LinearMap.congr_fun h (b₀ i))
  have htail := D.tensorSlice_fixedFactors_ne_zero A.finite T.irreducible A.nonzero A.irreducible
    A.admissible i (P.finiteTensorEquiv hP a₀) b₀ evalOne hJ₀
  have hJinj : Function.Injective (J false) :=
    D.tensorSlice_injective A.finite T.irreducible A.nonzero A.irreducible A.admissible
      i (P.finiteTensorEquiv hP a₀) b₀ htail.1 htail.2
  let δ := complexCharacterDifferential (twistChar.infiniteDeterminantCharacter n)
    (twistChar.infiniteDeterminantCharacter_mem_smoothFunctions n)
  let δi := δ.comp (lieInclusion n i).toLinearMap
  have hδi (X Y : Lie n i) : δi ⁅X, Y⁆ = 0 := by
    change δ (lieInclusion n i ⁅X, Y⁆) = 0
    rw [LieHom.map_lie]
    exact complexCharacterDifferential_lie _ _ _ _
  let d := shiftLieAction (D.sourceLie i) δi hδi
  have hk (t : Bool) (k : Compact n i) (v : V i) :
      J' t (D.sourceCompact i k v) = S.realization.placeCompactFamily i k (J' t v) := by
    let k₀ := compactInclusion n i k
    have h := T.realization.heckeDeterminantTwistEquiv_compact twistChar k₀ (J t v)
    have ht : twistChar.adelicDeterminant n (AdelicGL.ofInfinite F n k₀.val) = 1 :=
      unitarizingCharacter_adelic_compact central k₀
    have he := congrArg (fun z : ℂˣ => (z : ℂ) • E (T.realization.compactRepresentation k₀ (J t v))) ht
    exact (congrArg E (sliceVector_compact P hP (tailFinite t) i (tailInfinite t) k v)).trans
      (h.trans (he.trans (one_smul ℂ _))).symm
  have hd (t : Bool) (X : Lie n i) (v : V i) :
      J' t (d X v) = S.realization.placeLieFamily i X (J' t v) := by
    let X₀ := lieInclusion n i X
    let generator := envelopingGenerator F n X₀
    let ρ := T.realization.envelopingAction
    have hshift : heckeEnvelopingShift n twistChar generator =
        generator + algebraMap ℂ (EnvelopingAlgebra F n) (δi X) :=
      envelopingShift_generator δ (complexCharacterDifferential_lie _ _) X₀
    have he : ρ (heckeEnvelopingShift n twistChar generator) (J t v) =
        ρ generator (J t v) + δi X • J t v :=
      (congrArg (fun y => ρ y (J t v)) hshift).trans (algAction_add_scalar ρ generator (δi X) (J t v))
    have hjd : J t (d X v) = ρ generator (J t v) + δi X • J t v :=
      (congrArg (J t) (shiftLieAction_apply (D.sourceLie i) δi hδi X v)).trans
        ((map_add (J t) _ _).trans
          (congrArg₂ (· + ·) (sliceVector_lie P hP (tailFinite t) i (tailInfinite t) X v)
            (map_smul (J t) (δi X) v)))
    calc
      J' t (d X v) = E (ρ generator (J t v) + δi X • J t v) := congrArg E hjd
      _ = E (ρ (heckeEnvelopingShift n twistChar generator) (J t v)) := congrArg E he.symm
      _ = S.realization.placeLieFamily i X (J' t v) :=
        (T.realization.heckeDeterminantTwistEquiv_differential twistChar generator (J t v)).symm
  have hfix (t : Bool) : ∃ B : CompactOpenSubgroup (FiniteAdelicGL F n),
      ∀ (g : B.toSubgroup) v, S.realization.finiteRepresentation g.val (J' t v) = J' t v := by
    have hU := D.exists_compactOpen_fixes_tensorSlice A.finite T.irreducible A.nonzero A.irreducible
      A.admissible i (P.finiteTensorEquiv hP (tailFinite t)) (tailInfinite t)
    refine hU.elim fun U hU => ?_
    have hlevels := OperatorRealization.exists_compact_openSubgroup_le (U ⊓ twistChar.heckeFiniteDeterminantKernel n)
    refine hlevels.elim fun B hB => ⟨⟨B, hB.2⟩, fun g v => ?_⟩
    have hg : g.val ∈ U ∧ g.val ∈ twistChar.heckeFiniteDeterminantKernel n := hB.1 g.property
    have ht := (HeckeCharacter.mem_heckeFiniteDeterminantKernel n twistChar g.val).mp hg.2
    have he := T.realization.heckeDeterminantTwistEquiv_finite twistChar g.val (J t v)
    have hs : T.realization.finiteRepresentation g.val (J t v) = J t v := hU.2 g.val hg.1 v
    exact he.trans ((congrArg₂ (fun z : ℂˣ => fun x : S.Space => (z : ℂ) • x) ht (congrArg E hs)).trans
      (one_smul ℂ _))
  have hW (t : Bool) (v : V i) : cuspWhittaker F S χ (J' t v) 1 = cuspWhittaker F T χ (J t v) 1 :=
    cuspWhittaker_heckeDeterminantTwist_one T twistChar χ (J t v)
  have hfin (v : V i) : FiniteVectors.IsFiniteVector (D.sourceCompact i) v :=
    finiteVector_of_stable (D.sourceCompact i) v ((D.densityHyp i).finite v)
  have h := proportional_cuspWhittaker_one_of_placeEmbeddings S
    (hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T hcentral) χ hχ i
    (D.sourceCompact i) d (shiftLieAction_irreducible _ _ _ _ (D.densityHyp i).irreducible)
    (D.densityHyp i).admissible hfin J' (E.injective.comp hJinj) hk hd hfix
    ⟨b₀ i, fun h => href ((hW false _).symm.trans h)⟩
  exact h.elim fun s hs => ⟨s, fun v => (sliceMap_identity P hP χ hχ a i b v).trans
    ((hW true v).symm.trans ((hs v).trans
      (congrArg (s * ·) ((hW false v).trans (sliceMap_identity P hP χ hχ a₀ i b₀ v).symm))))⟩

end Slices

/-- The normalized model from a nonzero pure tensor contains every one-place
slice of the supplied cuspidal spectral presentation. -/
theorem infiniteWhittakerSliceModel : InfiniteWhittakerSliceModelStatement.{u,uQ} := by
  intro F _ _ _ r T P hP χ hχ _ _ _ _
  obtain ⟨a₀, b₀, h₀⟩ := exists_tensorWhittaker_one_ne_zero P hP χ hχ
  have hc : ∃ central : HeckeCharacter F, T.HasCentralCharacter central :=
    (T.realization.existsUnique_hasCentralCharacter T.irreducible).exists
  exact hc.elim fun central hcentral =>
    nonempty_modelData_of_eval_one P hP χ hχ a₀ b₀ h₀
      (sliceIdentity_proportional_of_center P hP χ hχ a₀ b₀ h₀ central hcentral)

end Langlands.Global.RankinSelbergGlobal
