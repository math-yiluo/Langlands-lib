import Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint
import Langlands.Geometry.Building.SplitTorusTranslationBaseChange
import Langlands.Geometry.Building.RootValueTorusFieldValuation
import Langlands.Geometry.Building.GaloisTranslationAction
import Langlands.Geometry.Building.RootBuildingGaloisFieldExtension
import Langlands.Geometry.Building.ReflectionRealizationUniqueness
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Geometry.Building.KPApartmentGaloisTransport
import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Normalizer shifts of the descended quasi-split apartment family -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits

namespace Langlands.Geometry.Building

section Averaging

variable {Γ W : Type*} [Group Γ] [Fintype Γ] [AddCommGroup W] [Module ℝ W]
  (ρ : Γ →* (W ≃ₗ[ℝ] W))

/-- The average of a vector over a finite group of linear automorphisms. -/
def linearAverage (w : W) : W :=
  (Fintype.card Γ : ℝ)⁻¹ • ∑ σ : Γ, ρ σ w

theorem linearAverage_fixed (w : W) (τ : Γ) : ρ τ (linearAverage ρ w) = linearAverage ρ w := by
  simp only [linearAverage, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [Equiv.coe_mulLeft, map_mul, LinearEquiv.mul_apply]

theorem linearAverage_sub_mem (U : Submodule ℝ W) (w : W) (hw : ∀ σ : Γ, ρ σ w - w ∈ U) :
    linearAverage ρ w - w ∈ U := by
  have hN : (Fintype.card Γ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : linearAverage ρ w - w = (Fintype.card Γ : ℝ)⁻¹ • ∑ σ : Γ, (ρ σ w - w) := by
    rw [linearAverage, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [hsum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => hw σ)

end Averaging

section GaloisFixedVectors

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  (t : S ⟶ T) (hS : IsSplitTorus S.toGrp)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t

/-- Real cocharacters of the original split torus, pushed into the extended torus. -/
def descentCocharacterMap : V S →ₗ[ℝ] V T_K :=
  (cocharacterMapReal t_K).comp (splitCocharacterBaseChange (K := K) S hS).toLinearMap

@[simp] theorem descentCocharacterMap_tmul (r : ℝ) (ξ : cocharacterLattice S) :
    descentCocharacterMap k K t hS (r ⊗ₜ[ℤ] ξ) =
      r ⊗ₜ[ℤ] (cocharacterLattice.baseChange b S ξ ≫ t_K) := rfl

theorem eval_descentCocharacterMap (χ : characterLattice T_K) (v : V S) :
    eval T_K χ (descentCocharacterMap k K t hS v) =
      eval (CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S) (t_K ≫ χ)
        (splitCocharacterBaseChange (K := K) S hS v) := by
  rw [descentCocharacterMap, LinearMap.comp_apply, eval_eq_pair, eval_eq_pair,
    pair_cocharacterMapReal]
  rfl

variable [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [IsAffineHom T.X.hom]

/-- Galois orbit sums of real cocharacters of the extended torus come from the
largest split subtorus. -/
theorem sum_galoisCocharacterAction_mem_range
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t)) (u : V T_K) :
    ∑ σ : K ≃ₐ[k] K, galoisCocharacterAction k K T σ u ∈
      LinearMap.range (descentCocharacterMap k K t hS) := by
  induction u using TensorProduct.inductionOn with
  | tmul r ν =>
    have h : ∑ σ : K ≃ₐ[k] K, galoisCocharacterAction k K T σ (r ⊗ₜ[ℤ] ν) =
        r ⊗ₜ[ℤ] CocharacterAveraging.galoisOrbitSum k K T ν := by
      simp only [galoisCocharacterAction_tmul, ← TensorProduct.tmul_sum]
      rfl
    rw [h, ← CocharacterAveraging.baseChange_descendedOrbitSum k K T ν]
    obtain ⟨g, hg, -⟩ := ht.2 (Gm (Spec (CommRingCat.of k)))
      (CommGroupScheme.groupHom (CocharacterAveraging.descendedOrbitSum k K T ν)) isSplitTorus_gm
    let ξ : cocharacterLattice S := Additive.ofMul g
    have hξ : ξ ≫ t = CocharacterAveraging.descendedOrbitSum k K T ν :=
      congrArg Additive.ofMul hg
    refine ⟨r ⊗ₜ[ℤ] ξ, ?_⟩
    rw [descentCocharacterMap_tmul, ← hξ, cocharacterLattice.baseChange_comp]
  | add x y hx hy =>
    simp only [map_add, Finset.sum_add_distrib]
    exact add_mem hx hy

/-- **Galois-fixed real cocharacters descend to the largest split subtorus.** -/
theorem exists_descentCocharacterMap_eq
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t)) (w : V T_K)
    (hw : ∀ σ : K ≃ₐ[k] K, galoisCocharacterAction k K T σ w = w) :
    ∃ v : V S, descentCocharacterMap k K t hS v = w := by
  have hmem := sum_galoisCocharacterAction_mem_range k K t hS ht w
  simp only [hw, Finset.sum_const, Finset.card_univ] at hmem
  have hc : (Fintype.card (K ≃ₐ[k] K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw' : w = (Fintype.card (K ≃ₐ[k] K) : ℝ)⁻¹ • (Fintype.card (K ≃ₐ[k] K) • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨v, hv⟩ := Submodule.smul_mem _ ((Fintype.card (K ≃ₐ[k] K) : ℝ)⁻¹) hmem
  exact ⟨v, hv.trans hw'.symm⟩

end GaloisFixedVectors

section Bridge

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Normalizer points of two equal torus maps with the same ambient point act equally on
root function families. -/
theorem RootFunctionFamily.smul_eq_of_map_eq {ι₁ ι₂ : S.toGrp ⟶ G}
    [Mono ι₁.hom.hom.left] [Mono ι₂.hom.hom.left] (h : ι₁ = ι₂)
    (n₁ : normalizerPoints ι₁) (n₂ : normalizerPoints ι₂)
    (hn : (n₁ : rationalPoints G) = n₂) (ψ : RootFunctionFamily S G) :
    n₁ • ψ = n₂ • ψ := by
  subst h
  have : n₁ = n₂ := Subtype.ext hn
  subst this
  rfl

/-- The torus-restricted family depends only on the upper family. -/
theorem torusRestrictedRootFunctionFamily_congr {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) {φ₁ φ₂ : RootFunctionFamily T G}
    (h : φ₁ = φ₂) (h₁ : IsRootDatumValuation i φ₁) (h₂ : IsRootDatumValuation i φ₂)
    (f : S ⟶ T) :
    torusRestrictedRootFunctionFamily hS hT hE h₁ f =
      torusRestrictedRootFunctionFamily hS hT hE h₂ f := by
  subst h
  rfl

end Bridge

section CentralizerConverse

namespace IntegerValuation

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {h : Function.Bijective (Cartan.restrictionEvaluation s)}

/-- Full V6 follows once every centralizer point acts on the family by the KP translation. -/
theorem isCentralizerCompatible_of_smul_eq_vadd
    (hj : (torusCentralizer i).IsRepresentedBy j) {φ : RootFunctionFamily S G}
    (hφ : ∀ z : rationalPoints Z,
      centralizerToNormalizer i j hj z • φ = (centralizerTranslation v s h z).toAdd +ᵥ φ) :
    IsCentralizerCompatible v i j s h φ := by
  intro a _ z u _
  have hw : weylAction i (centralizerToNormalizer i j hj z)⁻¹ = 1 := by
    rw [← map_inv]
    exact weylAction_centralizerToNormalizer hj z⁻¹
  have hz := congrArg (fun ψ : RootFunctionFamily S G => ψ a u) (hφ z)
  simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hw,
    LinearEquiv.coe_one, id, coe_centralizerToNormalizer] at hz
  rw [hz, add_comm]

end IntegerValuation

end CentralizerConverse

section TorusPointGalois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T

/-- The scalar extension of a rational point of the original torus, viewed in the split
torus over the extension. -/
abbrev torusPointExtend (z : rationalPoints T.toGrp) : rationalPoints (T_K).toGrp :=
  rationalExtend k K T.toGrp z

/-- A scalar-extended original torus point is fixed by the coefficient action. -/
theorem rationalConjugate_torusPointExtend (z : rationalPoints T.toGrp) (σ : K ≃ₐ[k] K) :
    rationalConjugate k K T.toGrp σ (torusPointExtend (K := K) z) =
      torusPointExtend (K := K) z :=
  GaloisPointComparison.rationalConjugate_rationalExtend k K T.toGrp σ z

/-- Character values of a scalar-extended original torus point are covariant for the
coefficient action. -/
theorem rationalCharacterEval_galoisRepresentation_torusPointExtend
    (z : rationalPoints T.toGrp) (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
        (characterLattice.galoisRepresentation k K T σ χ)) (torusPointExtend (K := K) z) =
      Units.map σ.toMonoidHom
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm χ)
          (torusPointExtend (K := K) z)) := by
  have hg := GaloisPointComparison.rationalCharacterEval_galois k K T σ χ
    (torusPointExtend (K := K) z)
  exact (congrArg (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
    (characterLattice.galoisRepresentation k K T σ χ)))
      (rationalConjugate_torusPointExtend z σ)).symm.trans hg

/-- With a Galois-invariant order function, the translation vector of a scalar-extended
original torus point is fixed by the coefficient action. -/
theorem galoisCocharacterAction_eq_of_eval_eq_neg_order (hT : IsSplitTorus (T_K).toGrp)
    {ω : Kˣ → ℝ} (hω : ∀ (σ : K ≃ₐ[k] K) (x : Kˣ), ω (Units.map σ.toMonoidHom x) = ω x)
    (z : rationalPoints T.toGrp) (w : V T_K)
    (hw : ∀ a, eval T_K a w = -ω (rationalCharacterEval
        ((rationalCharacters.equivCharacterLattice T_K).symm a) (torusPointExtend (K := K) z)))
    (σ : K ≃ₐ[k] K) : galoisCocharacterAction k K T σ w = w := by
  have key : ∀ (τ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      eval T_K (characterLattice.galoisRepresentation k K T τ χ) w = eval T_K χ w := by
    intro τ χ
    have h1 := hw (characterLattice.galoisRepresentation k K T τ χ)
    rw [rationalCharacterEval_galoisRepresentation_torusPointExtend, hω] at h1
    rw [h1, hw]
  rw [← sub_eq_zero]
  apply Cartan.eq_zero_of_eval_eq_zero hT
  intro χ
  rw [map_sub, eval_galoisCocharacterAction_right, key, sub_self]

end TorusPointGalois

section Shifts

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (t : S ⟶ T) (jT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left]

/-- **Torus restriction of an upper normalizer translation.** If an original normalizer
point of `i` also normalizes `jT`, acts on the upper family by a translation `w`, and `w`
agrees on all upper roots with the push-forward of an original real cocharacter `v`, then
its scalar extension shifts the torus-restricted family by the base change of `v`. -/
theorem normalizerPointsFieldExtend_smul_torusRestricted
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hfactor : CommGroupScheme.groupHom t_K ≫ j_K = i_K)
    (n : normalizerPoints i) (n0 : normalizerPoints jT)
    (hn : (n0 : rationalPoints G) = n) (w : V T_K)
    (hw : normalizerPointsFieldExtend (K := K) jT n0 • φ = w +ᵥ φ) (v : V S)
    (hv : w - descentCocharacterMap k K t hS v ∈ rootAnnihilator (S := T_K) j_K) :
    normalizerPointsFieldExtend (K := K) i n •
        torusRestrictedRootFunctionFamily (T := T_K) (i := j_K) (hS.baseChange b) hT hE hφ t_K =
      splitCocharacterBaseChange (K := K) S hS v +ᵥ
        torusRestrictedRootFunctionFamily (T := T_K) (i := j_K) (hS.baseChange b) hT hE hφ t_K := by
  set nT := normalizerPointsFieldExtend (K := K) jT n0 with hnT
  have hw' : nT • φ =
      cocharacterMapReal t_K (splitCocharacterBaseChange (K := K) S hS v) +ᵥ φ := by
    rw [hw]
    exact (hφ.vadd_eq_vadd_iff).2 hv
  have hmono : Mono (CommGroupScheme.groupHom t_K ≫ j_K).hom.hom.left := by
    rw [hfactor]
    infer_instance
  let nS : normalizerPoints (CommGroupScheme.groupHom t_K ≫ j_K) :=
    ⟨rationalExtend k K G n, by
      rw [hfactor]
      exact (normalizerPointsFieldExtend (K := K) i n).property⟩
  have hnS : (nS : rationalPoints G_K) = (nT : rationalPoints G_K) := by
    change rationalExtend k K G n = rationalExtend k K G n0
    rw [hn]
  have h1 := torusRestrictedRootFunctionFamily_normalizer_smul t_K nS nT hnS
    (hS.baseChange b) hT hE hφ
  have h2 := torusRestrictedRootFunctionFamily_vadd (hS.baseChange b) hT hE hφ t_K
    (splitCocharacterBaseChange (K := K) S hS v)
  have hcongr := torusRestrictedRootFunctionFamily_congr (hS.baseChange b) hT hE hw'
    (hφ.normalizer_smul nT) (hφ.vadd _) t_K
  rw [← RootFunctionFamily.smul_eq_of_map_eq hfactor nS
    (normalizerPointsFieldExtend (K := K) i n) rfl]
  exact h1.symm.trans (hcongr.trans h2)

omit [Smooth G.X.hom] in
/-- **Galois-fixed upper translations descend.** For a Galois-fixed upper family and a
scalar-extended original normalizer point acting on it by `w`, some original real
cocharacter agrees with `w` on all upper roots. -/
theorem exists_descentCocharacterMap_sub_mem
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [IsAffineHom T.X.hom]
    (hS : IsSplitTorus S.toGrp)
    {φ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (n0 : normalizerPoints jT) (w : V T_K)
    (hw : normalizerPointsFieldExtend (K := K) jT n0 • φ = w +ᵥ φ) :
    ∃ v : V S, w - descentCocharacterMap k K t hS v ∈ rootAnnihilator (S := T_K) j_K := by
  set nT := normalizerPointsFieldExtend (K := K) jT n0 with hnT
  have hnTfix : ∀ σ : K ≃ₐ[k] K, normalizerGaloisAction k K jT σ nT = nT := fun σ =>
    Subtype.ext (rationalConjugate_rationalExtend k K G σ _)
  have hσw : ∀ σ : K ≃ₐ[k] K,
      galoisCocharacterAction k K T σ w - w ∈ rootAnnihilator (S := T_K) j_K := by
    intro σ
    have h1 := RootFunctionFamily.galoisAction_smul k K jT σ nT φ
    rw [hnTfix σ, hfix σ, hw, RootFunctionFamily.galoisAction_vadd, hfix σ] at h1
    exact (hφ.vadd_eq_vadd_iff).1 h1
  obtain ⟨v, hv⟩ := exists_descentCocharacterMap_eq k K t hS ht
    (linearAverage (galoisCocharacterAction k K T) w)
    (linearAverage_fixed (galoisCocharacterAction k K T) w)
  refine ⟨v, ?_⟩
  rw [hv, ← neg_sub]
  exact neg_mem (linearAverage_sub_mem (galoisCocharacterAction k K T) _ w hσw)

/-- **Original-point normalizer shifts.** For a Galois-fixed point of a normalizer-stable
upper apartment class, every original normalizer point that also normalizes `jT` gives
the original-point shift condition of the torus-then-field restricted family. -/
theorem torusFieldOriginalPointShifts_of_galoisFixed
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [IsAffineHom T.X.hom]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K) {ω : Kˣ → ℝ}
    (D : KPApartmentData (S := T_K) j_K ω) (x : D.Apartment)
    (hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val)
    (hfactor : CommGroupScheme.groupHom t_K ≫ j_K = i_K)
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (hnorm : ∀ n : normalizerPoints i, (n : rationalPoints G) ∈ normalizerPoints jT) :
    TorusFieldOriginalPointShifts i hS hT hE x.isValuation t_K := by
  intro n
  let n0 : normalizerPoints jT := ⟨n, hnorm n⟩
  obtain ⟨w, hw⟩ := (D.mem_iff_equipollent x.mem).1
    (D.smul_mem (normalizerPointsFieldExtend (K := K) jT n0) x.val x.mem)
  obtain ⟨v, hv⟩ := exists_descentCocharacterMap_sub_mem t jT hS x.isValuation hfix ht n0 w hw
  refine ⟨v, fun a _ g _ => ?_⟩
  rw [normalizerPointsFieldExtend_smul_torusRestricted i t jT hS hT hE x.isValuation hfactor
    n n0 rfl w hw v hv, RootFunctionFamily.vadd_apply, eval_splitCocharacterBaseChange]


omit [Smooth G.X.hom] in
/-- A rational point of the original torus that centralizes `jT` acts on a split-torus
compatible upper valuation by a translation with the negative order values. -/
theorem exists_centralizer_translation_upper (hT : IsSplitTorus (T_K).toGrp) {ω : Kˣ → ℝ}
    (hadd : ∀ x y : Kˣ, ω (x * y) = ω x + ω y)
    {φ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hcompat : IsSplitTorusCompatible (S := T_K) j_K ω φ)
    (z : rationalPoints T.toGrp) (n0 : normalizerPoints jT)
    (hn0 : (n0 : rationalPoints G) = rationalPoints.map jT z)
    (hn0c : (n0 : rationalPoints G) ∈ centralizerPoints jT) :
    ∃ w : V T_K, (∀ a, eval T_K a w = -ω (rationalCharacterEval
        ((rationalCharacters.equivCharacterLattice T_K).symm a) (torusPointExtend (K := K) z))) ∧
      normalizerPointsFieldExtend (K := K) jT n0 • φ = w +ᵥ φ := by
  obtain ⟨w, hw⟩ := exists_eval_eq_neg_order hT ω hadd (torusPointExtend (K := K) z)
  refine ⟨w, hw, ?_⟩
  let zc : centralizerPoints (T := T_K) j_K :=
    ⟨(normalizerPointsFieldExtend (K := K) jT n0).val,
      normalizerPointsFieldExtend_mem_centralizerPoints (K := K) jT hn0c⟩
  have hzc : rationalPoints.map j_K (torusPointExtend (K := K) z) = zc := by
    change rationalPoints.map j_K (rationalExtend k K T.toGrp z) =
      rationalExtend k K G n0.val
    rw [hn0, GaloisPointComparison.rationalExtend_map]
  have := IsSplitTorusCompatible.centralizer_smul_eq_vadd hφ hcompat zc
    (torusPointExtend (K := K) z) hzc w hw
  exact this

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- A rational point of a commutative group scheme centralizes its own image. -/
theorem map_mem_centralizerPoints_self (z : rationalPoints T.toGrp) :
    rationalPoints.map jT z ∈ centralizerPoints jT := by
  rw [← torusCentralizer_carrier_base]
  exact range_le_torusCentralizer jT _ ⟨z, rfl⟩

/-- **Full centralizer compatibility of the descended family.** Let `jT` represent the
centralizer of `i`, let the order `ω` on `Kˣ` be additive, Galois invariant and restrict to
the integer order of `v`, and let `t : S → T` be the largest split subtorus. Then the
torus-then-field restriction of a split-torus compatible upper valuation satisfies full V6
for the actual centralizer `T(k)`, with `s = t`. -/
theorem torusFieldRestricted_isCentralizerCompatible
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [IsAffineHom T.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K) {ω : Kˣ → ℝ}
    (hadd : ∀ x y : Kˣ, ω (x * y) = ω x + ω y)
    (hωσ : ∀ (σ : K ≃ₐ[k] K) (x : Kˣ), ω (Units.map σ.toMonoidHom x) = ω x)
    (hωext : ∀ x : kˣ,
      ω (Units.map (algebraMap k K).toMonoidHom x) = IntegerValuation.order v x)
    {φ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hcompat : IsSplitTorusCompatible (S := T_K) j_K ω φ)
    (hfactor : CommGroupScheme.groupHom t_K ≫ j_K = i_K)
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (hj : (torusCentralizer i).IsRepresentedBy jT)
    (h : Function.Bijective (Cartan.restrictionEvaluation (CommGroupScheme.groupHom t))) :
    IntegerValuation.IsCentralizerCompatible v i jT (CommGroupScheme.groupHom t) h
      (torusFieldRestrictedRootFunctionFamily (T := T_K) (G := G) (j := j_K) hS hT hE hφ t_K) := by
  apply IntegerValuation.isCentralizerCompatible_of_smul_eq_vadd v hj
  intro z
  set n := centralizerToNormalizer i jT hj z with hn
  let n0 : normalizerPoints jT :=
    ⟨rationalPoints.map jT z,
      centralizerPoints_le_normalizerPoints jT (map_mem_centralizerPoints_self jT z)⟩
  obtain ⟨w, hweval, hw⟩ := exists_centralizer_translation_upper jT hT hadd hφ hcompat z n0 rfl
    (map_mem_centralizerPoints_self jT z)
  have hwfix := galoisCocharacterAction_eq_of_eval_eq_neg_order hT hωσ z w hweval
  obtain ⟨v', hv'⟩ := exists_descentCocharacterMap_eq k K t hS ht w hwfix
  set c := (IntegerValuation.centralizerTranslation v (CommGroupScheme.groupHom t) h z).toAdd
    with hc
  have hv'c : v' = c := by
    apply h.1
    refine AddMonoidHom.ext fun χ => ?_
    rw [Cartan.restrictionEvaluation_apply, Cartan.restrictionEvaluation_apply, hc,
      IntegerValuation.eval_centralizerTranslation, ← eval_splitCocharacterBaseChange (K := K) S hS]
    have hres : characterLattice.baseChange b S
        (Cartan.characterRestriction (CommGroupScheme.groupHom t) χ) =
          t_K ≫ characterLattice.baseChange b T (rationalCharacters.equivCharacterLattice T χ) :=
      characterLattice.baseChange_torusCharacterRestrict b (CommGroupScheme.groupHom t) χ
    rw [hres, ← eval_descentCocharacterMap, hv', hweval]
    have hev : rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
        (characterLattice.baseChange b T (rationalCharacters.equivCharacterLattice T χ)))
          (torusPointExtend (K := K) z) =
          Units.map (algebraMap k K).toMonoidHom (rationalCharacterEval χ z) := by
      have hχ : (rationalCharacters.equivCharacterLattice T_K).symm
          (characterLattice.baseChange b T (rationalCharacters.equivCharacterLattice T χ)) =
            rationalCharacters.baseChange b χ := by
        change rationalCharacters.baseChange b ((rationalCharacters.equivCharacterLattice T).symm
          (rationalCharacters.equivCharacterLattice T χ)) = _
        rw [AddEquiv.symm_apply_apply]
      rw [hχ]
      exact rationalCharacterEval_extend k K T.toGrp χ z
    rw [hev, hωext]
  have hnorm := torusFieldRestrictedRootFunctionFamily_normalization (T := T_K) i hS hT hE hφ
    t_K hfactor
  refine (RootFunctionFamily.fieldRestrict_smul_eq_vadd_iff (K := K) i
    (torusRestrictedRootFunctionFamily (T := T_K) (i := j_K) (hS.baseChange b) hT hE hφ t_K)
      hnorm.1 hnorm.2 n c).mpr fun a _ g _ => ?_
  have hsub : w - descentCocharacterMap k K t hS c ∈ rootAnnihilator (S := T_K) j_K := by
    rw [← hv'c, hv', sub_self]
    exact zero_mem _
  rw [normalizerPointsFieldExtend_smul_torusRestricted i t jT hS hT hE hφ hfactor
    n n0 rfl w hw c hsub, RootFunctionFamily.vadd_apply, eval_splitCocharacterBaseChange]

end Shifts

end Langlands.Geometry.Building
