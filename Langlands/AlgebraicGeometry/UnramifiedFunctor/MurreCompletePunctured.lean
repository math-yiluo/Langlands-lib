import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteMono
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleCover
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Completeness of finite algebras and pro-representability on complete local rings

For Step 2a of Murre's induction (Bourbaki exp. 294): finite algebras over a complete local
noetherian ring are complete, and `ξ_y ∈ F(Spec B_y)` is pro-representable on complete local
noetherian `R`-algebras. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Finite

/-- A finite module over a noetherian ring complete for an ideal `I` is `I`-adically complete. -/
lemma isAdicComplete_of_finite {A M : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e : A ≃ₗ[A] AdicCompletion I A := AdicCompletion.ofLinearEquiv I A
  let φ : M ≃ₗ[A] AdicCompletion I A ⊗[A] M :=
    (TensorProduct.lid A M).symm ≪≫ₗ LinearEquiv.rTensor M e
  have h : (AdicCompletion.of I M : M → AdicCompletion I M) =
      (AdicCompletion.ofTensorProduct I M) ∘ φ := by
    funext x
    simp only [Function.comp_apply, φ, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul]
    rw [AdicCompletion.ofTensorProduct_tmul]
    have : e 1 = 1 := by
      change AdicCompletion.of I A 1 = 1
      rw [← map_one (algebraMap A A), ← AdicCompletion.algebraMap_apply, map_one]
    rw [this, one_smul]
  rw [h]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp
    φ.bijective

/-- A finite algebra over a noetherian ring complete for `I` is complete for the image of
`I`. -/
lemma isAdicComplete_map_of_finite {A S : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] [CommRing S] [Algebra A S] [Module.Finite A S] :
    IsAdicComplete (I.map (algebraMap A S)) S := by
  have hc := isAdicComplete_of_finite (M := S) I
  have key : ∀ (n : ℕ) (x : S), x ∈ (I ^ n • ⊤ : Submodule A S) ↔
      x ∈ ((I.map (algebraMap A S)) ^ n • ⊤ : Submodule S S) := by
    intro n x
    rw [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
    rfl
  have hH : IsHausdorff (I.map (algebraMap A S)) S := ⟨fun x hx ↦ hc.haus' x fun n ↦ by
    have := hx n
    rw [SModEq.sub_mem] at this ⊢
    exact (key n _).2 this⟩
  have hP : IsPrecomplete (I.map (algebraMap A S)) S := ⟨fun f hf ↦ by
    obtain ⟨L, hL⟩ := hc.prec' f fun {m n} hmn ↦ by
      have := hf hmn
      rw [SModEq.sub_mem] at this ⊢
      exact (key m _).2 this
    exact ⟨L, fun n ↦ by
      have := hL n
      rw [SModEq.sub_mem] at this ⊢
      exact (key n _).1 this⟩⟩
  exact {}

end Finite

section Complete

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {Y : ℕ → Scheme.{u}} {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
  (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))
  [hfu : ∀ k, FormallyUnramified (q k)] [hlft : ∀ k, LocallyOfFiniteType (q k)]
  (hF3 : AdicLimits F) (y : Y 0)

omit [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
/-- The `R`-algebra map `κ(A) → κ(A/I)` for a proper ideal `I` of a local ring `A`. -/
def residueQuotₐ {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A] (I : Ideal A)
    (hI : I ≤ maximalIdeal A) [IsLocalRing (A ⧸ I)] :
    ResidueField A →ₐ[R] ResidueField (A ⧸ I) :=
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot _ (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hI)
  { ResidueField.map (Ideal.Quotient.mk I) with
    commutes' := fun r ↦ by
      change ResidueField.map (Ideal.Quotient.mk I) (residue A (algebraMap R A r)) = _
      rw [ResidueField.map_residue]
      rfl }

omit [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
lemma residueQuotₐ_comp {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A] (I : Ideal A)
    (hI : I ≤ maximalIdeal A) [IsLocalRing (A ⧸ I)] :
    (residueQuotₐ I hI).comp (IsScalarTower.toAlgHom R A (ResidueField A)) =
      (IsScalarTower.toAlgHom R (A ⧸ I) (ResidueField (A ⧸ I))).comp
        (Ideal.Quotient.mkₐ R I) := by
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot _ (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hI)
  ext a
  change ResidueField.map (Ideal.Quotient.mk I) (residue A a) = residue _ (Ideal.Quotient.mk I a)
  rw [ResidueField.map_residue]

include hfu hlft in
/-- Pro-representability on complete local rings: an element of `F` over a complete local
noetherian `R`-algebra, whose restriction to the residue field comes from `ξ_y`, comes from
`ξ_y`. -/
lemma chart_lift_complete {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    (η : F.obj (op (ovR R A))) (σ : ChartRing e y →ₐ[R] ResidueField A)
    (hσ : F.map (homR σ).op (chartElem e hF3 y) =
      F.map (homR (IsScalarTower.toAlgHom R A (ResidueField A))).op η) :
    ∃ ψ : ChartRing e y →ₐ[R] A, F.map (homR ψ).op (chartElem e hF3 y) = η := by
  have hloc : ∀ r ∈ maximalIdeal R, algebraMap R A r ∈ maximalIdeal A := fun r hr ↦
    (mem_maximalIdeal _).2 fun h ↦ (mem_maximalIdeal r).1 hr (isUnit_of_map_unit _ r h)
  have hle : ∀ n : ℕ, maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := fun n ↦
    Ideal.pow_le_self (Nat.succ_ne_zero n)
  have : ∀ n : ℕ, IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) := fun n ↦
    have : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (hle n))
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hA : ∀ n : ℕ, ∀ r ∈ maximalIdeal R ^ (n + 1),
      algebraMap R (A ⧸ maximalIdeal A ^ (n + 1)) r = 0 := by
    intro n r hr
    rw [IsScalarTower.algebraMap_apply R A, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    have hmap : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A :=
      Ideal.map_le_iff_le_comap.2 (fun r hr ↦ Ideal.mem_comap.2 (hloc r hr))
    have := Ideal.mem_map_of_mem (algebraMap R A) hr
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmap _ this
  let ηn : ∀ n : ℕ, F.obj (op (ovR R (A ⧸ maximalIdeal A ^ (n + 1)))) := fun n ↦
    F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (n + 1)))).op η
  have hσn : ∀ n : ℕ, F.map (homR ((residueQuotₐ _ (hle n)).comp σ)).op (chartElem e hF3 y) =
      F.map (homR (IsScalarTower.toAlgHom R _ (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))))).op
        (ηn n) := by
    intro n
    rw [← map_homR_map_homR, hσ, map_homR_map_homR, residueQuotₐ_comp, ← map_homR_map_homR]
  choose ψn hψn using fun n ↦ chart_lift e hF3 y n (hA n) (ηn n) _ (hσn n)
  have hcomp : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal A)
        (Nat.succ_le_succ hmn))).comp (ψn n) = ψn m := by
    intro m n hmn
    apply chart_inj_level e hF3 y m (hA m)
    rw [← map_homR_map_homR, hψn, hψn]
    change F.map _ (F.map _ η) = F.map _ η
    rw [map_homR_map_homR, Ideal.Quotient.factorₐ_comp_mk]
  let f : ∀ n : ℕ, ChartRing e y →ₐ[R] A ⧸ maximalIdeal A ^ n := fun n ↦
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal A) n.le_succ)).comp
      (ψn n)
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal A) hmn)).comp (f n) =
        f m := by
    intro m n hmn
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← hcomp hmn, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  refine ⟨IsAdicComplete.liftAlgHom (maximalIdeal A) f hf, adic_unique A hF3 fun n ↦ ?_⟩
  rw [map_homR_map_homR, IsAdicComplete.mkₐ_comp_liftAlgHom]
  simp only [f]
  rw [← map_homR_map_homR, hψn]
  change F.map _ (F.map _ η) = _
  rw [map_homR_map_homR, Ideal.Quotient.factorₐ_comp_mk]

end Complete

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
