import Langlands.AlgebraicGeometry.PointTopology.HenselianTensorCompletionFieldProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# A valued field is henselian exactly when it is separably closed in its completion

One direction is the published `separableClosure_completion_eq_bot`. Conversely, suppose `K` is
separably algebraically closed in its completion `K̂`.

* Existence: an algebraic extension `L` embeds over `K` in an algebraic closure `Ω` of `K̂`, and
  the absolute value of `Ω` extending the norm of the complete field `K̂` restricts to `L`.
* Uniqueness: for a finite separable `L = K(α)` with minimal polynomial `f`, the image of `f`
  over `K̂` stays irreducible, so `E = K̂[X]/(f)` is a field. An absolute value `w` on `L`
  extending the norm gives a field map from `E` to the completion of `L` at `w`, hence an
  absolute value on `E` extending the norm of `K̂`. Over the complete `K̂` this is unique, so `w`
  is determined. A general algebraic extension reduces to this case: some `p`-power of each
  element is separable over `K`.
-/

noncomputable section

universe u

open Polynomial IntermediateField

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianIffSeparablyClosed

/-- The pullback of an absolute value along a field map. -/
def pullback {R M : Type*} [Field R] [Field M] (u : AbsoluteValue M ℝ) (f : R →+* M) :
    AbsoluteValue R ℝ where
  toFun x := u (f x)
  map_mul' x y := by simp
  nonneg' x := u.nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using u.add_le _ _

@[simp] theorem pullback_apply {R M : Type*} [Field R] [Field M] (u : AbsoluteValue M ℝ)
    (f : R →+* M) (x : R) : pullback u f x = u (f x) := rfl

variable (K : Type u) [NontriviallyNormedField K]

local notation "K̂" => UniformSpace.Completion K

/-- The completion of a nontrivially normed field is nontrivially normed. -/
@[instance_reducible]
def completionNormedField : NontriviallyNormedField K̂ :=
  { (inferInstance : NormedField K̂) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      exact ⟨(x : K̂), by rw [UniformSpace.Completion.norm_coe]; exact hx⟩ }

/-- **Existence.** The norm of `K` extends to every algebraic extension. -/
theorem exists_extension (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ∃ v : AbsoluteValue L ℝ, ∀ x : K, v (algebraMap K L x) = ‖x‖ := by
  let Ω := AlgebraicClosure K̂
  obtain ⟨u, hu, -⟩ :=
    @completeHenselianValuedField K̂ (completionNormedField K) _ Ω _ _ inferInstance
  let τ : L →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨pullback u τ.toRingHom, fun x => ?_⟩
  rw [pullback_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    IsScalarTower.algebraMap_apply K K̂ Ω]
  exact (hu _).trans (UniformSpace.Completion.norm_coe x)

section Uniqueness

variable {K}

/-- **Uniqueness for finite separable extensions.** -/
theorem eq_of_finiteDimensional (hsep : separableClosure K K̂ = ⊥) {L : Type u} [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (v w : AbsoluteValue L ℝ)
    (hv : ∀ x : K, v (algebraMap K L x) = ‖x‖) (hw : ∀ x : K, w (algebraMap K L x) = ‖x‖) :
    v = w := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  have hint : IsIntegral K pb.gen := pb.isIntegral_gen
  have hirr' : Irreducible ((minpoly K pb.gen).map (algebraMap K K̂)) :=
    HenselianTensorCompletion.irreducible_map hsep (minpoly.monic hint) (minpoly.irreducible hint)
      (Algebra.IsSeparable.isSeparable K pb.gen)
  have : Fact (Irreducible ((minpoly K pb.gen).map (algebraMap K K̂))) := ⟨hirr'⟩
  have hroot : aeval (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K K̂)))
      (minpoly K pb.gen) = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K̂, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let φL : L →ₐ[K] AdjoinRoot ((minpoly K pb.gen).map (algebraMap K K̂)) := pb.lift _ hroot
  -- every extension of the norm to `L` comes from one on `K̂[X]/(f)` extending the norm of `K̂`
  have key : ∀ w : AbsoluteValue L ℝ, (∀ x : K, w (algebraMap K L x) = ‖x‖) →
      ∃ a : AbsoluteValue (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K K̂))) ℝ,
        (∀ c : K̂, a (algebraMap K̂ _ c) = ‖c‖) ∧ ∀ x, a (φL x) = w x := by
    intro w hw
    let jL : L →+* w.Completion :=
      UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv w).symm.toRingHom
    let jK : K →+* WithAbs w := (WithAbs.equiv w).symm.toRingHom.comp (algebraMap K L)
    have hjK : Isometry jK := AddMonoidHomClass.isometry_of_norm jK fun x => hw x
    let ι : K̂ →+* w.Completion := UniformSpace.Completion.mapRingHom jK hjK.continuous
    have hι : ∀ c, ‖ι c‖ = ‖c‖ := fun c =>
      (UniformSpace.Completion.isometry_mapRingHom hjK).norm_map_of_map_zero (map_zero _) c
    have hιK : ι.comp (algebraMap K K̂) = jL.comp (algebraMap K L) := by
      ext x
      exact UniformSpace.Completion.mapRingHom_coe hjK.continuous x
    have hfw : ((minpoly K pb.gen).map (algebraMap K K̂)).eval₂ ι (jL pb.gen) = 0 := by
      rw [eval₂_map, hιK, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
    let Ψ := AdjoinRoot.lift ι (jL pb.gen) hfw
    have hΨ : ∀ x, Ψ (φL x) = jL x := by
      let _ : Algebra K w.Completion := (jL.comp (algebraMap K L)).toAlgebra
      let ψ1 : L →ₐ[K] w.Completion :=
        { Ψ.comp φL.toRingHom with
          commutes' := fun a => by
            change Ψ (φL (algebraMap K L a)) = jL (algebraMap K L a)
            rw [AlgHom.commutes, AdjoinRoot.algebraMap_eq', RingHom.comp_apply,
              AdjoinRoot.lift_of, ← RingHom.comp_apply ι, hιK, RingHom.comp_apply] }
      let ψ2 : L →ₐ[K] w.Completion := { jL with commutes' := fun _ => rfl }
      have h12 : ψ1 = ψ2 := pb.algHom_ext (by
        change Ψ (φL pb.gen) = jL pb.gen
        rw [PowerBasis.lift_gen, AdjoinRoot.lift_root])
      intro x
      exact congrArg (fun ψ : L →ₐ[K] w.Completion => ψ x) h12
    refine ⟨pullback (NormedField.toAbsoluteValue w.Completion) Ψ, fun c => ?_, fun x => ?_⟩
    · change ‖Ψ (AdjoinRoot.of _ c)‖ = ‖c‖
      rw [AdjoinRoot.lift_of]
      exact hι c
    · change ‖Ψ (φL x)‖ = w x
      rw [hΨ]
      exact UniformSpace.Completion.norm_coe _
  obtain ⟨a, ha, hav⟩ := key v hv
  obtain ⟨b, hb, hbw⟩ := key w hw
  have : Module.Finite K̂ (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K K̂))) :=
    (AdjoinRoot.powerBasis hirr'.ne_zero).finite
  have : Algebra.IsAlgebraic K̂ (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K K̂))) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hab : a = b := by
    let := completionNormedField K
    exact CompleteHenselian.absoluteValue_eq a b ha hb
  ext x
  rw [← hav, ← hbw, hab]

/-- **Uniqueness for algebraic extensions.** -/
theorem eq_of_isAlgebraic (hsep : separableClosure K K̂ = ⊥) {L : Type u} [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v w : AbsoluteValue L ℝ)
    (hv : ∀ x : K, v (algebraMap K L x) = ‖x‖) (hw : ∀ x : K, w (algebraMap K L x) = ‖x‖) :
    v = w := by
  have hs : ∀ y : L, IsSeparable K y → v y = w y := by
    intro y hy
    have : FiniteDimensional K K⟮y⟯ := IntermediateField.adjoin.finiteDimensional hy.isIntegral
    have : Algebra.IsSeparable K K⟮y⟯ :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).2 hy
    have h := eq_of_finiteDimensional hsep (pullback v (algebraMap K⟮y⟯ L))
      (pullback w (algebraMap K⟮y⟯ L))
      (fun x => by rw [pullback_apply, ← IsScalarTower.algebraMap_apply]; exact hv x)
      (fun x => by rw [pullback_apply, ← IsScalarTower.algebraMap_apply]; exact hw x)
    exact congrArg (fun a : AbsoluteValue K⟮y⟯ ℝ =>
      a ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩) h
  ext x
  obtain ⟨n, s, hsx⟩ := IsPurelyInseparable.pow_mem (separableClosure K L)
    (ringExpChar (separableClosure K L)) x
  have hy : IsSeparable K (x ^ ringExpChar (separableClosure K L) ^ n) := by
    rw [← hsx]
    exact mem_separableClosure_iff.mp s.2
  have h := hs _ hy
  rw [map_pow, map_pow] at h
  exact (pow_left_inj₀ (v.nonneg x) (w.nonneg x)
    (pow_ne_zero _ (expChar_ne_zero (separableClosure K L) _))).mp h

end Uniqueness

variable {K} in
/-- **A field separably closed in its completion is henselian.** -/
theorem isHenselianValuedField_of_separableClosure_eq_bot
    (hsep : separableClosure K K̂ = ⊥) : IsHenselianValuedField K := by
  intro L _ _ _
  obtain ⟨v, hv⟩ := exists_extension K L
  exact ⟨v, hv, fun w hw => eq_of_isAlgebraic hsep w v hw hv⟩

end HenselianIffSeparablyClosed

/-- **A valued field is henselian exactly when it is separably algebraically closed in its
completion** (Conrad, printed p.14). -/
theorem henselianIffSeparablyClosed : HenselianIffSeparablyClosedStatement.{u} := fun K _ =>
  ⟨separableClosure_completion_eq_bot K,
    HenselianIffSeparablyClosed.isHenselianValuedField_of_separableClosure_eq_bot⟩

end Langlands.AlgebraicGeometry.PointTopology
