import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientAutomorphismStatement

/-! Pullback of actual compact induction along a subgroup-preserving automorphism. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  (H : Subgroup G) (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

/-- Pull the inducing action back through the actual restriction of `α`. -/
def automorphismInducing (σ : Representation R H V) : Representation R H V :=
  σ.comp (QuotientIntegration.subgroupAutomorphism H α hα).toMonoidHom

/-- The existing smooth transport, specialized to the canonical subgroup restriction. -/
def automorphismSmoothEquiv (σ : Representation R H V) :
    Representation.Equiv ((smoothInduced H σ).comp α.toMonoidHom)
      (smoothInduced H (automorphismInducing H α hα σ)) :=
  precomposeSmoothInducedEquiv α
    (QuotientIntegration.subgroupAutomorphism H α hα).toMulEquiv
    (fun _ => rfl) (fun _ => rfl)

/-- The projected nonzero support pulls back by the actual quotient homeomorphism. -/
theorem quotientSupport_automorphismSmoothEquiv (σ : Representation R H V)
    (f : SmoothFunctions H σ) :
    quotientSupport H
        (eval H (automorphismInducing H α hα σ) (automorphismSmoothEquiv H α hα σ f)) =
      QuotientIntegration.quotientAutomorphism H α hα ⁻¹' quotientSupport H (eval H σ f) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x =>
    change x ∈ quotientMap H ⁻¹' quotientSupport H _ ↔
      α x ∈ quotientMap H ⁻¹' quotientSupport H _
    rw [quotientMap_preimage_quotientSupport, quotientMap_preimage_quotientSupport]
    rfl

/-- Compactness of the actual quotient support is preserved in both directions. -/
theorem compactSupport_automorphismSmoothEquiv_iff (σ : Representation R H V)
    (f : SmoothFunctions H σ) :
    IsCompact (quotientSupport H
      (eval H (automorphismInducing H α hα σ) (automorphismSmoothEquiv H α hα σ f))) ↔
      IsCompact (quotientSupport H (eval H σ f)) := by
  rw [quotientSupport_automorphismSmoothEquiv]
  exact (QuotientIntegration.quotientAutomorphism H α hα).isCompact_preimage

/-- Precomposition by `α` on actual compact functions, with pulled-back ambient action. -/
def precomposeCompactInducedEquiv (σ : Representation R H V) :
    Representation.Equiv ((compactInduced H σ).comp α.toMonoidHom)
      (compactInduced H (automorphismInducing H α hα σ)) where
  toFun f := ⟨automorphismSmoothEquiv H α hα σ f.val,
    (compactSupport_automorphismSmoothEquiv_iff H α hα σ f.val).mpr f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(automorphismSmoothEquiv H α hα σ).symm f.val, by
    apply (compactSupport_automorphismSmoothEquiv_iff H α hα σ _).mp
    have hf : IsCompact (quotientSupport H
        (eval H (automorphismInducing H α hα σ) f.val)) := f.property
    simpa only [Representation.Equiv.apply_symm_apply] using hf⟩
  left_inv f := by
    apply Subtype.ext
    exact (automorphismSmoothEquiv H α hα σ).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (automorphismSmoothEquiv H α hα σ).apply_symm_apply f.val
  isIntertwining' g := by
    ext f x
    change eval H σ f.val (α x * α g) = eval H σ f.val (α (x * g))
    rw [map_mul]

@[simp]
theorem precomposeCompactInducedEquiv_eval (σ : Representation R H V)
    (f : CompactFunctions H σ) (x : G) :
    eval H (automorphismInducing H α hα σ)
      (precomposeCompactInducedEquiv H α hα σ f).val x = eval H σ f.val (α x) := rfl

@[simp]
theorem precomposeCompactInducedEquiv_symm_eval (σ : Representation R H V)
    (f : CompactFunctions H (automorphismInducing H α hα σ)) (x : G) :
    eval H σ ((precomposeCompactInducedEquiv H α hα σ).symm f).val x =
      eval H (automorphismInducing H α hα σ) f.val (α.symm x) := rfl

/-- The same coefficient map intertwines the two pulled-back inducing actions. -/
def automorphismInducingMap {σ : Representation R H V} {τ : Representation R H W}
    (T : σ.IntertwiningMap τ) :
    (automorphismInducing H α hα σ).IntertwiningMap (automorphismInducing H α hα τ) where
  toLinearMap := T.toLinearMap
  isIntertwining' h := T.isIntertwining' (QuotientIntegration.subgroupAutomorphism H α hα h)

/-- Precomposition commutes with every coefficient intertwiner. -/
theorem precomposeCompactInducedEquiv_natural
    {σ : Representation R H V} {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) :
    precomposeCompactInducedEquiv H α hα τ (compactInducedMap H T f) =
      compactInducedMap H (automorphismInducingMap H α hα T)
        (precomposeCompactInducedEquiv H α hα σ f) := by
  ext x
  rfl

end Langlands.Induction
