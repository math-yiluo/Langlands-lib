import Langlands.Representation.Plancherel.UnramifiedNormalizedModels

/-! Coefficient maps and the actual universal normalized models. -/

noncomputable section

open scoped NNReal TensorProduct

namespace Langlands.Plancherel.UnramifiedNormalized

universe uL uI uG uV uW uX

section Tensor

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

local instance tensorAddCommGroup (Y : Type*) [AddCommGroup Y] [Module ℂ Y] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] Y) :=
  TensorProduct.addCommGroup

/-- Scalar extension of a complex intertwiner, with the actual universal action. -/
def tensorMap {σ : Representation ℂ L V} {τ : Representation ℂ L W}
    (T : σ.IntertwiningMap τ) :
    (universalUnramifiedRepresentation ν σ).IntertwiningMap
      (universalUnramifiedRepresentation ν τ) where
  toLinearMap := T.toLinearMap.baseChange _
  isIntertwining' g := by
    ext v
    change (unramifiedEvaluationRegular ν g * 1) ⊗ₜ[ℂ] T (σ g v) =
      (unramifiedEvaluationRegular ν g * 1) ⊗ₜ[ℂ] τ g (T v)
    rw [Representation.IntertwiningMap.isIntertwining σ τ T]

@[simp] theorem tensorMap_tmul {σ : Representation ℂ L V} {τ : Representation ℂ L W}
    (T : σ.IntertwiningMap τ) (b : unramifiedRegularFunctions ν) (v : V) :
    tensorMap ν T (b ⊗ₜ[ℂ] v) = b ⊗ₜ[ℂ] T v := rfl

@[simp] theorem tensorMap_id (σ : Representation ℂ L V) :
    tensorMap ν (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (universalUnramifiedRepresentation ν σ) := by
  ext v
  rfl

@[simp] theorem tensorMap_comp {σ : Representation ℂ L V} {τ : Representation ℂ L W}
    {υ : Representation ℂ L X} (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) :
    tensorMap ν (S.comp T) = (tensorMap ν S).comp (tensorMap ν T) := by
  ext v
  rfl

theorem tensorEvaluation_map {σ : Representation ℂ L V} {τ : Representation ℂ L W}
    (T : σ.IntertwiningMap τ) (t : unramifiedRegularFunctions ν ⊗[ℂ] V)
    (χ : unramifiedCharacters ν) :
    unramifiedTensorEvaluation ν W (tensorMap ν T t) χ =
      T (unramifiedTensorEvaluation ν V t χ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => exact (T.toLinearMap.map_smul (b.val χ) v).symm
  | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs]

end Tensor

section Maps

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : Aubert.General.IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {V : Type uV} [AddCommGroup V] [Module (unramifiedRegularFunctions ν) V]
  {W : Type uW} [AddCommGroup W] [Module (unramifiedRegularFunctions ν) W]
  {X : Type uX} [AddCommGroup X] [Module (unramifiedRegularFunctions ν) X]

/-- Postcomposition on full normalized induction by a B-linear Levi intertwiner. -/
def inducedMap {σ : Representation (unramifiedRegularFunctions ν) M V}
    {τ : Representation (unramifiedRegularFunctions ν) M W} (T : σ.IntertwiningMap τ) :
    (inducedRepresentation ν h hU σ).IntertwiningMap
      (inducedRepresentation ν h hU τ) :=
  Induction.smoothInducedMap P
    (Langlands.twistIntertwining (inductionCharacter ν U P hU h.le_normalizer).toMonoidHom
      { toLinearMap := T.toLinearMap
        isIntertwining' p := T.isIntertwining' (h.projection p) })

@[simp] theorem inducedMap_eval {σ : Representation (unramifiedRegularFunctions ν) M V}
    {τ : Representation (unramifiedRegularFunctions ν) M W} (T : σ.IntertwiningMap τ)
    (f : Induced ν h hU σ) (x : G) :
    Induction.eval P (inducingRepresentation ν h hU τ) (inducedMap ν h hU T f) x =
      T (Induction.eval P (inducingRepresentation ν h hU σ) f x) := rfl

@[simp] theorem inducedMap_id (σ : Representation (unramifiedRegularFunctions ν) M V) :
    inducedMap ν h hU (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (inducedRepresentation ν h hU σ) := by
  ext f x
  rfl

@[simp] theorem inducedMap_comp {σ : Representation (unramifiedRegularFunctions ν) M V}
    {τ : Representation (unramifiedRegularFunctions ν) M W}
    {υ : Representation (unramifiedRegularFunctions ν) M X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) :
    inducedMap ν h hU (S.comp T) =
      (inducedMap ν h hU S).comp (inducedMap ν h hU T) := by
  ext f x
  rfl

/-- Passage to the actual relation quotient, followed by the inverse-half twist. -/
def jacquetMap {ρ : Representation (unramifiedRegularFunctions ν) G V}
    {τ : Representation (unramifiedRegularFunctions ν) G W} (T : ρ.IntertwiningMap τ) :
    (jacquetRepresentation ν ρ U M hU h.levi_le_normalizer).IntertwiningMap
      (jacquetRepresentation ν τ U M hU h.levi_le_normalizer) :=
  Langlands.twistIntertwining
    (jacquetCharacter ν U M hU h.levi_le_normalizer).toMonoidHom
    (Langlands.Jacquet.Localization.map U 1 M h.levi_le_normalizer
      (Langlands.Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer) T)

@[simp] theorem jacquetMap_mk {ρ : Representation (unramifiedRegularFunctions ν) G V}
    {τ : Representation (unramifiedRegularFunctions ν) G W} (T : ρ.IntertwiningMap τ)
    (v : V) :
    jacquetMap ν h hU T (Langlands.Jacquet.Localization.mk ρ U 1 v) =
      Langlands.Jacquet.Localization.mk τ U 1 (T v) := rfl

@[simp] theorem jacquetMap_id (ρ : Representation (unramifiedRegularFunctions ν) G V) :
    jacquetMap ν h hU (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id
        (jacquetRepresentation ν ρ U M hU h.levi_le_normalizer) := by
  apply Representation.IntertwiningMap.ext
  exact Langlands.Jacquet.Localization.hom_ext rfl

@[simp] theorem jacquetMap_comp {ρ : Representation (unramifiedRegularFunctions ν) G V}
    {τ : Representation (unramifiedRegularFunctions ν) G W}
    {υ : Representation (unramifiedRegularFunctions ν) G X}
    (T : ρ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) :
    jacquetMap ν h hU (S.comp T) =
      (jacquetMap ν h hU S).comp (jacquetMap ν h hU T) := by
  apply Representation.IntertwiningMap.ext
  exact Langlands.Jacquet.Localization.hom_ext rfl

end Maps

section Universal

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (h : Aubert.General.IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance universalTensorAddCommGroup (Y : Type*) [AddCommGroup Y] [Module ℂ Y] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] Y) :=
  TensorProduct.addCommGroup

/-- The universal inducing tensor, inflated and positively normalized on full P. -/
abbrev universalInducingRepresentation (σ : Representation ℂ M V) :=
  inducingRepresentation ν h hU (universalUnramifiedRepresentation ν σ)

/-- The actual full smooth induced carrier of the universal tensor action. -/
abbrev UniversalInduced (σ : Representation ℂ M V) :=
  Induced ν h hU (universalUnramifiedRepresentation ν σ)

/-- Right translation on the actual universal normalized induced model. -/
abbrev universalInducedRepresentation (σ : Representation ℂ M V) :=
  inducedRepresentation ν h hU (universalUnramifiedRepresentation ν σ)

/-- Its actual U-relation quotient. -/
abbrev UniversalJacquet (σ : Representation ℂ M V) :=
  Jacquet ν (universalInducedRepresentation ν h hU σ) U

/-- The inverse-half normalized Levi action on that quotient. -/
abbrev universalJacquetRepresentation (σ : Representation ℂ M V) :=
  jacquetRepresentation ν (universalInducedRepresentation ν h hU σ)
    U M hU h.levi_le_normalizer

theorem isSmooth_universalInducedRepresentation (σ : Representation ℂ M V) :
    IsSmooth (universalInducedRepresentation ν h hU σ) :=
  isSmooth_inducedRepresentation ν h hU _

theorem isSmooth_universalJacquetRepresentation (σ : Representation ℂ M V) :
    IsSmooth (universalJacquetRepresentation ν h hU σ) :=
  isSmooth_jacquetRepresentation ν h hU _ (isSmooth_universalInducedRepresentation ν h hU σ)

/-- A complex coefficient intertwiner gives a B-linear map of the full induced models. -/
abbrev universalInducedMap {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) :=
  inducedMap ν h hU (tensorMap ν T)

/-- The corresponding B-linear map of the actual normalized Jacquet quotients. -/
abbrev universalJacquetMap {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) :
    (universalJacquetRepresentation ν h hU σ).IntertwiningMap
      (universalJacquetRepresentation ν h hU τ) :=
  jacquetMap ν h hU
    (universalInducedMap ν h hU (σ := σ) (τ := τ) T)

end Universal

end Langlands.Plancherel.UnramifiedNormalized
