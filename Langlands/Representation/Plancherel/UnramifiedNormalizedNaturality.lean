import Langlands.Representation.Plancherel.UnramifiedNormalizedSpecialization

/-! Coefficient naturality of the actual normalized specialization maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped NNReal TensorProduct

namespace Langlands.Plancherel.UnramifiedNormalized

universe uI uG uV uW uX

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S] {e : R →+* S}
  {G : Type uG} [Group G]
  {V V' W W' : Type*}
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
  [AddCommGroup W] [Module S W] [AddCommGroup W'] [Module S W']
  (ρ : Representation R G V) (ρ' : Representation R G V')
  (τ : Representation S G W) (τ' : Representation S G W') (U : Subgroup G)
  (T : V →ₛₗ[e] W) (T' : V' →ₛₗ[e] W')
  (hT : ∀ g v, T (ρ g v) = τ g (T v))
  (hT' : ∀ g v, T' (ρ' g v) = τ' g (T' v))

/-- A commuting coefficient square descends through the actual relation quotients. -/
theorem quotientEvaluation_natural (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (hn : ∀ v, T' (f v) = g (T v))
    (q : Langlands.Jacquet.Localization.Coinvariants ρ U 1) :
    quotientEvaluation ρ' τ' U T' hT'
        (Langlands.Jacquet.Localization.mapLinear U 1 f q) =
      Langlands.Jacquet.Localization.mapLinear U 1 g
        (quotientEvaluation ρ τ U T hT q) := by
  obtain ⟨v, rfl⟩ := Langlands.Jacquet.Localization.mk_surjective ρ U 1 q
  change Langlands.Jacquet.Localization.mk τ' U 1 (T' (f v)) =
    Langlands.Jacquet.Localization.mk τ' U 1 (g (T v))
  rw [hn]

end Quotient

section Parabolic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (h : Aubert.General.IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

local instance naturalityTensorAddCommGroup (Y : Type*) [AddCommGroup Y] [Module ℂ Y] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] Y) :=
  TensorProduct.addCommGroup

/-- The existing pointwise complex induced map after the common character twists. -/
def complexInducedMap {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν) :
    (complexInducedRepresentation ν h hU σ χ).IntertwiningMap
      (complexInducedRepresentation ν h hU τ χ) :=
  Induction.smoothInducedMap P
    (Langlands.twistIntertwining (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
      { toLinearMap := (Langlands.twistIntertwining χ.val.toMonoidHom T).toLinearMap
        isIntertwining' p :=
          (Langlands.twistIntertwining χ.val.toMonoidHom T).isIntertwining' (h.projection p) })

@[simp] theorem complexInducedMap_eval {σ : Representation ℂ M V}
    {τ : Representation ℂ M W} (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν)
    (f : ComplexInduced ν h hU σ χ) (x : G) :
    Induction.eval P (complexInducingRepresentation ν h hU τ χ)
        (complexInducedMap ν h hU T χ f) x =
      T (Induction.eval P (complexInducingRepresentation ν h hU σ χ) f x) := rfl

@[simp] theorem complexInducedMap_id (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) :
    complexInducedMap ν h hU (Representation.IntertwiningMap.id σ) χ =
      Representation.IntertwiningMap.id (complexInducedRepresentation ν h hU σ χ) := by
  ext f x
  rfl

@[simp] theorem complexInducedMap_comp {σ : Representation ℂ M V}
    {τ : Representation ℂ M W} {υ : Representation ℂ M X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) (χ : unramifiedCharacters ν) :
    complexInducedMap ν h hU (S.comp T) χ =
      (complexInducedMap ν h hU S χ).comp (complexInducedMap ν h hU T χ) := by
  ext f x
  rfl

/-- The existing complex relation-quotient map with the inverse Levi twist. -/
def complexJacquetMap {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν) :
    (complexJacquetRepresentation ν h hU σ χ).IntertwiningMap
      (complexJacquetRepresentation ν h hU τ χ) :=
  Langlands.twistIntertwining (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
    (Langlands.Jacquet.Localization.map U 1 M h.levi_le_normalizer
      (Langlands.Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer)
      (complexInducedMap ν h hU T χ))

@[simp] theorem complexJacquetMap_mk {σ : Representation ℂ M V}
    {τ : Representation ℂ M W} (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν)
    (f : ComplexInduced ν h hU σ χ) :
    complexJacquetMap ν h hU T χ
        (Langlands.Jacquet.Localization.mk (complexInducedRepresentation ν h hU σ χ) U 1 f) =
      Langlands.Jacquet.Localization.mk (complexInducedRepresentation ν h hU τ χ) U 1
        (complexInducedMap ν h hU T χ f) := rfl

@[simp] theorem complexJacquetMap_id (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) :
    complexJacquetMap ν h hU (Representation.IntertwiningMap.id σ) χ =
      Representation.IntertwiningMap.id (complexJacquetRepresentation ν h hU σ χ) := by
  apply Representation.IntertwiningMap.ext
  apply Langlands.Jacquet.Localization.hom_ext
  ext f
  change Langlands.Jacquet.Localization.mk _ U 1
      (complexInducedMap ν h hU (Representation.IntertwiningMap.id σ) χ f) = _
  rw [complexInducedMap_id]
  rfl

@[simp] theorem complexJacquetMap_comp {σ : Representation ℂ M V}
    {τ : Representation ℂ M W} {υ : Representation ℂ M X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ) (χ : unramifiedCharacters ν) :
    complexJacquetMap ν h hU (S.comp T) χ =
      (complexJacquetMap ν h hU S χ).comp (complexJacquetMap ν h hU T χ) := by
  apply Representation.IntertwiningMap.ext
  apply Langlands.Jacquet.Localization.hom_ext
  ext f
  change Langlands.Jacquet.Localization.mk _ U 1
      (complexInducedMap ν h hU (S.comp T) χ f) = _
  rw [complexInducedMap_comp]
  rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Tensor evaluation commutes with every scalar-extended coefficient intertwiner. -/
theorem tensorEvaluation_natural {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) :
    tensorEvaluation ν W χ (tensorMap ν T t) = T (tensorEvaluation ν V χ t) :=
  tensorEvaluation_map ν T t χ

/-- Pointwise specialization commutes with actual normalized induced maps. -/
theorem inducedEvaluation_natural {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν)
    (f : UniversalInduced ν h hU σ) :
    inducedEvaluation ν h hU τ χ (universalInducedMap ν h hU T f) =
      complexInducedMap ν h hU T χ (inducedEvaluation ν h hU σ χ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact tensorEvaluation_map ν T
    (Induction.eval P (universalInducingRepresentation ν h hU σ) f x) χ

/-- Descended specialization commutes with actual normalized Jacquet maps. -/
theorem jacquetEvaluation_natural {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    (T : σ.IntertwiningMap τ) (χ : unramifiedCharacters ν)
    (q : UniversalJacquet ν h hU σ) :
    jacquetEvaluation ν h hU τ χ (universalJacquetMap ν h hU T q) =
      complexJacquetMap ν h hU T χ (jacquetEvaluation ν h hU σ χ q) :=
  quotientEvaluation_natural (universalInducedRepresentation ν h hU σ)
    (universalInducedRepresentation ν h hU τ)
    (complexInducedRepresentation ν h hU σ χ) (complexInducedRepresentation ν h hU τ χ) U
    (inducedEvaluation ν h hU σ χ) (inducedEvaluation ν h hU τ χ)
    (inducedEvaluation_action ν h hU σ χ) (inducedEvaluation_action ν h hU τ χ)
    (universalInducedMap ν h hU T) (complexInducedMap ν h hU T χ)
    (inducedEvaluation_natural ν h hU T χ) q

set_option backward.isDefEq.respectTransparency.types true in
/-- The complex induced map is the map of the existing normalized functor. -/
theorem complexInducedMap_heq_functor
    {A D : SmoothRep.{0, uG, uV} ℂ M} (T : A ⟶ D) (χ : unramifiedCharacters ν) :
    HEq (complexInducedMap ν h hU (SmoothRep.hom T) χ)
      (SmoothRep.hom ((Aubert.General.normalizedInductionFunctor h hU).map
        ((SmoothRep.twistFunctor χ.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker ν χ)).map T))) := by
  rfl

end Parabolic

end Langlands.Plancherel.UnramifiedNormalized
