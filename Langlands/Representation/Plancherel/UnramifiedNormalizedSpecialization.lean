import Langlands.Representation.Plancherel.UnramifiedNormalizedTensorModels

/-! Actual semilinear specialization of the full normalized models. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped NNReal TensorProduct

namespace Langlands.Plancherel.UnramifiedNormalized

universe uL uI uG uV uW

private theorem dependentCongr {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

section Tensor

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  (V : Type uV) [AddCommGroup V] [Module ℂ V]

local instance tensorEvaluationAddCommGroup :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

/-- The published tensor evaluation, bundled along actual scalar evaluation. -/
def tensorEvaluation (χ : unramifiedCharacters ν) :
    unramifiedRegularFunctions ν ⊗[ℂ] V →ₛₗ[evaluation ν χ] V where
  toFun t := unramifiedTensorEvaluation ν V t χ
  map_add' t s := congrFun ((unramifiedTensorEvaluation ν V).map_add t s) χ
  map_smul' b t := unramifiedTensorEvaluation_regular_smul ν V b t χ

@[simp] theorem tensorEvaluation_apply (χ : unramifiedCharacters ν)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) :
    tensorEvaluation ν V χ t = unramifiedTensorEvaluation ν V t χ := rfl

@[simp] theorem tensorEvaluation_tmul (χ : unramifiedCharacters ν)
    (b : unramifiedRegularFunctions ν) (v : V) :
    tensorEvaluation ν V χ (b ⊗ₜ[ℂ] v) = b.val χ • v := rfl

theorem tensorEvaluation_action (σ : Representation ℂ L V)
    (χ : unramifiedCharacters ν) (m : L)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) :
    tensorEvaluation ν V χ (universalUnramifiedRepresentation ν σ m t) =
      Langlands.twist χ.val.toMonoidHom σ m (tensorEvaluation ν V χ t) :=
  unramifiedTensorEvaluation_action ν σ m t χ

end Tensor

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S] {e : R →+* S}
  {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module S W]
  (ρ : Representation R G V) (τ : Representation S G W) (U : Subgroup G)
  (T : V →ₛₗ[e] W) (hT : ∀ g v, T (ρ g v) = τ g (T v))

include hT in
/-- Semilinear equivariant maps preserve the actual character-one relation spans. -/
theorem relations_le_comap :
    Langlands.Jacquet.Localization.relations ρ U 1 ≤
      (Langlands.Jacquet.Localization.relations τ U 1).comap T := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  change T (ρ u v - ((1 : U →* Rˣ) u : R) • v) ∈
    Langlands.Jacquet.Localization.relations τ U 1
  simpa only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hT] using
    Langlands.Jacquet.Localization.sub_mem_relations τ U 1 u (T v)

/-- Descend a semilinear equivariant map through the actual relation quotient. -/
def quotientEvaluation :
    Langlands.Jacquet.Localization.Coinvariants ρ U 1 →ₛₗ[e]
      Langlands.Jacquet.Localization.Coinvariants τ U 1 :=
  (Langlands.Jacquet.Localization.relations ρ U 1).mapQ
    (Langlands.Jacquet.Localization.relations τ U 1) T
    (relations_le_comap ρ τ U T hT)

@[simp] theorem quotientEvaluation_mk (v : V) :
    quotientEvaluation ρ τ U T hT (Langlands.Jacquet.Localization.mk ρ U 1 v) =
      Langlands.Jacquet.Localization.mk τ U 1 (T v) := rfl

/-- Descended evaluation commutes with the actual normalizer action. -/
theorem quotientEvaluation_action (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M)
    (q : Langlands.Jacquet.Localization.Coinvariants ρ U 1) :
    quotientEvaluation ρ τ U T hT
        (Langlands.Jacquet.Localization.action ρ U 1 M hMU
          (Langlands.Jacquet.Localization.isInvariant_one U M hMU) m q) =
      Langlands.Jacquet.Localization.action τ U 1 M hMU
        (Langlands.Jacquet.Localization.isInvariant_one U M hMU) m
        (quotientEvaluation ρ τ U T hT q) := by
  obtain ⟨v, rfl⟩ := Langlands.Jacquet.Localization.mk_surjective ρ U 1 q
  change Langlands.Jacquet.Localization.mk τ U 1 (T (ρ m v)) =
    Langlands.Jacquet.Localization.mk τ U 1 (τ m (T v))
  rw [hT]

/-- A scalar-compatible pair of normalizing twists preserves equivariance. -/
theorem quotientEvaluation_twist_action (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (α : M →* Rˣ) (β : M →* Sˣ) (hα : ∀ m, e (α m : R) = (β m : S))
    (m : M) (q : Langlands.Jacquet.Localization.Coinvariants ρ U 1) :
    quotientEvaluation ρ τ U T hT
        (Langlands.twist α (Langlands.Jacquet.Localization.action ρ U 1 M hMU
          (Langlands.Jacquet.Localization.isInvariant_one U M hMU)) m q) =
      Langlands.twist β (Langlands.Jacquet.Localization.action τ U 1 M hMU
        (Langlands.Jacquet.Localization.isInvariant_one U M hMU)) m
        (quotientEvaluation ρ τ U T hT q) := by
  change quotientEvaluation ρ τ U T hT ((α m : R) • _) = (β m : S) • _
  rw [(quotientEvaluation ρ τ U T hT).map_smulₛₗ, hα, quotientEvaluation_action]

end Quotient

section FullInduction

variable {R S : Type*} [CommRing R] [CommRing S] {e : R →+* S}
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module S W]
  (P : Subgroup G) (ρ : Representation R P V) (τ : Representation S P W)
  (T : V →ₛₗ[e] W) (hT : ∀ p v, T (ρ p v) = τ p (T v))

/-- Semilinear postcomposition preserves covariance and a uniform open stabilizer. -/
def fullInductionEvaluation :
    Induction.SmoothFunctions P ρ →ₛₗ[e] Induction.SmoothFunctions P τ where
  toFun f :=
    ⟨⟨fun x => T (f.1.1 x), by
        intro p x
        exact (congrArg T (f.1.2 p x)).trans (hT p (f.1.1 x))⟩, by
      obtain ⟨K, hK⟩ := f.property
      refine ⟨K, ?_⟩
      intro k
      apply Subtype.ext
      funext x
      exact congrArg T
        (congrArg (fun F : Induction.EquivariantFunctions P ρ => F.1 x) (hK k))⟩
  map_add' f s := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact T.map_add (f.1.1 x) (s.1.1 x)
  map_smul' b f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact T.map_smulₛₗ b (f.1.1 x)

omit [IsTopologicalGroup G] in
@[simp] theorem fullInductionEvaluation_eval (f : Induction.SmoothFunctions P ρ) (x : G) :
    Induction.eval P τ (fullInductionEvaluation P ρ τ T hT f) x =
      T (Induction.eval P ρ f x) := rfl

theorem fullInductionEvaluation_action (g : G) (f : Induction.SmoothFunctions P ρ) :
    fullInductionEvaluation P ρ τ T hT (Induction.smoothInduced P ρ g f) =
      Induction.smoothInduced P τ g (fullInductionEvaluation P ρ τ T hT f) := rfl

end FullInduction

section Parabolic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (h : Aubert.General.IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance specializationTensorAddCommGroup (Y : Type*) [AddCommGroup Y] [Module ℂ Y] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] Y) :=
  TensorProduct.addCommGroup

/-- The complex inducing action with exactly the positive full-P normalization. -/
abbrev complexInducingRepresentation (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) : Representation ℂ P V :=
  Langlands.twist (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
    ((Langlands.twist χ.val.toMonoidHom σ).comp h.projection)

/-- The existing full complex smooth induced carrier at χ. -/
abbrev ComplexInduced (σ : Representation ℂ M V) (χ : unramifiedCharacters ν) :
    Type (max uG uV) :=
  Induction.SmoothFunctions P (complexInducingRepresentation ν h hU σ χ)

/-- Right translation on that complex full induced model. -/
abbrev complexInducedRepresentation (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) :
    Representation ℂ G (ComplexInduced ν h hU σ χ) :=
  Induction.smoothInduced P (complexInducingRepresentation ν h hU σ χ)

/-- The actual complex relation quotient of the full induced model at χ. -/
abbrev ComplexJacquet (σ : Representation ℂ M V) (χ : unramifiedCharacters ν) :
    Type (max uG uV) :=
  Langlands.Jacquet.Localization.Coinvariants (complexInducedRepresentation ν h hU σ χ) U 1

/-- The complex normalized Jacquet action with the inverse Levi half-character. -/
abbrev complexJacquetRepresentation (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) :
    Representation ℂ M (ComplexJacquet ν h hU σ χ) :=
  Langlands.twist (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
    (Langlands.Jacquet.Localization.action (complexInducedRepresentation ν h hU σ χ)
      U 1 M h.levi_le_normalizer
      (Langlands.Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer))

/-- Evaluation intertwines the positively normalized inducing actions. -/
theorem inducingEvaluation_action (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) (p : P)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) :
    tensorEvaluation ν V χ (universalInducingRepresentation ν h hU σ p t) =
      complexInducingRepresentation ν h hU σ χ p (tensorEvaluation ν V χ t) := by
  change tensorEvaluation ν V χ
    (((inductionCharacter ν U P hU h.le_normalizer).toMonoidHom p :
        unramifiedRegularFunctions ν) •
      universalUnramifiedRepresentation ν σ (h.projection p) t) = _
  rw [(tensorEvaluation ν V χ).map_smulₛₗ, tensorEvaluation_action]
  rfl

/-- Specialize every function value, preserving its single uniform open stabilizer. -/
def inducedEvaluation (σ : Representation ℂ M V) (χ : unramifiedCharacters ν) :
    UniversalInduced ν h hU σ →ₛₗ[evaluation ν χ] ComplexInduced ν h hU σ χ :=
  fullInductionEvaluation P (universalInducingRepresentation ν h hU σ)
    (complexInducingRepresentation ν h hU σ χ) (tensorEvaluation ν V χ)
    (inducingEvaluation_action ν h hU σ χ)

@[simp] theorem inducedEvaluation_eval (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) (f : UniversalInduced ν h hU σ) (x : G) :
    Induction.eval P (complexInducingRepresentation ν h hU σ χ)
        (inducedEvaluation ν h hU σ χ f) x =
      tensorEvaluation ν V χ
        (Induction.eval P (universalInducingRepresentation ν h hU σ) f x) := rfl

theorem inducedEvaluation_action (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) (g : G) (f : UniversalInduced ν h hU σ) :
    inducedEvaluation ν h hU σ χ (universalInducedRepresentation ν h hU σ g f) =
      complexInducedRepresentation ν h hU σ χ g (inducedEvaluation ν h hU σ χ f) := rfl

/-- Actual descended specialization, on quotient classes rather than a fiber identification. -/
def jacquetEvaluation (σ : Representation ℂ M V) (χ : unramifiedCharacters ν) :
    UniversalJacquet ν h hU σ →ₛₗ[evaluation ν χ] ComplexJacquet ν h hU σ χ :=
  quotientEvaluation (universalInducedRepresentation ν h hU σ)
    (complexInducedRepresentation ν h hU σ χ) U (inducedEvaluation ν h hU σ χ)
    (inducedEvaluation_action ν h hU σ χ)

@[simp] theorem jacquetEvaluation_mk (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) (f : UniversalInduced ν h hU σ) :
    jacquetEvaluation ν h hU σ χ
        (Langlands.Jacquet.Localization.mk (universalInducedRepresentation ν h hU σ) U 1 f) =
      Langlands.Jacquet.Localization.mk (complexInducedRepresentation ν h hU σ χ) U 1
        (inducedEvaluation ν h hU σ χ f) := rfl

theorem jacquetEvaluation_action (σ : Representation ℂ M V)
    (χ : unramifiedCharacters ν) (m : M) (q : UniversalJacquet ν h hU σ) :
    jacquetEvaluation ν h hU σ χ (universalJacquetRepresentation ν h hU σ m q) =
      complexJacquetRepresentation ν h hU σ χ m (jacquetEvaluation ν h hU σ χ q) :=
  quotientEvaluation_twist_action (universalInducedRepresentation ν h hU σ)
    (complexInducedRepresentation ν h hU σ χ) U
    (inducedEvaluation ν h hU σ χ) (inducedEvaluation_action ν h hU σ χ)
    M h.levi_le_normalizer
    (jacquetCharacter ν U M hU h.levi_le_normalizer).toMonoidHom
    (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
    (fun _ => rfl) m q

/-- The complex target is exactly the existing normalized induction of σ ⊗ χ. -/
theorem complexInducedRepresentation_eq_functor
    (A : SmoothRep.{0, uG, uV} ℂ M) (χ : unramifiedCharacters ν) :
    complexInducedRepresentation ν h hU A.representation χ =
      ((Aubert.General.normalizedInductionFunctor h hU).obj
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation := rfl

set_option backward.isDefEq.respectTransparency.types true in
/-- The complex quotient target is exactly the existing normalized Jacquet functor. -/
theorem complexJacquetRepresentation_heq_functor
    (A : SmoothRep.{0, uG, uV} ℂ M) (χ : unramifiedCharacters ν) :
    HEq (complexJacquetRepresentation ν h hU A.representation χ)
      ((Aubert.General.normalizedJacquetFunctor U M hU h.levi_le_normalizer).obj
        ((Aubert.General.normalizedInductionFunctor h hU).obj
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)))).representation := by
  have hI : SmoothRep.of (complexInducedRepresentation ν h hU A.representation χ)
      (Induction.smoothInduced_smooth P
        (complexInducingRepresentation ν h hU A.representation χ)) =
      (Aubert.General.normalizedInductionFunctor h hU).obj
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) := rfl
  have hJ := congrArg
    (Aubert.General.normalizedJacquetFunctor U M hU h.levi_le_normalizer).obj hI
  exact dependentCongr (fun X : SmoothRep.{0, uG, max uG uV} ℂ M =>
    X.representation) hJ

end Parabolic

end Langlands.Plancherel.UnramifiedNormalized
