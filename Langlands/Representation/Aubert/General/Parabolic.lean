import Langlands.Group.HaarModulus
import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Category.Twist
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Aubert.SubgroupTransition
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

/-!
# Normalized parabolic induction and Jacquet functors for actual subgroups

For an actual semidirect decomposition `P = M ⋉ U` of subgroups of a
nonarchimedean locally compact group `G`, with `U` closed, this file defines
normalized parabolic induction `i : SmoothRep ℂ M ⥤ SmoothRep ℂ G` and the
normalized Jacquet functor `r : SmoothRep ℂ G ⥤ SmoothRep ℂ M` on the full
smooth categories, following Bernstein–Zelevinsky and Renard VI.1:

* `r` takes the actual `U`-coinvariants with the `M`-action and twists by
  `δ_P^{-1/2}`, where `δ_P(m)` is the Haar modulus of conjugation by `m` on `U`;
* `i` inflates along the actual projection `P →* M`, twists by `δ_P^{1/2}` on
  `P` and takes smooth induction (right translation on smooth functions with
  `f (p g) = δ_P(p)^{1/2} σ(m(p)) f g`).

It also gives Levi-in-Levi versions, read inside an intermediate closed subgroup
through the actual continuous identification `L.subgroupOf M ≃ₜ* L`, and
conjugation transports between conjugate subgroups. No reductive structure is
constructed here: the subgroups, the decomposition and closedness are inputs.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

section Decomposition

variable {G : Type uG} [Group G]

/-- `P = M ⋉ U` for actual subgroups of `G`: `M` and `U` lie in `P`, `P`
normalizes `U`, and inside `P` the subgroups `M` and `U` are complements, i.e.
every element of `P` is uniquely `m * u` with `m ∈ M`, `u ∈ U`. -/
def IsSemidirectDecomposition (P M U : Subgroup G) : Prop :=
  M ≤ P ∧ U ≤ P ∧ P ≤ Subgroup.normalizer (U : Set G) ∧
    (M.subgroupOf P).IsComplement' (U.subgroupOf P)

namespace IsSemidirectDecomposition

variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
include h

theorem levi_le : M ≤ P := h.1

theorem unipotent_le : U ≤ P := h.2.1

theorem le_normalizer : P ≤ Subgroup.normalizer (U : Set G) := h.2.2.1

theorem levi_le_normalizer : M ≤ Subgroup.normalizer (U : Set G) :=
  h.levi_le.trans h.le_normalizer

theorem isComplement' : (M.subgroupOf P).IsComplement' (U.subgroupOf P) := h.2.2.2

omit h in
/-- The decomposition from the complement in the order `U * M`. -/
theorem of_isComplement'_symm (hMP : M ≤ P) (hUP : U ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hc : (U.subgroupOf P).IsComplement' (M.subgroupOf P)) :
    IsSemidirectDecomposition P M U :=
  ⟨hMP, hUP, hPU, hc.symm⟩

/-- The unipotent part is normal in the parabolic. -/
theorem normal : (U.subgroupOf P).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.unipotent_le).mpr h.le_normalizer

omit h in
/-- The actual Levi projection `P →* M`: the quotient `P ⧸ U` identified with
the complement `M`. -/
def projection (h : IsSemidirectDecomposition P M U) : P →* M :=
  letI := h.normal
  ((Subgroup.subgroupOfEquivOfLe h.levi_le).toMonoidHom.comp
    h.isComplement'.QuotientMulEquiv.toMonoidHom).comp
    (QuotientGroup.mk' (U.subgroupOf P))

/-- The projection is the identity on the Levi subgroup. -/
@[simp]
theorem projection_levi (m : M) :
    h.projection ⟨m, h.levi_le m.2⟩ = m := by
  let := h.normal
  have hm : (⟨m, h.levi_le m.2⟩ : P) ∈ M.subgroupOf P := m.2
  have key : h.isComplement'.QuotientMulEquiv
      (QuotientGroup.mk' (U.subgroupOf P) ⟨m, h.levi_le m.2⟩) = ⟨⟨m, h.levi_le m.2⟩, hm⟩ := by
    rw [← MulEquiv.eq_symm_apply]
    rfl
  change Subgroup.subgroupOfEquivOfLe h.levi_le (h.isComplement'.QuotientMulEquiv
      (QuotientGroup.mk' (U.subgroupOf P) ⟨m, h.levi_le m.2⟩)) = m
  rw [key]
  rfl

/-- The projection kills the unipotent subgroup. -/
@[simp]
theorem projection_unipotent (u : U) :
    h.projection ⟨u, h.unipotent_le u.2⟩ = 1 := by
  let := h.normal
  have hu : QuotientGroup.mk' (U.subgroupOf P) ⟨u, h.unipotent_le u.2⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr u.2
  change Subgroup.subgroupOfEquivOfLe h.levi_le (h.isComplement'.QuotientMulEquiv
      (QuotientGroup.mk' (U.subgroupOf P) ⟨u, h.unipotent_le u.2⟩)) = 1
  rw [hu, map_one, map_one]

/-- The kernel of the projection is the unipotent subgroup. -/
theorem projection_eq_one_iff (p : P) : h.projection p = 1 ↔ (p : G) ∈ U := by
  let := h.normal
  constructor
  · intro hp
    have h1 : h.isComplement'.QuotientMulEquiv (QuotientGroup.mk' (U.subgroupOf P) p) = 1 :=
      (Subgroup.subgroupOfEquivOfLe h.levi_le).injective (by
        rw [map_one]
        exact hp)
    have h2 : QuotientGroup.mk' (U.subgroupOf P) p = 1 :=
      h.isComplement'.QuotientMulEquiv.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff p).mp h2
  · intro hp
    exact h.projection_unipotent ⟨p, hp⟩

/-- Every element of the parabolic is its projection times an element of `U`. -/
theorem projection_inv_mul_mem (p : P) :
    ((h.projection p : M) : G)⁻¹ * (p : G) ∈ U := by
  have hq := (h.projection_eq_one_iff ((⟨h.projection p, h.levi_le (h.projection p).2⟩ : P)⁻¹ * p)).mp
  apply hq
  rw [map_mul, map_inv, h.projection_levi, inv_mul_cancel]

/-- The projection is characterized by `m⁻¹ p ∈ U`. -/
theorem projection_eq_iff (p : P) (m : M) :
    h.projection p = m ↔ (m : G)⁻¹ * (p : G) ∈ U := by
  have key := h.projection_eq_one_iff ((⟨m, h.levi_le m.2⟩ : P)⁻¹ * p)
  rw [map_mul, map_inv, h.projection_levi, inv_mul_eq_one, eq_comm] at key
  exact key

/-- The projection of `m * u`. -/
theorem projection_mul (m : M) (u : U) :
    h.projection (⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩) = m := by
  rw [map_mul, h.projection_levi, h.projection_unipotent, mul_one]

end IsSemidirectDecomposition

end Decomposition

section Functors

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The smooth normalizing character `δ_P^{1/2}` on the actual parabolic: the
positive square root of the Haar modulus of conjugation by `P` on the closed
subgroup `U`, as a complex character. -/
def inductionCharacter (U P : Subgroup G) (hU : IsClosed (U : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) : Induction.SmoothCharacter ℂ P where
  toMonoidHom := HaarModulus.closedHalfCharacter U hU P hPU
  isOpen_ker := HaarModulus.isOpen_ker_closedHalfCharacter U hU P hPU

@[simp]
theorem inductionCharacter_toMonoidHom (U P : Subgroup G) (hU : IsClosed (U : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    (inductionCharacter U P hU hPU).toMonoidHom = HaarModulus.closedHalfCharacter U hU P hPU :=
  rfl

/-- Normalized Jacquet restriction `r : SmoothRep ℂ G ⥤ SmoothRep ℂ M`: the
actual `U`-coinvariants with the descended `M`-action, twisted by `δ_P^{-1/2}`. -/
def normalizedJacquetFunctor (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ M :=
  Jacquet.Localization.smoothFunctor U 1 M hMU (Jacquet.Localization.isInvariant_one U M hMU) ⋙
    SmoothRep.twistFunctor (HaarModulus.closedInverseHalfCharacter U hU M hMU)
      (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M hMU)

/-- The normalized Jacquet module is carried by the actual `U`-coinvariants. -/
theorem normalizedJacquetFunctor_obj_representation (U M : Subgroup G)
    (hU : IsClosed (U : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    ((normalizedJacquetFunctor U M hU hMU).obj A).representation =
      Langlands.twist (HaarModulus.closedInverseHalfCharacter U hU M hMU)
        (Jacquet.Localization.action A.representation U 1 M hMU
          (Jacquet.Localization.isInvariant_one U M hMU)) :=
  rfl

/-- The action on a coinvariant class: `m · [v] = δ_P(m)^{-1/2} [m v]`. -/
theorem normalizedJacquetFunctor_obj_apply (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ G)
    (m : M) (v : A) :
    ((normalizedJacquetFunctor U M hU hMU).obj A).representation m
        (Jacquet.Localization.mk A.representation U 1 v) =
      ((HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk A.representation U 1 (A.representation m v) :=
  rfl

/-- The action on actual equivariant maps: `[v] ↦ [f v]`. -/
theorem normalizedJacquetFunctor_map_mk (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {A B : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (v : A) :
    SmoothRep.hom ((normalizedJacquetFunctor U M hU hMU).map f)
        (Jacquet.Localization.mk A.representation U 1 v) =
      Jacquet.Localization.mk B.representation U 1 (SmoothRep.hom f v) :=
  rfl

variable {P M U : Subgroup G}

/-- Inflation along the actual Levi projection, from smooth `M`-representations
to Mathlib's representation category of `P`. -/
def inflationFunctor (h : IsSemidirectDecomposition P M U) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ Rep.{uV} ℂ P :=
  SmoothRep.toRep ⋙ Rep.resFunctor h.projection

/-- Normalized parabolic induction `i : SmoothRep ℂ M ⥤ SmoothRep ℂ G`: inflate
along `P →* M`, twist by `δ_P^{1/2}` on `P`, and take smooth induction. Carriers
are saturated to `Type (max uG uV)`. -/
def normalizedInductionFunctor (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  inflationFunctor h ⋙
    Induction.normalizedSmoothInductionFunctor P (inductionCharacter U P hU h.le_normalizer)

/-- The inducing representation of `P` on the carrier of a smooth `M`-representation:
`p ↦ δ_P(p)^{1/2} σ(m(p))`. -/
abbrev inducingRepresentation (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation ℂ P A :=
  Langlands.twist (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
    (A.representation.comp h.projection)

/-- The normalized induced representation is smooth induction of the inducing
representation. -/
theorem normalizedInductionFunctor_obj_representation (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj A).representation =
      Induction.smoothInduced P (inducingRepresentation h hU A) :=
  rfl

/-- The covariance of a normalized induced function:
`f (p g) = δ_P(p)^{1/2} σ(m(p)) (f g)`. -/
theorem normalizedInductionFunctor_covariant (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (p : P) (g : G) :
    Induction.eval P (inducingRepresentation h hU A) f ((p : G) * g) =
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
        A.representation (h.projection p)
          (Induction.eval P (inducingRepresentation h hU A) f g) :=
  f.1.2 p g

/-- `G` acts on normalized induced functions by right translation. -/
theorem normalizedInductionFunctor_obj_apply (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (g : G) (f : (normalizedInductionFunctor h hU).obj A) (x : G) :
    Induction.eval P (inducingRepresentation h hU A)
        (((normalizedInductionFunctor h hU).obj A).representation g f) x =
      Induction.eval P (inducingRepresentation h hU A) f (x * g) :=
  rfl

/-- The action on actual equivariant maps is postcomposition. -/
theorem normalizedInductionFunctor_map_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {A B : SmoothRep.{0, uG, uV} ℂ M} (φ : A ⟶ B)
    (f : (normalizedInductionFunctor h hU).obj A) (x : G) :
    Induction.eval P (inducingRepresentation h hU B)
        (SmoothRep.hom ((normalizedInductionFunctor h hU).map φ) f) x =
      SmoothRep.hom φ (Induction.eval P (inducingRepresentation h hU A) f x) :=
  rfl

/-- Normalized Jacquet restriction attached to a semidirect decomposition. -/
abbrev jacquetFunctor (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G)) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ M :=
  normalizedJacquetFunctor U M hU h.levi_le_normalizer

/-- The composite `i ∘ r` on the full smooth category with saturated carriers
`Type (max uG uV)`. -/
def inductionJacquetFunctor (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) :
    SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  jacquetFunctor.{uG, max uG uV} h hU ⋙ normalizedInductionFunctor.{uG, max uG uV} h hU

section Normalization

variable {P M U : Subgroup G}

/-- The induction character restricted to the Levi is the Levi half modulus
`δ_P^{1/2}|_M`. -/
theorem closedHalfCharacter_levi (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (m : M) :
    HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨m, h.levi_le m.2⟩ =
      HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m :=
  rfl

/-- Named hypothesis: inner automorphisms of the closed subgroup `U` have trivial
Haar modulus, i.e. `U` is unimodular. -/
def IsUnimodularModulus (U : Subgroup G) (hU : IsClosed (U : Set G)) : Prop :=
  ∀ u : U, HaarModulus.closedNormalizerCharacter U hU ⟨u, Subgroup.le_normalizer u.2⟩ = 1

/-- If every compact subset of `U` lies in a compact subgroup (BZ77's limit of
compact subgroups), then `U` is unimodular: the modulus of an inner automorphism
by `u ∈ K`, `K` compact, has finite order because the kernel is open, hence is
`1` in the torsion-free positive reals. -/
theorem isUnimodularModulus_of_isLimitOfCompactSubgroups (U : Subgroup G)
    (hU : IsClosed (U : Set G)) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    IsUnimodularModulus U hU := by
  intro u
  obtain ⟨K, hK, huK⟩ := hUc {u} isCompact_singleton
  let ι : K →* Subgroup.normalizer (U : Set G) :=
    { toFun := fun k => ⟨((k : U) : G), Subgroup.le_normalizer (k : U).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Continuous ι := by
    change Continuous fun k : K =>
      (⟨((k : U) : G), Subgroup.le_normalizer (k : U).2⟩ : Subgroup.normalizer (U : Set G))
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let χ := (HaarModulus.closedNormalizerCharacter U hU).comp ι
  have hopen : IsOpen (χ.ker : Set K) :=
    (HaarModulus.isOpen_ker_closedNormalizerCharacter U hU).preimage hι
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Finite (K ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  let k : K := ⟨u, huK rfl⟩
  have hk : k ^ Nat.card (K ⧸ χ.ker) ∈ χ.ker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hpow : ((χ k : NNReal)) ^ Nat.card (K ⧸ χ.ker) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, MonoidHom.mem_ker.mp hk, Units.val_one]
  have h1 : (χ k : NNReal) = 1 :=
    (pow_eq_one_iff_of_nonneg (by positivity) Nat.card_pos.ne').mp hpow
  exact Units.ext h1

/-- On a unimodular `U` the induction character is trivial. -/
theorem closedHalfCharacter_unipotent (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU) (u : U) :
    HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨u, h.unipotent_le u.2⟩ = 1 := by
  have hu : HaarModulus.closedRestrictCharacter U hU P h.le_normalizer ⟨u, h.unipotent_le u.2⟩ = 1 :=
    hδ u
  simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, hu, map_one]

/-- With `U` unimodular, the induction character on `P` is the inflation of the
Levi half modulus along the projection. -/
theorem closedHalfCharacter_eq_comp_projection (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU) :
    HaarModulus.closedHalfCharacter U hU P h.le_normalizer =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer).comp h.projection := by
  ext p
  let m := h.projection p
  let u : U := ⟨((m : M) : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hp : p = ⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩ := by
    ext
    simp [u]
  rw [MonoidHom.comp_apply, hp, map_mul, closedHalfCharacter_unipotent h hU hδ, mul_one,
    closedHalfCharacter_levi h hU, h.projection_mul]

/-- With `U` unimodular, the inducing representation of `i (r A)` is the
unnormalized quotient action of `P` on the actual `U`-coinvariants used in
`Aubert.SubgroupTransition`: the half-modulus twists cancel. -/
theorem inducingRepresentation_jacquet_eq (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    inducingRepresentation h hU ((jacquetFunctor h hU).obj A) =
      SubgroupTransition.inducing P U h.le_normalizer A.representation := by
  apply MonoidHom.ext
  intro p
  apply LinearMap.ext
  intro c
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 c
  let m := h.projection p
  let u : U := ⟨((m : M) : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hpu : (p : G) = (m : G) * (u : G) := by simp [u]
  have hv : Jacquet.Localization.mk A.representation U 1 (A.representation p v) =
      Jacquet.Localization.mk A.representation U 1 (A.representation m v) := by
    rw [hpu, map_mul, Module.End.mul_apply]
    have hrel := Jacquet.Localization.relations_stable A.representation U 1 M
      h.levi_le_normalizer (Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer) m
      (Jacquet.Localization.sub_mem_relations A.representation U 1 u v)
    rw [Jacquet.Localization.mk_eq_iff, ← map_sub]
    simpa using hrel
  have hχ : ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) *
      ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer m : ℂˣ) : ℂ) = 1 := by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ, MonoidHom.comp_apply, ← Units.val_mul]
    simp [HaarModulus.closedHalfCharacter, HaarModulus.closedInverseHalfCharacter,
      Jacquet.inverseHalfCharacter, m]
  change ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
      (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk A.representation U 1 (A.representation m v)) =
      Jacquet.Localization.mk A.representation U 1 (A.representation p v)
  rw [smul_smul, hχ, one_smul, hv]

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The identity intertwiner between equal representations. -/
def intertwiningOfEq {H : Type uG} [Group H] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ τ : Representation ℂ H V} (e : σ = τ) : σ.IntertwiningMap τ where
  toLinearMap := LinearMap.id
  isIntertwining' _ := by
    subst e
    rfl

/-- With `U` unimodular, `i (r A)` is isomorphic to the unnormalized term
`SubgroupTransition.term P U` of `A`; the isomorphism is the identity on
induced functions. -/
def inductionJacquetTermIso (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    (inductionJacquetFunctor.{uG, uV} h hU).obj A ≅
      SmoothRep.of (SubgroupTransition.term P U h.le_normalizer A.representation)
        (Induction.smoothInduced_smooth _ _) where
  hom := SmoothRep.ofHom (Induction.smoothInducedMap P
    (intertwiningOfEq (inducingRepresentation_jacquet_eq h hU hδ A)))
  inv := SmoothRep.ofHom (Induction.smoothInducedMap P
    (intertwiningOfEq (inducingRepresentation_jacquet_eq h hU hδ A).symm))
  hom_inv_id := by
    ext f
    rfl
  inv_hom_id := by
    ext f
    rfl

/-- The comparison isomorphism keeps every induced function. -/
theorem inductionJacquetTermIso_hom_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (f : (inductionJacquetFunctor.{uG, uV} h hU).obj A)
    (x : G) :
    Induction.eval P (SubgroupTransition.inducing P U h.le_normalizer A.representation)
        (SmoothRep.hom (inductionJacquetTermIso h hU hδ A).hom f) x =
      Induction.eval P (inducingRepresentation h hU ((jacquetFunctor h hU).obj A)) f x :=
  rfl

/-- The inverse comparison isomorphism keeps every induced function. -/
theorem inductionJacquetTermIso_inv_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (f : SmoothRep.of (SubgroupTransition.term P U h.le_normalizer A.representation)
      (Induction.smoothInduced_smooth _ _)) (x : G) :
    Induction.eval P (inducingRepresentation h hU ((jacquetFunctor h hU).obj A))
        (SmoothRep.hom (inductionJacquetTermIso.{uG, uV} h hU hδ A).inv f) x =
      Induction.eval P (SubgroupTransition.inducing P U h.le_normalizer A.representation) f x :=
  rfl

/-- Naturality of the comparison in the ambient representation: it intertwines
`i (r φ)` with Worker 194's `SubgroupTransition.termMap` of `φ`. -/
theorem inductionJacquetTermIso_natural (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B) :
    (SmoothRep.hom (inductionJacquetTermIso.{uG, uV} h hU hδ B).hom).comp
        (SmoothRep.hom ((inductionJacquetFunctor.{uG, uV} h hU).map φ)) =
      (SubgroupTransition.termMap P U h.le_normalizer (SmoothRep.hom φ)).comp
        (SmoothRep.hom (inductionJacquetTermIso.{uG, uV} h hU hδ A).hom) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

end Normalization

end Functors

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The continuous identification of `L.subgroupOf M` with `L` for `L ≤ M`. -/
def subgroupOfContinuousEquiv {L M : Subgroup G} (hLM : L ≤ M) :
    L.subgroupOf M ≃ₜ* L where
  toMulEquiv := Subgroup.subgroupOfEquivOfLe hLM
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem subgroupOfContinuousEquiv_apply {L M : Subgroup G} (hLM : L ≤ M)
    (x : L.subgroupOf M) : ((subgroupOfContinuousEquiv hLM x : L) : G) = ((x : M) : G) :=
  rfl

@[simp]
theorem subgroupOfContinuousEquiv_symm_apply {L M : Subgroup G} (hLM : L ≤ M) (x : L) :
    (((subgroupOfContinuousEquiv hLM).symm x : M) : G) = (x : G) :=
  rfl

variable [IsTopologicalGroup G]

/-- Conjugation `x ↦ g⁻¹ x g` from `N` to `M` when `N = g M g⁻¹`. -/
def conjugationEquiv (g : G) {M N : Subgroup G} (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    N ≃ₜ* M where
  toFun x := ⟨g⁻¹ * x * g, (hMN x).mp x.2⟩
  invFun y := ⟨g * y * g⁻¹, (hMN _).mpr (by simp [mul_assoc])⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem conjugationEquiv_apply (g : G) {M N : Subgroup G}
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (x : N) :
    ((conjugationEquiv g hMN x : M) : G) = g⁻¹ * x * g :=
  rfl

/-- Conjugation transport `σ ↦ ᵍσ`, `(ᵍσ)(x) = σ(g⁻¹ x g)`, from smooth
representations of `M` to smooth representations of `N = g M g⁻¹`. -/
def conjugationFunctor (g : G) {M N : Subgroup G} (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ N :=
  SmoothRep.pullbackFunctor (conjugationEquiv g hMN)

theorem conjugationFunctor_obj_apply (g : G) {M N : Subgroup G}
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (A : SmoothRep.{0, uG, uV} ℂ M)
    (x : N) (v : A) :
    ((conjugationFunctor g hMN).obj A).representation x v =
      A.representation (conjugationEquiv g hMN x) v :=
  rfl

end Transport

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Levi-in-Levi normalized induction `i^M_L : SmoothRep ℂ L ⥤ SmoothRep ℂ M`
for subgroups `L ≤ Q`, `N ≤ Q` of a closed subgroup `M`, where inside `M` the
decomposition `Q = L ⋉ N` holds: transport along `L.subgroupOf M ≃ₜ* L`, then
normalized induction inside the locally compact group `M`. -/
def leviNormalizedInductionFunctor {M Q L N : Subgroup G} (hM : IsClosed (M : Set G))
    (hLM : L ≤ M) (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) :
    SmoothRep.{0, uG, uV} ℂ L ⥤ SmoothRep.{0, uG, max uG uV} ℂ M :=
  letI := hM.locallyCompactSpace
  SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM) ⋙
    normalizedInductionFunctor h (hN.preimage continuous_subtype_val)

/-- Levi-in-Levi normalized Jacquet restriction `r^M_L : SmoothRep ℂ M ⥤ SmoothRep ℂ L`:
normalized Jacquet restriction inside `M`, then transport along
`L ≃ₜ* L.subgroupOf M`. -/
def leviNormalizedJacquetFunctor {M Q L N : Subgroup G} (hM : IsClosed (M : Set G))
    (hLM : L ≤ M) (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ L :=
  letI := hM.locallyCompactSpace
  jacquetFunctor h (hN.preimage continuous_subtype_val) ⋙
    SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM).symm

end Levi

end Langlands.Aubert.General
