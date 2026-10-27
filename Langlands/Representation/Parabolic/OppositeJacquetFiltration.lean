import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Filtration.ObjectDefinitions

/-! Actual images of finite filtrations in normalized opposite Jacquet quotients. -/

noncomputable section

namespace Langlands

universe uR uG uH uV uF

namespace Jacquet

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V] [Module R V]
  (U : Subgroup G) (f : H →* Subgroup.normalizer (U : Set G)) (χ : H →* Rˣ)

/-- The actual quotient image, invariant under the pulled-back, scalar-twisted action. -/
def normalizedImageSubrepresentation (ρ : Representation R G V) (S : Subrepresentation ρ) :
    Subrepresentation (twist χ ((action ρ U (Subgroup.normalizer U) le_rfl).comp f)) where
  toSubmodule := S.toSubmodule.map (mk ρ U)
  apply_mem_toSubmodule h := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨(χ h : R) • ρ (f h : G) v,
      S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hv), ?_⟩
    change mk ρ U ((χ h : R) • ρ (f h : G) v) =
      (χ h : R) • mk ρ U (ρ (f h : G) v)
    exact map_smul (mk ρ U) _ _

@[simp]
theorem normalizedImageSubrepresentation_toSubmodule
    (ρ : Representation R G V) (S : Subrepresentation ρ) :
    (normalizedImageSubrepresentation U f χ ρ S).toSubmodule =
      S.toSubmodule.map (mk ρ U) := rfl

@[simp]
theorem mem_normalizedImageSubrepresentation
    (ρ : Representation R G V) (S : Subrepresentation ρ) (q : Coinvariants ρ U) :
    q ∈ normalizedImageSubrepresentation U f χ ρ S ↔
      ∃ v ∈ S, mk ρ U v = q := Iff.rfl

theorem normalizedImageSubrepresentation_mono (ρ : Representation R G V)
    {S T : Subrepresentation ρ} (h : S ≤ T) :
    normalizedImageSubrepresentation U f χ ρ S ≤
      normalizedImageSubrepresentation U f χ ρ T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

@[simp]
theorem normalizedImageSubrepresentation_bot (ρ : Representation R G V) :
    normalizedImageSubrepresentation U f χ ρ ⊥ = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv0 : v = 0 := hv
    change mk ρ U v = 0
    rw [hv0, map_zero]
  · exact bot_le

@[simp]
theorem normalizedImageSubrepresentation_top (ρ : Representation R G V) :
    normalizedImageSubrepresentation U f χ ρ ⊤ = ⊤ := by
  apply le_antisymm le_top
  intro q _
  obtain ⟨v, rfl⟩ := mk_surjective ρ U q
  exact ⟨v, trivial, rfl⟩

/-- Keep the original length and index, taking the image under the actual quotient map. -/
def normalizedImageFiltration (ρ : Representation R G V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) :
    ObjectRepFiltration
      (Rep.of (twist χ ((action ρ U (Subgroup.normalizer U) le_rfl).comp f))) l :=
  ObjectRepFiltration.ofSubrepresentations
    (fun k => normalizedImageSubrepresentation U f χ ρ (s.subrepresentation k))
    (fun _ _ h => normalizedImageSubrepresentation_mono U f χ ρ
      (s.monotone_subrepresentation h))
    (by rw [s.subrepresentation_zero, normalizedImageSubrepresentation_bot])
    (by rw [s.subrepresentation_last, normalizedImageSubrepresentation_top])

@[simp]
theorem normalizedImageFiltration_subrepresentation (ρ : Representation R G V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1)) :
    (normalizedImageFiltration U f χ ρ s).subrepresentation k =
      normalizedImageSubrepresentation U f χ ρ (s.subrepresentation k) := rfl

@[simp]
theorem normalizedImageFiltration_toSubmodule (ρ : Representation R G V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1)) :
    ((normalizedImageFiltration U f χ ρ s).subrepresentation k).toSubmodule =
      (s.subrepresentation k).toSubmodule.map (mk ρ U) := rfl

/-- A quotient vector belongs to a step exactly when it has a representative in that step. -/
theorem mem_normalizedImageFiltration (ρ : Representation R G V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1))
    (q : Coinvariants ρ U) :
    q ∈ (normalizedImageFiltration U f χ ρ s).subrepresentation k ↔
      ∃ v ∈ s.subrepresentation k, mk ρ U v = q := Iff.rfl

end Jacquet

namespace PadicField.TopologicalData

open GeneralLinear Geometric Parabolic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Images of all original steps in the actual normalized inner opposite quotient. -/
def normalizedRefinedOppositeJacquetFiltration
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) :
    ObjectRepFiltration (Rep.of (T.normalizedRefinedOppositeJacquet B S ρ)) l :=
  Jacquet.normalizedImageFiltration (refinedOppositeUnipotent F.Carrier B S)
    (refinedOppositeLeviNormalizer F.Carrier B S)
    (Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S)) ρ s

@[simp]
theorem normalizedRefinedOppositeJacquetFiltration_toSubmodule
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1)) :
    ((T.normalizedRefinedOppositeJacquetFiltration B S ρ s).subrepresentation k).toSubmodule =
      (s.subrepresentation k).toSubmodule.map (refinedOppositeJacquetMk B S ρ) := rfl

theorem mem_normalizedRefinedOppositeJacquetFiltration
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1))
    (q : RefinedOppositeJacquetModule B S ρ) :
    q ∈ (T.normalizedRefinedOppositeJacquetFiltration B S ρ s).subrepresentation k ↔
      ∃ v ∈ s.subrepresentation k, refinedOppositeJacquetMk B S ρ v = q := Iff.rfl

/-- Images of all original steps in the actual normalized ambient opposite quotient. -/
def normalizedComposedOppositeJacquetFiltration
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) :
    ObjectRepFiltration (Rep.of (T.normalizedComposedOppositeJacquet B S ρ)) l :=
  Jacquet.normalizedImageFiltration (composedOppositeUnipotent F.Carrier B S)
    (composedOppositeLeviNormalizer F.Carrier B S)
    (Jacquet.inverseHalfCharacter (T.composedOppositeLeviModulus B S)) ρ s

@[simp]
theorem normalizedComposedOppositeJacquetFiltration_toSubmodule
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1)) :
    ((T.normalizedComposedOppositeJacquetFiltration B S ρ s).subrepresentation k).toSubmodule =
      (s.subrepresentation k).toSubmodule.map (composedOppositeJacquetMk B S ρ) := rfl

theorem mem_normalizedComposedOppositeJacquetFiltration
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {l : ℕ} (s : ObjectRepFiltration (Rep.of ρ) l) (k : Fin (l + 1))
    (q : ComposedOppositeJacquetModule B S ρ) :
    q ∈ (T.normalizedComposedOppositeJacquetFiltration B S ρ s).subrepresentation k ↔
      ∃ v ∈ s.subrepresentation k, composedOppositeJacquetMk B S ρ v = q := Iff.rfl

end PadicField.TopologicalData

end Langlands
