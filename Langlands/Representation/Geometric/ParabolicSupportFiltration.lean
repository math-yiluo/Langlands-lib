import Langlands.Representation.Geometric.SmoothSupportFiltration
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Filtration.Transport

/-! Support images in the actual normalized parabolic Jacquet quotient. -/

noncomputable section
open CategoryTheory
open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)

/-- The image of a parabolic-stable subspace in the actual normalized Jacquet module. -/
def normalizedJacquetImage (δ : B.Levi F →* ℝ≥0ˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V)
    (S : Subrepresentation (ρ.comp (B.parabolic F).subtype)) :
    Subrepresentation (B.normalizedJacquetOf δ ρ) where
  toSubmodule := S.toSubmodule.map (B.jacquetMk ρ)
  apply_mem_toSubmodule m := by
    rintro _ ⟨v, hv, rfl⟩
    rw [B.normalizedJacquetOf_mk]
    refine ⟨(((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
      ρ (B.leviEmbedding F m) v, ?_, ?_⟩
    · exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (B.leviInParabolic F m) hv)
    · exact map_smul (B.jacquetMk ρ) _ _

@[simp]
theorem mem_normalizedJacquetImage (δ : B.Levi F →* ℝ≥0ˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V)
    (S : Subrepresentation (ρ.comp (B.parabolic F).subtype)) (q : B.JacquetModule ρ) :
    q ∈ B.normalizedJacquetImage δ ρ S ↔ ∃ v ∈ S, B.jacquetMk ρ v = q := Iff.rfl

theorem normalizedJacquetImage_mono (δ : B.Levi F →* ℝ≥0ˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V)
    {S S' : Subrepresentation (ρ.comp (B.parabolic F).subtype)} (h : S ≤ S') :
    B.normalizedJacquetImage δ ρ S ≤ B.normalizedJacquetImage δ ρ S' := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

@[simp]
theorem normalizedJacquetImage_bot (δ : B.Levi F →* ℝ≥0ˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    B.normalizedJacquetImage δ ρ ⊥ = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.map_bot _

@[simp]
theorem normalizedJacquetImage_top (δ : B.Levi F →* ℝ≥0ˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    B.normalizedJacquetImage δ ρ ⊤ = ⊤ := by
  apply le_antisymm le_top
  intro q _
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ q
  exact ⟨v, trivial, rfl⟩

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Inflate and twist a smooth Levi representation to its parabolic covariance data. -/
def inducingFunctor (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤ Rep.{uV} ℂ (B.parabolic F) where
  obj A := Rep.of (B.inducingRepresentation χ A.representation)
  map f := Rep.ofHom (B.inducingMap χ (SmoothRep.hom f))
  map_id A := by ext v; rfl
  map_comp f g := by ext v; rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Geometric

open GeneralLinear
universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- Support filtration of actual normalized parabolic induction restricted to P_C. -/
def parabolicInductionSupportFiltration {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m) :
    letI := T.topology
    RepFunctorFiltration
      (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F.Carrier).subtype) m := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact s.rawSmoothSupportFiltration.precomp (B.inducingFunctor (T.leviHalfCharacter B))

/-- Take actual images of the support subfunctor in the normalized Jacquet quotient. -/
def parabolicJacquetImageSubfunctor
    (S : letI := T.topology
      RepSubfunctor (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F.Carrier).subtype)) :
    letI := T.topology
    RepSubfunctor (jacquetInductionFunctor.{uF, uV} T B C) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact {
    obj A := C.normalizedJacquetImage (T.leviModulus C)
      ((T.normalizedParabolicInductionFunctor B).obj A).representation (S.obj A)
    map_mem := by
      intro A A' f q hq
      obtain ⟨v, hv, rfl⟩ := hq
      exact ⟨((T.normalizedParabolicInductionFunctor B).map f).hom.hom v,
        S.map_mem f hv, rfl⟩ }

set_option maxHeartbeats 800000 in
/-- The fixed support-image filtration of the exact functor in the geometric lemma. -/
def parabolicJacquetSupportFiltration {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m) :
    letI := T.topology
    RepFunctorFiltration (jacquetInductionFunctor.{uF, uV} T B C) m := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let t := parabolicInductionSupportFiltration.{uF, uV} T B C s
  exact {
    step k := parabolicJacquetImageSubfunctor T B C (t.step k)
    monotone A := by
      intro i j hij
      exact C.normalizedJacquetImage_mono _ _ (t.monotone A hij)
    zero A := by
      change C.normalizedJacquetImage _ _ ((t.step 0).obj A) = ⊥
      rw [t.zero A, C.normalizedJacquetImage_bot]
    top A := by
      change C.normalizedJacquetImage _ _ ((t.step (Fin.last m)).obj A) = ⊤
      rw [t.top A, C.normalizedJacquetImage_top] }

end Langlands.Geometric
