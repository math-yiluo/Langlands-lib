import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Jacquet.ReciprocityProof
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Representation.Geometric.BruhatDescent
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-! Support lemmas for BZ77 Theorem 2.9(a), (i) ⇒ (ii). -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uG uV uW

section Frobenius

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n)
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The standard parabolic normalizes its unipotent radical inside `GL_n`. -/
theorem parabolic_le_normalizer_unipotentSubgroup :
    C.parabolic F.Carrier ≤
      Subgroup.normalizer (C.unipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) := by
  intro g hg
  apply Subgroup.le_normalizer_map
  exact ⟨⟨g, hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

/-- A nonzero map from the normalized Jacquet module gives a nonzero map to
normalized parabolic induction, by the orbit-map half of Frobenius reciprocity. -/
theorem exists_ne_zero_to_normalizedParabolicInduced
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : letI := T.topology; IsSmooth ρ)
    (τ : Representation ℂ (C.Levi F.Carrier) W)
    (φ : (T.normalizedJacquet C ρ).IntertwiningMap τ) (hφ : φ ≠ 0) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∃ f : ρ.IntertwiningMap (T.normalizedParabolicInduced C τ), f ≠ 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let P := C.parabolic F.Carrier
  let N := C.unipotentSubgroup F.Carrier
  let hPN := parabolic_le_normalizer_unipotentSubgroup (F := F) C
  let chi := C.inflateCharacter (T.leviHalfCharacter C)
  let sigma := τ.comp (C.leviProjection F.Carrier)
  let A : (twist chi.toMonoidHom⁻¹ (Jacquet.action ρ N P hPN)).IntertwiningMap sigma :=
    { toLinearMap := φ.toLinearMap ∘ₗ (C.jacquetModuleEquiv ρ).symm.toLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N q
        change φ ((C.jacquetModuleEquiv ρ).symm
            ((((chi.toMonoidHom g)⁻¹ : ℂˣ) : ℂ) • Jacquet.mk ρ N (ρ g v))) =
          τ (C.leviProjection F.Carrier g) (φ (C.jacquetMk ρ v))
        rw [map_smul, map_smul]
        change (((chi.toMonoidHom g)⁻¹ : ℂˣ) : ℂ) • φ (C.jacquetMk ρ (ρ g v)) = _
        have h1 : C.jacquetMk ρ (ρ g v) = C.jacquetMk ρ
            (ρ (C.leviEmbedding F.Carrier (C.leviProjection F.Carrier g)) v) :=
          Parabolic.mk_action_eq_levi C (ρ.comp (C.parabolic F.Carrier).subtype) g v
        have h2 := T.normalizedJacquet_mk_eq_inv_halfModulus C ρ
          (C.leviProjection F.Carrier g) v
        have h3 := Representation.IntertwiningMap.isIntertwining _ _ φ
          (C.leviProjection F.Carrier g) (C.jacquetMk ρ v)
        rw [h2, Units.smul_def, map_smul] at h3
        rw [← h3, h1]
        rfl }
  refine ⟨Jacquet.CharacterReciprocity.backward P N hPN ρ sigma chi hρ A, ?_⟩
  intro h0
  apply hφ
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective ρ x
  have h := congrArg (fun f => Induction.eval P (twist chi.toMonoidHom sigma) (f v) 1) h0
  change A (Jacquet.mk ρ N (ρ 1 v)) = 0 at h
  rw [map_one, Module.End.one_apply] at h
  exact h

end Frobenius

section Subquotient

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual smooth subquotient realizing the `i`th graded piece of an
object filtration of a smooth representation: the `i+1`st step modulo the
`i`th step pulled back into it. -/
def filtrationSubquotient (A : SmoothRep.{0, uG, uV} ℂ G) {r : ℕ}
    (s : ObjectRepFiltration (Rep.of A.representation) r) (i : Fin r) :
    SmoothRep.{0, uG, uV} ℂ G :=
  SmoothRep.subquotient A (s.subrepresentation i.succ)
    ((s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit))

theorem filtrationSubquotient_isSubquotient (A : SmoothRep.{0, uG, uV} ℂ G) {r : ℕ}
    (s : ObjectRepFiltration (Rep.of A.representation) r) (i : Fin r) :
    SmoothRep.IsSubquotient (filtrationSubquotient A s i) A :=
  ⟨_, _, ⟨Iso.refl _⟩⟩

/-- The filtration subquotient carries exactly the graded representation. -/
def filtrationSubquotientEquiv (A : SmoothRep.{0, uG, uV} ℂ G) {r : ℕ}
    (s : ObjectRepFiltration (Rep.of A.representation) r) (i : Fin r) :
    (filtrationSubquotient A s i).representation.Equiv (s.gradedRepresentation i).ρ :=
  Representation.Equiv.refl _

/-- If the filtration subquotient is an actual quotient of `A` and its graded
representation is equivalent to an irreducible `τ`, then `A` maps nonzero to `τ`. -/
theorem exists_ne_zero_of_isQuotient_filtrationSubquotient
    (A : SmoothRep.{0, uG, uV} ℂ G) {r : ℕ}
    (s : ObjectRepFiltration (Rep.of A.representation) r) (i : Fin r)
    (τ : Representation ℂ G W) (e : (s.gradedRepresentation i).ρ.Equiv τ)
    (hτ : Representation.IsIrreducible τ)
    (hq : SmoothRep.IsQuotient (filtrationSubquotient A s i) A) :
    ∃ φ : A.representation.IntertwiningMap τ, φ ≠ 0 := by
  obtain ⟨f, hf⟩ := hq
  let e' := (filtrationSubquotientEquiv A s i).trans e
  obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
    apply le_antisymm bot_le
    intro w _
    change w ∈ (⊥ : Submodule ℂ W)
    rw [h w]
    exact Submodule.zero_mem _
  obtain ⟨a, ha⟩ := hf (e'.symm w)
  refine ⟨e'.toIntertwiningMap.comp (SmoothRep.hom f), fun h0 => hw ?_⟩
  have h := congrArg (fun φ : A.representation.IntertwiningMap τ => φ a) h0
  change e'.toIntertwiningMap (SmoothRep.hom f a) = 0 at h
  rw [ha] at h
  rw [← h]
  exact (e'.toLinearEquiv.apply_symm_apply w).symm

end Subquotient

section Constituent

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n)

/-- If some graded piece of a filtration of the admissible Jacquet module
`r_C(i_B σ)` is equivalent to an irreducible cuspidal `τ`, then the cuspidal
constituent theorem and Frobenius reciprocity give a nonzero intertwiner
`i_B σ → i_C τ`. -/
theorem exists_ne_zero_of_gradedRepresentation_equiv
    (hcon : LeviCuspidalConstituentTheorem.{uF, max uF uV} F T C) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      let A := (T.normalizedJacquetFunctor C).obj
        ((T.normalizedParabolicInductionFunctor B).obj σ)
      A.IsAdmissible →
      ∀ (r : ℕ) (s : ObjectRepFiltration (Rep.of A.representation) r) (i : Fin r),
        Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.representation) →
        letI := T.generalLinearTopologicalGroup n
        ∃ f : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
            (T.normalizedParabolicInduced C τ.representation), f ≠ 0 := by
  intro σ τ hτ hτc A hA r s i ⟨e⟩
  let := T.topology
  let D := filtrationSubquotient A s i
  let eD : D.representation.Equiv τ.representation :=
    (filtrationSubquotientEquiv A s i).trans e
  have hDirr : D.IsIrreducible := (isIrreducible_iff_of_equiv eD).mpr hτ
  have hDc : IsLeviCuspidal C D.representation :=
    (isLeviCuspidal_iff_of_equiv C eD).mpr hτc
  have hq := (hcon A D hA hDirr hDc (filtrationSubquotient_isSubquotient A s i)).2
  obtain ⟨φ, hφ⟩ :=
    exists_ne_zero_of_isQuotient_filtrationSubquotient A s i τ.representation e hτ hq
  exact exists_ne_zero_to_normalizedParabolicInduced T C _
    (T.isSmooth_normalizedParabolicInduced B σ.representation) τ.representation φ hφ

end Constituent

end Langlands.CuspidalSupport
