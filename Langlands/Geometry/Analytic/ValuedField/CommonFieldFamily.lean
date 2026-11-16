import Langlands.Geometry.Analytic.ValuedField.AmalgamationProof
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Order.Compact

/-! # A common complete field for a family of ultrametric extensions -/

noncomputable section

universe u

namespace Langlands.Analytic.ValuedField

private theorem exists_cofinal_limit {I A : Type u}
    (f : Finset I → A → ℝ)
    (hb : ∀ a, ∃ B : ℝ, ∀ s, f s a ∈ Set.Icc 0 B) :
    ∃ q : A → ℝ, ∀ (s : Finset I) (C : Set (A → ℝ)),
      IsClosed C → (∀ t, s ⊆ t → f t ∈ C) → q ∈ C := by
  classical
  choose B hB using hb
  let cube : Set (A → ℝ) := Set.pi Set.univ (fun a => Set.Icc 0 (B a))
  have hc : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc
  let T (s : Finset I) : Set (A → ℝ) :=
    closure (Set.range (fun t : {t : Finset I // s ⊆ t} => f t.val))
  have hTsub (s : Finset I) : T s ⊆ cube := by
    apply closure_minimal _ hc.isClosed
    rintro _ ⟨t, rfl⟩ a _
    exact hB a t.val
  have hTdir : Directed (· ⊇ ·) T := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · apply closure_mono
      rintro _ ⟨r, rfl⟩
      exact ⟨⟨r.val, Finset.Subset.trans Finset.subset_union_left r.property⟩, rfl⟩
    · apply closure_mono
      rintro _ ⟨r, rfl⟩
      exact ⟨⟨r.val, Finset.Subset.trans Finset.subset_union_right r.property⟩, rfl⟩
  have hTne (s : Finset I) : (T s).Nonempty :=
    ⟨f s, subset_closure ⟨⟨s, Finset.Subset.refl s⟩, rfl⟩⟩
  obtain ⟨q, hq⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hTdir hTne
      (fun s => hc.of_isClosed_subset isClosed_closure (hTsub s))
      (fun _ => isClosed_closure)
  refine ⟨q, fun s C hC hf => ?_⟩
  apply closure_minimal _ hC (Set.mem_iInter.mp hq s)
  rintro _ ⟨t, rfl⟩
  exact hf t.val t.property

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I : Type u} (E : I → Type u)
  [∀ i, NormedField (E i)] [∀ i, IsUltrametricDist (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, NormedAlgebra K (E i)]

private structure FiniteModel (s : Finset I) where
  Carrier : Type u
  [field : NormedField Carrier]
  [ultra : IsUltrametricDist Carrier]
  [complete : CompleteSpace Carrier]
  [algebra : NormedAlgebra K Carrier]
  embedding : ∀ i ∈ s, BoundedAlgHom K (E i) Carrier
  isometry : ∀ i hi, Isometry (embedding i hi)

attribute [instance] FiniteModel.field FiniteModel.ultra FiniteModel.complete FiniteModel.algebra

private def baseEmbedding (F : Type u) [NormedField F] [NormedAlgebra K F] :
    BoundedAlgHom K K F where
  toAlgHom := Algebra.ofId K F
  bounded := ⟨1, zero_lt_one, fun a => by
    change ‖algebraMap K F a‖ ≤ 1 * ‖a‖
    simp⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem baseEmbedding_isometry (F : Type u) [NormedField F] [NormedAlgebra K F] :
    Isometry (baseEmbedding K F) := by
  apply AddMonoidHomClass.isometry_of_norm (baseEmbedding K F).toAlgHom
  intro a
  change ‖algebraMap K F a‖ = ‖a‖
  simp

private theorem finiteModel_nonempty (s : Finset I) : Nonempty (FiniteModel K E s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨{
        Carrier := K
        embedding := fun i hi => False.elim (Finset.notMem_empty i hi)
        isometry := fun i hi => False.elim (Finset.notMem_empty i hi)
      }⟩
  | @insert i s _ ih =>
      obtain ⟨M⟩ := ih
      obtain ⟨L, _, _, _, _, f, g, _, hf, hg⟩ :=
        completeFieldAmalgamation K K M.Carrier (E i)
          (baseEmbedding K M.Carrier) (baseEmbedding K (E i))
          (baseEmbedding_isometry K M.Carrier) (baseEmbedding_isometry K (E i))
      let e : ∀ j ∈ insert i s, BoundedAlgHom K (E j) L := by
        intro j hj
        by_cases hji : j = i
        · subst j
          exact g
        · exact f.comp (M.embedding j ((Finset.mem_insert.mp hj).resolve_left hji))
      refine ⟨{
        Carrier := L
        embedding := e
        isometry := ?_
      }⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa [e] using hg
      · simpa [e, hji, BoundedAlgHom.comp, Function.comp_def] using
          hf.comp (M.isometry j ((Finset.mem_insert.mp hj).resolve_left hji))

private def finiteModel (s : Finset I) : FiniteModel K E s :=
  Classical.choice (finiteModel_nonempty K E s)

private abbrev FamilyRing := MvPolynomial (Sigma E) K

private def finiteVariable (s : Finset I) (a : Sigma E) :
    (finiteModel K E s).Carrier := by
  classical
  exact if h : a.1 ∈ s then (finiteModel K E s).embedding a.1 h a.2 else 0

private def finiteEvaluation (s : Finset I) :
    FamilyRing K E →+* (finiteModel K E s).Carrier :=
  MvPolynomial.eval₂Hom (algebraMap K _) (finiteVariable K E s)

private def finiteSeminorm (s : Finset I) (p : FamilyRing K E) : ℝ :=
  ‖finiteEvaluation K E s p‖

private theorem finiteVariable_norm_le (s : Finset I) (a : Sigma E) :
    ‖finiteVariable K E s a‖ ≤ ‖a.2‖ := by
  classical
  dsimp [finiteVariable]
  split
  · exact ((finiteModel K E s).isometry a.1 _ |>.norm_map_of_map_zero
      (map_zero ((finiteModel K E s).embedding a.1 _).toAlgHom) a.2).le
  · simp

private theorem finiteSeminorm_bounded (p : FamilyRing K E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, finiteSeminorm K E s p ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨‖a‖, norm_nonneg _, fun s => ?_⟩
      simp [finiteSeminorm, finiteEvaluation]
  | add p r hp hr =>
      obtain ⟨B, hB0, hB⟩ := hp
      obtain ⟨C, hC0, hC⟩ := hr
      refine ⟨B + C, add_nonneg hB0 hC0, fun s => ?_⟩
      simp only [finiteSeminorm, map_add]
      exact (norm_add_le _ _).trans (add_le_add (hB s) (hC s))
  | mul_X p a hp =>
      obtain ⟨B, hB0, hB⟩ := hp
      refine ⟨B * ‖a.2‖, mul_nonneg hB0 (norm_nonneg _), fun s => ?_⟩
      change ‖finiteEvaluation K E s (p * MvPolynomial.X a)‖ ≤ B * ‖a.2‖
      rw [map_mul, norm_mul]
      simp only [finiteEvaluation, MvPolynomial.eval₂Hom_X']
      exact mul_le_mul (hB s) (finiteVariable_norm_le K E s a)
        (norm_nonneg _) hB0

private def seminormConditions {A : Type u} [CommRing A] (q : A → ℝ) : Prop :=
  q 0 = 0 ∧ q 1 = 1 ∧ (∀ a b, q (a * b) = q a * q b) ∧
    (∀ a b, q (a + b) ≤ max (q a) (q b)) ∧
    (∀ a, q (-a) = q a) ∧ (∀ a, 0 ≤ q a)

private theorem seminormConditions_closed {A : Type u} [CommRing A] :
    IsClosed {q : A → ℝ | seminormConditions q} := by
  simp only [seminormConditions, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply 1) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a * b))
        ((continuous_apply a).mul (continuous_apply b))).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (continuous_apply (a + b))
        ((continuous_apply a).max (continuous_apply b))).inter
    ((isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (-a)) (continuous_apply a)).inter
      (isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a))))))

private theorem finiteSeminorm_conditions (s : Finset I) :
    seminormConditions (finiteSeminorm K E s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finiteSeminorm]
  · simp [finiteSeminorm]
  · intro a b
    simp [finiteSeminorm, map_mul, norm_mul]
  · intro a b
    simp only [finiteSeminorm, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _
  · intro a
    simp [finiteSeminorm]
  · exact fun _ => norm_nonneg _

private theorem exists_familySeminorm :
    ∃ q : MulRingSeminorm (FamilyRing K E), IsNonarchimedean q ∧
      ∀ p c, (∃ s : Finset I, ∀ t, s ⊆ t → finiteSeminorm K E t p = c) → q p = c := by
  obtain ⟨q₀, hq₀⟩ := exists_cofinal_limit (finiteSeminorm K E) (by
    intro p
    obtain ⟨B, _, hB⟩ := finiteSeminorm_bounded K E p
    exact ⟨B, fun s => ⟨norm_nonneg _, hB s⟩⟩)
  have hq : seminormConditions q₀ :=
    hq₀ ∅ _ seminormConditions_closed (fun s _ => finiteSeminorm_conditions K E s)
  let q : MulRingSeminorm (FamilyRing K E) := {
    toFun := q₀
    map_zero' := hq.1
    map_one' := hq.2.1
    map_mul' := hq.2.2.1
    add_le' := fun _ _ => IsNonarchimedean.add_le hq.2.2.2.2.2 hq.2.2.2.1
    neg' := hq.2.2.2.2.1
  }
  refine ⟨q, hq.2.2.2.1, ?_⟩
  rintro p c ⟨s, hs⟩
  exact hq₀ s {q | q p = c}
    (isClosed_eq (continuous_apply p) continuous_const) hs

private theorem finiteEvaluation_X (s : Finset I) (i : I) (hi : i ∈ s) (x : E i) :
    finiteEvaluation K E s (MvPolynomial.X ⟨i, x⟩) =
      (finiteModel K E s).embedding i hi x := by
  classical
  simp [finiteEvaluation, finiteVariable, hi]

/-- A family of complete ultrametric extensions of a complete field admits
isometric coefficient-compatible embeddings into one complete field, without
raising the universe. -/
theorem exists_commonFieldFamily :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : NormedAlgebra K L)
      (e : ∀ i, BoundedAlgHom K (E i) L), ∀ i, Isometry (e i) := by
  classical
  obtain ⟨q, hqna, hqevent⟩ := exists_familySeminorm K E
  obtain ⟨L, _, _, _, r, hr⟩ := seminormRealization (FamilyRing K E) q hqna
  have hC (c : K) : ‖r (MvPolynomial.C c)‖ = ‖c‖ := by
    rw [hr]
    apply hqevent
    refine ⟨∅, fun s _ => ?_⟩
    simp [finiteSeminorm, finiteEvaluation]
  have hX (i : I) (x : E i) : ‖r (MvPolynomial.X ⟨i, x⟩)‖ = ‖x‖ := by
    rw [hr]
    apply hqevent
    refine ⟨{i}, fun s hs => ?_⟩
    rw [finiteSeminorm, finiteEvaluation_X K E s i (hs (Finset.mem_singleton_self i))]
    exact (finiteModel K E s).isometry i _ |>.norm_map_of_map_zero
      (map_zero ((finiteModel K E s).embedding i _).toAlgHom) x
  have hz (i : I) (p : FamilyRing K E)
      (hp : ∀ s, i ∈ s → finiteEvaluation K E s p = 0) : r p = 0 := by
    apply norm_eq_zero.mp
    rw [hr]
    apply hqevent
    refine ⟨{i}, fun s hs => ?_⟩
    simp only [finiteSeminorm, hp s (hs (Finset.mem_singleton_self i)), norm_zero]
  let e₀ (i : I) : E i →+* L := {
    toFun := fun x => r (MvPolynomial.X ⟨i, x⟩)
    map_zero' := by
      exact norm_eq_zero.mp (by simpa using hX i 0)
    map_one' := by
      apply sub_eq_zero.mp
      rw [← map_one r, ← map_sub]
      apply hz i
      intro s hi
      rw [map_sub, map_one, finiteEvaluation_X K E s i hi, map_one]
      exact sub_self _
    map_add' := fun x y => by
      apply sub_eq_zero.mp
      rw [← map_add, ← map_sub]
      apply hz i
      intro s hi
      simp only [map_sub, map_add, finiteEvaluation_X K E s i hi, sub_self]
    map_mul' := fun x y => by
      apply sub_eq_zero.mp
      rw [← map_mul, ← map_sub]
      apply hz i
      intro s hi
      simp only [map_sub, map_mul, finiteEvaluation_X K E s i hi, sub_self]
  }
  let : Algebra K L := (r.comp MvPolynomial.C).toAlgebra
  let : NormedAlgebra K L := {
    norm_smul_le c x := by
      rw [Algebra.smul_def, norm_mul]
      exact le_of_eq (congrArg (· * ‖x‖) (hC c))
  }
  have hecomm (i : I) (c : K) : e₀ i (algebraMap K (E i) c) = algebraMap K L c := by
    apply sub_eq_zero.mp
    change r (MvPolynomial.X ⟨i, algebraMap K (E i) c⟩) - r (MvPolynomial.C c) = 0
    rw [← map_sub]
    apply hz i
    intro s hi
    rw [map_sub, finiteEvaluation_X K E s i hi]
    simp only [finiteEvaluation, MvPolynomial.eval₂Hom_C]
    rw [((finiteModel K E s).embedding i hi).toAlgHom.commutes, sub_self]
  let e (i : I) : BoundedAlgHom K (E i) L := {
    toRingHom := e₀ i
    commutes' := hecomm i
    bounded := ⟨1, zero_lt_one, fun x => by
      change ‖r (MvPolynomial.X ⟨i, x⟩)‖ ≤ 1 * ‖x‖
      rw [hX, one_mul]⟩
  }
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, e, fun i => ?_⟩
  exact AddMonoidHomClass.isometry_of_norm (e₀ i) (hX i)

/-- A chosen common complete ultrametric extension of the family `E`.
The field, coefficient algebra, and embeddings are chosen together. -/
def CommonFieldFamily : Type u :=
  (exists_commonFieldFamily K E).choose

namespace CommonFieldFamily

instance instNormedField : NormedField (CommonFieldFamily K E) :=
  (exists_commonFieldFamily K E).choose_spec.choose

instance instIsUltrametricDist : IsUltrametricDist (CommonFieldFamily K E) :=
  (exists_commonFieldFamily K E).choose_spec.choose_spec.choose

instance instCompleteSpace : CompleteSpace (CommonFieldFamily K E) :=
  (exists_commonFieldFamily K E).choose_spec.choose_spec.choose_spec.choose

instance instNormedAlgebra : NormedAlgebra K (CommonFieldFamily K E) :=
  (exists_commonFieldFamily K E).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The isometric coefficient-compatible inclusion of a family member. -/
def embedding (i : I) : BoundedAlgHom K (E i) (CommonFieldFamily K E) :=
  (exists_commonFieldFamily K E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose i

/-- Every chosen family inclusion is an isometry. -/
theorem isometry_embedding (i : I) : Isometry (embedding K E i) :=
  (exists_commonFieldFamily K E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec i

/-- Every chosen family inclusion preserves the norm. -/
theorem norm_embedding (i : I) (x : E i) : ‖embedding K E i x‖ = ‖x‖ :=
  (isometry_embedding K E i).norm_map_of_map_zero
    (map_zero (embedding K E i).toAlgHom) x

end CommonFieldFamily

end Langlands.Analytic.ValuedField
