import Langlands.Representation.CuspidalSupport.JacquetInductionStatement

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV uR uG

private theorem rankZero_empty (B : BlockShape 0) : IsEmpty (Fin B.length) :=
  ⟨fun i => Fin.elim0 (B.index i ⟨0, B.positive i⟩)⟩

private theorem rankZero_levi_subsingleton (F : Type uF) [Field F]
    (B : BlockShape 0) : Subsingleton (B.Levi F) := by
  let := rankZero_empty B
  infer_instance

private theorem rankZero_quasicuspidal (F : Type uF) [Field F]
    (B : BlockShape 0) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) : IsLeviQuasicuspidal B ρ := by
  let := rankZero_levi_subsingleton F B
  intro S hS
  exact (hS (Subsingleton.elim _ _)).elim

private def rankZero_minimal (F : Type uF) [Field F] (B C : BlockShape 0) :
    MinimalConjugatingPermutations (F := F) B C := by
  refine ⟨⟨1, ?_, ?_⟩, ?_⟩
  · intro i a b h
    exact Fin.elim0 (B.index i a)
  · intro i a b h
    exact Fin.elim0 (C.index i a)
  · exact Subsingleton.elim _ _

private def subsingletonInducedEquiv
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Subsingleton G]
    (P : Subgroup G) {V : Type uV} [AddCommGroup V] [Module R V]
    (σ : Representation R P V) : Induction.SmoothFunctions P σ ≃ₗ[R] V where
  toFun f := Induction.eval P σ f 1
  invFun v := Induction.smoothFunctionOf P σ (fun _ => v)
    (by intro p x; have hp : p = 1 := Subsingleton.elim _ _; simp [hp])
    ⊤ (by intros; rfl)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrArg (Induction.eval P σ f) (Subsingleton.elim _ _)
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def subsingletonCoinvariantsEquiv
    {R : Type uR} [CommRing R] {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (N : Subgroup G) : Jacquet.Coinvariants ρ N ≃ₗ[R] V := by
  let f := Jacquet.lift ρ N (LinearMap.id : V →ₗ[R] V)
    (by intro g; have hg : (g : G) = 1 := Subsingleton.elim _ _; ext v; simp [hg])
  exact {
    toLinearMap := f
    invFun := Jacquet.mk ρ N
    left_inv := by
      intro v
      obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N v
      rfl
    right_inv := by intro v; rfl }

private def oneStepFiltration {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    (A : Rep.{uV} R G) : ObjectRepFiltration A 1 :=
  ObjectRepFiltration.ofSubrepresentations
    (fun i => if i = 0 then ⊥ else ⊤)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by simp) (by simp)

private def oneStepGradedEquiv {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    (A : Rep.{uV} R G) (i : Fin 1) :
    ((oneStepFiltration A).gradedRepresentation i).ρ.Equiv A.ρ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let q : Submodule R (⊤ : Submodule R A) :=
    (⊥ : Submodule R A).comap (⊤ : Subrepresentation A.ρ).toSubmodule.subtype
  have hq : q = ⊥ := by
    ext v
    change (v.val = 0) ↔ v = 0
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine Representation.Equiv.mk
    ((q.quotEquivOfEqBot hq).trans Submodule.topEquiv) ?_
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := (oneStepFiltration A).gradedProjection_surjective 0 v
  rfl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- At rank zero, evaluation and the trivial coinvariant quotient identify
Jacquet-of-induction with the transported inducing representation. -/
def rankZero_jacquetInductionEquiv (B C : BlockShape 0)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin 0)) (hw : ConjugatesLevi (F := F.Carrier) B C w) :
    letI := T.topology
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    A.representation.Equiv (transport B C w hw ρ.representation) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := rankZero_levi_subsingleton F.Carrier C
  refine Representation.Equiv.mk
    ((subsingletonCoinvariantsEquiv _ _).trans (subsingletonInducedEquiv _ _)) ?_
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  ext v
  simp [hg]

/-- The associated Jacquet filtration theorem at rank zero, with one factor
indexed by its unique minimal conjugating permutation. -/
theorem associatedJacquetFiltration_rankZero :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T 0 := by
  let := T.topology
  intro B C ρ _ _
  let A := (T.normalizedJacquetFunctor C).obj
    ((T.normalizedParabolicInductionFunctor B).obj ρ)
  refine ⟨rankZero_quasicuspidal F.Carrier C A.representation, ?_⟩
  let : Unique (MinimalConjugatingPermutations (F := F.Carrier) B C) :=
    { default := rankZero_minimal F.Carrier B C
      uniq := fun _ => Subsingleton.elim _ _ }
  let e : Fin 1 ≃ MinimalConjugatingPermutations (F := F.Carrier) B C :=
    Equiv.ofUnique _ _
  refine ⟨1, e, oneStepFiltration (Rep.of A.representation), ?_⟩
  intro i
  exact ⟨(oneStepGradedEquiv (Rep.of A.representation) i).trans
    (rankZero_jacquetInductionEquiv F T B C ρ (e i).val.val (e i).property)⟩

end Langlands.CuspidalSupport
