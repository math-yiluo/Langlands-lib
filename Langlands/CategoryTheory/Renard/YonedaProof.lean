import Langlands.CategoryTheory.Renard.YonedaStatements

/-!
# Renard A.III.2: proof of Yoneda and the representable-presheaf equivalence

The proof uses the actual lifted Yoneda embedding, representation data and
full-subcategory inclusion, with independent value, morphism and object universes.
-/

universe w v u

open CategoryTheory Opposite

namespace Langlands.Renard.Yoneda

/-- Evaluation and its inverse action, after removing the explicit value lift. -/
theorem evaluationStatement : EvaluationStatement.{w, v, u} := by
  intro C _ F X
  refine ⟨uliftYonedaEquiv.{w}.trans Equiv.ulift, ?_, ?_⟩
  · intro θ
    rfl
  · intro x Y f
    rfl

/-- The lifted Yoneda Hom equivalence has the stated evaluation inverse. -/
theorem homEquivalenceStatement : HomEquivalenceStatement.{w, v, u} := by
  intro C _ X Y
  let e := (ULiftYoneda.fullyFaithful.{w} C).homEquiv (X := X) (Y := Y)
  refine ⟨e, fun _ => rfl, ?_⟩
  intro θ
  obtain ⟨f, rfl⟩ := e.surjective θ
  rw [e.symm_apply_apply]
  change f = 𝟙 X ≫ f
  exact (Category.id_comp f).symm

/-- Representation data and natural isomorphisms agree across value universes. -/
theorem representationDictionaryStatement :
    RepresentationDictionaryStatement.{w, v, u} := by
  intro C _ F X
  let e : F.RepresentableBy X ≃
      (uliftYoneda.{w}.obj X ≅ F ⋙ uliftFunctor.{v}) :=
    Functor.representableByUliftFunctorEquiv.symm.trans
      (Functor.RepresentableBy.equivUliftYonedaIso (F ⋙ uliftFunctor.{v}) X)
  exact e.nonempty_congr

/-- The actual lifted Yoneda functor induces the representable equivalence. -/
theorem representableEquivalenceStatement :
    RepresentableEquivalenceStatement.{w, v, u} := by
  intro C _
  let P : ObjectProperty (Cᵒᵖ ⥤ Type (max w v)) := fun F => F.IsRepresentable
  let L : C ⥤ P.FullSubcategory :=
    P.lift uliftYoneda.{w} (fun _ => inferInstance)
  let : L.EssSurj := ⟨fun F => by
    let : F.obj.IsRepresentable := F.property
    exact ⟨F.obj.reprX, ⟨P.isoMk F.obj.uliftYonedaReprXIso⟩⟩⟩
  let : L.IsEquivalence := {}
  exact ⟨L.asEquivalence, ⟨P.liftCompιIso _ _⟩⟩

/-- Renard's core Yoneda assertions, with all three independent universe levels. -/
theorem yonedaStatements : YonedaStatements.{w, v, u} :=
  ⟨evaluationStatement, homEquivalenceStatement,
    representationDictionaryStatement, representableEquivalenceStatement⟩

end Langlands.Renard.Yoneda
