import Langlands.CategoryTheory.Renard.OrderedSystemLimitStatements

/-!
# Renard A.IV: universal properties of inverse and direct systems

The compatible families in the published statements are exactly the legs of
competing cones and cocones. Repackaging them gives both equivalences without
any existence or nonemptiness assumption.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Renard.OrderedSystemLimit

universe vC uC uI

/-- The inverse-system characterization, with all inputs bound internally. -/
theorem inverseLimitStatement_proof : InverseLimitStatement.{vC, uC, uI} := by
  intro C _ I _ _ D t
  constructor
  · rintro ⟨ht⟩ Y q hq
    let s : Cone D :=
      { pt := Y
        π :=
          { app := fun i => q i.unop
            naturality := by
              intro i j f
              dsimp
              rw [Category.id_comp]
              have hf : homOfLE (leOfHom f.unop) = f.unop :=
                Subsingleton.elim _ _
              simpa only [hf, Quiver.Hom.op_unop] using
                (hq j.unop i.unop (leOfHom f.unop)).symm } }
    obtain ⟨l, hl, hu⟩ := ht.existsUnique s
    refine ⟨l, fun i => hl (op i), ?_⟩
    intro m hm
    exact hu m (fun i => hm i.unop)
  · intro h
    refine ⟨IsLimit.ofExistsUnique ?_⟩
    intro s
    obtain ⟨l, hl, hu⟩ :=
      h s.pt (fun i => s.π.app (op i)) (fun i j hij => s.w (homOfLE hij).op)
    refine ⟨l, fun i => hl i.unop, ?_⟩
    intro m hm
    exact hu m (fun i => hm (op i))

/-- The direct-system characterization, with all inputs bound internally. -/
theorem directLimitStatement_proof : DirectLimitStatement.{vC, uC, uI} := by
  intro C _ I _ _ D t
  constructor
  · rintro ⟨ht⟩ Y q hq
    let s : Cocone D :=
      { pt := Y
        ι :=
          { app := q
            naturality := by
              intro i j f
              dsimp
              rw [Category.comp_id]
              have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
              simpa only [hf] using hq i j (leOfHom f) } }
    exact ht.existsUnique s
  · intro h
    refine ⟨IsColimit.ofExistsUnique ?_⟩
    intro s
    exact h s.pt s.ι.app (fun i j hij => s.w (homOfLE hij))

/-- The unchanged inverse-then-direct aggregate at three independent universes. -/
theorem orderedSystemLimitStatements_proof :
    OrderedSystemLimitStatements.{vC, uC, uI} :=
  ⟨inverseLimitStatement_proof.{vC, uC, uI},
    directLimitStatement_proof.{vC, uC, uI}⟩

end Langlands.Renard.OrderedSystemLimit
