import Langlands.CategoryTheory.Renard.ElementaryLimitColimitStatements

/-!
# Proofs of Renard A.IV elementary limit and colimit characterizations

The supplied-cone and supplied-cocone universal properties for the first
four limit examples and their four duals.
-/

universe vC uC uI

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.ElementaryLimitColimit

/-- The vertex of an empty limiting cone is terminal, and conversely. -/
theorem emptyLimitStatement : EmptyLimitStatement.{vC, uC, uI} := by
  classical
  intro C _ D t
  constructor
  · rintro ⟨ht⟩ Y
    let hT := isLimitEquivIsTerminalOfIsEmpty C t ht
    exact ⟨hT.from Y, trivial, fun m _ => hT.hom_ext m _⟩
  · intro h
    let hT : IsTerminal t.pt := IsTerminal.ofUniqueHom
      (fun Y => (h Y).choose) (fun Y m => (h Y).choose_spec.2 m trivial)
    exact ⟨(isLimitEquivIsTerminalOfIsEmpty C t).symm hT⟩

/-- A supplied kernel fork is limiting exactly when its arrow has unique factors. -/
theorem kernelStatement : KernelStatement.{vC, uC} := by
  classical
  intro C _ _ _ X Y K f i h
  constructor
  · rintro ⟨ht⟩ Z q hq
    let l := KernelFork.IsLimit.lift' ht q hq
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact Fork.IsLimit.hom_ext ht (hm.trans l.2.symm)
  · intro hU
    exact ⟨KernelFork.IsLimit.ofι i h
      (fun {Z} q hq => (hU Z q hq).choose)
      (fun {Z} q hq => (hU Z q hq).choose_spec.1)
      (fun {Z} q hq m hm => (hU Z q hq).choose_spec.2 m hm)⟩

/-- A supplied fan is limiting exactly when every family factors uniquely. -/
theorem productStatement : ProductStatement.{vC, uC, uI} := by
  classical
  intro C _ I X P p
  constructor
  · rintro ⟨ht⟩ Y q
    refine ⟨Fan.IsLimit.lift ht q, fun i => Fan.IsLimit.fac ht q i, ?_⟩
    intro m hm
    exact Fan.IsLimit.hom_ext ht m _ fun i =>
      (hm i).trans (Fan.IsLimit.fac ht q i).symm
  · intro hU
    exact ⟨Fan.IsLimit.mk (Fan.mk P p)
      (fun s => (hU s.pt s.proj).choose)
      (fun s j => (hU s.pt s.proj).choose_spec.1 j)
      (fun s m hm => (hU s.pt s.proj).choose_spec.2 m hm)⟩

/-- A supplied pullback cone is limiting exactly when compatible pairs factor uniquely. -/
theorem pullbackStatement : PullbackStatement.{vC, uC} := by
  classical
  intro C _ X Y Z P f g p q h
  constructor
  · rintro ⟨ht⟩ W a b hab
    let l := PullbackCone.IsLimit.lift' ht a b hab
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact PullbackCone.IsLimit.hom_ext ht
      (hm.1.trans l.2.1.symm) (hm.2.trans l.2.2.symm)
  · intro hU
    exact ⟨PullbackCone.IsLimit.mk h
      (fun s => (hU s.pt s.fst s.snd s.condition).choose)
      (fun s => (hU s.pt s.fst s.snd s.condition).choose_spec.1.1)
      (fun s => (hU s.pt s.fst s.snd s.condition).choose_spec.1.2)
      (fun s m hm₁ hm₂ =>
        (hU s.pt s.fst s.snd s.condition).choose_spec.2 m ⟨hm₁, hm₂⟩)⟩

/-- The vertex of an empty colimiting cocone is initial, and conversely. -/
theorem emptyColimitStatement : EmptyColimitStatement.{vC, uC, uI} := by
  classical
  intro C _ D t
  constructor
  · rintro ⟨ht⟩ Y
    let hI := isColimitEquivIsInitialOfIsEmpty C t ht
    exact ⟨hI.to Y, trivial, fun m _ => hI.hom_ext m _⟩
  · intro h
    let hI : IsInitial t.pt := IsInitial.ofUniqueHom
      (fun Y => (h Y).choose) (fun Y m => (h Y).choose_spec.2 m trivial)
    exact ⟨(isColimitEquivIsInitialOfIsEmpty C t).symm hI⟩

/-- A supplied cokernel cofork is colimiting exactly when its arrow has unique factors. -/
theorem cokernelStatement : CokernelStatement.{vC, uC} := by
  classical
  intro C _ _ _ X Y Q f p h
  constructor
  · rintro ⟨ht⟩ Z q hq
    let l := CokernelCofork.IsColimit.desc' ht q hq
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact Cofork.IsColimit.hom_ext ht (hm.trans l.2.symm)
  · intro hU
    exact ⟨CokernelCofork.IsColimit.ofπ p h
      (fun {Z} q hq => (hU Z q hq).choose)
      (fun {Z} q hq => (hU Z q hq).choose_spec.1)
      (fun {Z} q hq m hm => (hU Z q hq).choose_spec.2 m hm)⟩

/-- A supplied cofan is colimiting exactly when every family factors uniquely. -/
theorem coproductStatement : CoproductStatement.{vC, uC, uI} := by
  classical
  intro C _ I X P p
  constructor
  · rintro ⟨ht⟩ Y q
    refine ⟨Cofan.IsColimit.desc ht q, fun i => Cofan.IsColimit.fac ht q i, ?_⟩
    intro m hm
    exact Cofan.IsColimit.hom_ext ht m _ fun i =>
      (hm i).trans (Cofan.IsColimit.fac ht q i).symm
  · intro hU
    exact ⟨Cofan.IsColimit.mk (Cofan.mk P p)
      (fun s => (hU s.pt s.inj).choose)
      (fun s j => (hU s.pt s.inj).choose_spec.1 j)
      (fun s m hm => (hU s.pt s.inj).choose_spec.2 m hm)⟩

/-- A supplied pushout cocone is colimiting exactly when compatible pairs factor uniquely. -/
theorem pushoutStatement : PushoutStatement.{vC, uC} := by
  classical
  intro C _ X Y Z P f g p q h
  constructor
  · rintro ⟨ht⟩ W a b hab
    let l := PushoutCocone.IsColimit.desc' ht a b hab
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact PushoutCocone.IsColimit.hom_ext ht
      (hm.1.trans l.2.1.symm) (hm.2.trans l.2.2.symm)
  · intro hU
    exact ⟨PushoutCocone.IsColimit.mk h
      (fun s => (hU s.pt s.inl s.inr s.condition).choose)
      (fun s => (hU s.pt s.inl s.inr s.condition).choose_spec.1.1)
      (fun s => (hU s.pt s.inl s.inr s.condition).choose_spec.1.2)
      (fun s m hm₁ hm₂ =>
        (hU s.pt s.inl s.inr s.condition).choose_spec.2 m ⟨hm₁, hm₂⟩)⟩

/-- The eight elementary characterizations, in their published order. -/
theorem elementaryLimitColimitStatements :
    ElementaryLimitColimitStatements.{vC, uC, uI} :=
  ⟨emptyLimitStatement, kernelStatement, productStatement, pullbackStatement,
    emptyColimitStatement, cokernelStatement, coproductStatement, pushoutStatement⟩

end Langlands.Renard.ElementaryLimitColimit
