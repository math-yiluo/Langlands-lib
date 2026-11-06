import Langlands.Correspondence.AssemblyLFactorStatement

/-!
# Pointwise use of supercuspidal extension

Supporting helper material for assembly characterization: uniqueness of the
zero-monodromy class makes the existential extension predicate pointwise.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Forgetting the rank and parameter properties does not identify additional
isomorphism classes. -/
theorem parameterForget_injective {n : ℕ+} :
    Function.Injective (parameterForget F (n := n) :
      WeilDeligneClass.{uF, uP} F n → _) := by
  intro D E h
  apply Subtype.ext
  have hinj : Function.Injective
      (WeilDeligneRepresentation.frobeniusSemisimpleClassForget.{uF, uP}
        (ν := (Weil.Local.localNormCharacter F).toMonoidHom)
        (Weil.Local.localInertia F) (Weil.Local.localDegree F)) := by
    intro A B
    refine Quotient.inductionOn₂ A B ?_
    intro A B hAB
    change WeilDeligneRepresentation.classOf A.val =
      WeilDeligneRepresentation.classOf B.val at hAB
    exact Quotient.sound ((WeilDeligneRepresentation.classOf_eq_iff _ _).mp hAB)
  exact hinj h

/-- A fixed irreducible Weil class has at most one zero-monodromy parameter
class of the specified rank. -/
theorem IsZeroMonodromyOf.unique {n : ℕ+}
    {σ : IrreducibleWeilClass.{uF, uP} F n}
    {D E : WeilDeligneClass.{uF, uP} F n}
    (hD : IsZeroMonodromyOf F σ D) (hE : IsZeroMonodromyOf F σ E) : D = E := by
  obtain ⟨A, hA, hAD⟩ := hD
  obtain ⟨B, hB, hBE⟩ := hE
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A B).mp (hA.trans hB.symm)
  have hAB : WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy
          (Weil.Local.localNormCharacter F).toMonoidHom A) =
      WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy
          (Weil.Local.localNormCharacter F).toMonoidHom B) := by
    apply (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr
    refine ⟨⟨e, ?_⟩⟩
    ext x
    change e.toLinearMap 0 = 0
    exact map_zero _
  exact parameterForget_injective (hAD.symm.trans (hAB.trans hBE))

/-- An existential supercuspidal extension agrees with the supercuspidal map
on every supplied zero-monodromy parameter class. -/
theorem ExtendsSupercuspidal.apply_of_zeroMonodromy
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc : ExtendsSupercuspidal F c0 c) {n : ℕ+}
    {σ : IrreducibleWeilClass.{uF, uP} F n}
    {D : WeilDeligneClass.{uF, uP} F n} (hD : IsZeroMonodromyOf F σ D) :
    c n D = supercuspidalToAutomorphic F (c0 n σ) := by
  obtain ⟨E, hE, hcE⟩ := hc n σ
  simpa only [hE.unique hD] using hcE

/-- Two extensions of the same supercuspidal map agree on every irreducible
Weil parameter class. -/
theorem ExtendsSupercuspidal.eq_on_irreducible
    {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c d : FullMap.{uF, uP, uA} F}
    (hc : ExtendsSupercuspidal F c0 c) (hd : ExtendsSupercuspidal F c0 d)
    {n : ℕ+} {D : WeilDeligneClass.{uF, uP} F n}
    (hD : IsIrreducibleWeilParameter F D) : c n D = d n D := by
  obtain ⟨σ, hσ⟩ := hD
  exact (hc.apply_of_zeroMonodromy hσ).trans
    (hd.apply_of_zeroMonodromy hσ).symm

end Langlands.Correspondence
