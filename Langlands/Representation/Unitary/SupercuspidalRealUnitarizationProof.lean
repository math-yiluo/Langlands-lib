import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement
import Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof
import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.Group.GL.OneBlockShape
import Langlands.Representation.Classification.SupercuspidalTwist

noncomputable section

namespace Langlands

open GeneralLinear

universe uF uV

/-- Single-block transport of the actual Levi positive form. -/
theorem supercuspidalRealUnitarization :
    SupercuspidalRealUnitarizationStatement.{uF,uV} := by
  intro p _ F T
  let := T.topology
  intro n hn V _ _ ρ hirr hcusp
  let D := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  let f := D.leviEmbedding F.Carrier
  have hsurj : Function.Surjective f :=
    D.singleBlock_leviEmbedding_surjective rfl F.Carrier
  have hsingle (m : D.Levi F.Carrier) : f m = m (0 : Fin 1) := by
    apply Units.ext
    ext a b
    have ha : D.index (0 : Fin 1) a = a := Fin.ext (D.singleBlock_index_val rfl (0 : Fin 1) a)
    have hb : D.index (0 : Fin 1) b = b := Fin.ext (D.singleBlock_index_val rfl (0 : Fin 1) b)
    change (D.leviEmbedding F.Carrier m).val a b = (m (0 : Fin 1)).val a b
    exact (congrArg₂
      (fun x y : Fin n => (D.leviEmbedding F.Carrier m).val x y)
      ha.symm hb.symm).trans (D.leviEmbedding_apply_same F.Carrier m (0 : Fin 1) a b)
  have hpull : Representation.IsIrreducible (ρ.comp f) := by
    let := hirr
    let E : Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ :=
      { toFun := fun S =>
          ⟨S.toSubmodule, fun g v hv => by
            obtain ⟨m, rfl⟩ := hsurj g
            exact S.apply_mem_toSubmodule m hv⟩
        invFun := fun S =>
          ⟨S.toSubmodule, fun m v hv => S.apply_mem_toSubmodule (f m) hv⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact E.isSimpleOrder
  have hcusppull : CuspidalSupport.IsLeviCuspidal D (ρ.comp f) :=
    (CuspidalSupport.singleBlockCuspidalityClause T n D rfl V ρ).mpr hcusp
  obtain ⟨t, hunit⟩ := leviCuspidalRealUnitarization p F T n hn D V (ρ.comp f)
    hpull hcusppull
  have hchar (m : D.Levi F.Carrier) :
      T.leviRealPowerCharacter D t m =
        realPowerCharacter (T.determinantNorm n) (t (0 : Fin 1)) (f m) := by
    rw [T.leviRealPowerCharacter_apply, hsingle]
    change (∏ i : Fin 1, realPowerCharacter (T.determinantNorm n) (t i) (m i)) = _
    simp
  have htwist : T.leviRealPowerTwist D t (ρ.comp f) =
      (realPowerTwist (T.determinantNorm n) (t (0 : Fin 1)) ρ).comp f := by
    ext m v
    change (T.leviRealPowerCharacter D t m : ℂ) • ρ (f m) v =
      (realPowerCharacter (T.determinantNorm n) (t (0 : Fin 1)) (f m) : ℂ) • ρ (f m) v
    rw [hchar]
  rw [htwist] at hunit
  obtain ⟨b⟩ := hunit
  refine ⟨t (0 : Fin 1), ⟨{ toInnerProductCore := b.toInnerProductCore, invariant := ?_ }⟩⟩
  intro g v w
  obtain ⟨m, rfl⟩ := hsurj g
  exact b.invariant m v w

/-- The unitary twist as an actual supercuspidal object, with its existing
normalized real-power class. -/
theorem supercuspidalRepRealUnitarization
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    ∀ A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := n),
      ∃ t : ℝ,
        let B := SupercuspidalRep.twist (T.determinantPowerCharacter n t)
          (T.isOpen_ker_determinantPowerCharacter n t)
          (T.ker_determinant_le_ker_determinantPowerCharacter n t) A
        IsUnitarizable B.obj.representation ∧
          B.isoClass = T.supercuspidalClassRealPowerTwist n t A.isoClass := by
  let := T.topology
  intro A
  obtain ⟨t, ht⟩ := supercuspidalRealUnitarization p F T n hn A.obj
    A.obj.representation A.property.1 A.property.2
  exact ⟨t, ht, rfl⟩

end Langlands
