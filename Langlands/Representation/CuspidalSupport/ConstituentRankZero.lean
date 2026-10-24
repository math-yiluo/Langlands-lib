import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! Elementary rank-zero helper for the constituent theorem. -/

noncomputable section

namespace Langlands.CuspidalSupport

open CategoryTheory

universe uG uF uV

private def trivialGroupHom {G : Type uG} [Group G] [TopologicalSpace G]
    [Subsingleton G] {A D : SmoothRep.{0, uG, uV} ℂ G}
    (f : A →ₗ[ℂ] D) : A ⟶ D :=
  SmoothRep.ofHom {
    toLinearMap := f
    isIntertwining' g := by
      rw [Subsingleton.elim g 1, map_one, map_one]
      rfl }

/-- For a trivial group, every actual subquotient is both a subrepresentation
and a quotient. No finite-dimensionality or irreducibility is needed. -/
theorem constituent_of_subsingleton_group {G : Type uG} [Group G]
    [TopologicalSpace G] [Subsingleton G]
    {A D : SmoothRep.{0, uG, uV} ℂ G} (h : SmoothRep.IsSubquotient D A) :
    SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A := by
  obtain ⟨S, T, ⟨e⟩⟩ := h
  let E := SmoothRep.subrepresentation A S
  let Q := SmoothRep.subquotient A S T
  let j : E →ₗ[ℂ] A := (SmoothRep.hom (SmoothRep.subtype A S)).toLinearMap
  let q : E →ₗ[ℂ] Q := (SmoothRep.hom (SmoothRep.mkQ E T)).toLinearMap
  let d : D ≃ₗ[ℂ] Q := (SmoothRep.equivOfIso e).toLinearEquiv
  have hj : Function.Injective j := SmoothRep.subtype_injective A S
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective E T
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hr' : Function.LeftInverse r j := fun v =>
    congrArg (fun f : E →ₗ[ℂ] E => f v) hr
  have hs' : Function.LeftInverse q s := fun v =>
    congrArg (fun f : Q →ₗ[ℂ] Q => f v) hs
  constructor
  · exact ⟨trivialGroupHom (j.comp (s.comp d.toLinearMap)),
      hj.comp (hs'.injective.comp d.injective)⟩
  · exact ⟨trivialGroupHom (d.symm.toLinearMap.comp (q.comp r)),
      d.symm.surjective.comp (hq.comp hr'.surjective)⟩

/-- The parameterized published target also holds for total rank zero. -/
theorem leviCuspidalConstituent_rankZero {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape 0) :
    LeviCuspidalConstituentTheorem.{uF, uV} F T B := by
  let := T.topology
  let : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let : Subsingleton (B.Levi F.Carrier) := inferInstance
  intro A D _ _ _ h
  exact constituent_of_subsingleton_group h

end Langlands.CuspidalSupport
