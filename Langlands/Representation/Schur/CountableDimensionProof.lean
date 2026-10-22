import Langlands.Representation.Schur.CountableDimensionStatement
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent

namespace Langlands

private theorem commute_subfield_closure {D : Type*} [DivisionRing D]
    {s : Set D} (hs : ∀ x ∈ s, ∀ y ∈ s, Commute x y)
    {x y : D} (hx : x ∈ Subfield.closure s) (hy : y ∈ Subfield.closure s) :
    Commute x y := by
  have gen (a : D) (ha : a ∈ s) : Commute a y := by
    induction hy using Subfield.closure_induction with
    | mem b hb => exact hs a ha b hb
    | one => exact Commute.one_right a
    | add b c hb hc ihb ihc => exact ihb.add_right ihc
    | neg b hb ih => exact ih.neg_right
    | inv b hb ih => exact ih.inv_right₀
    | mul b c hb hc ihb ihc => exact ihb.mul_right ihc
  induction hx using Subfield.closure_induction with
  | mem a ha => exact gen a ha
  | one => exact Commute.one_left y
  | add a b ha hb iha ihb => exact iha.add_left ihb
  | neg a ha ih => exact ih.neg_left
  | inv a ha ih => exact ih.inv_left₀
  | mul a b ha hb iha ihb => exact iha.mul_left ihb

private theorem countableDivisionAlgebra_algebraic
    {D V : Type*} [DivisionRing D] [Algebra ℂ D]
    [AddCommGroup V] [Module ℂ V]
    (ev : D →ₗ[ℂ] V) (hev : Function.Injective ev)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (x : D) : IsAlgebraic ℂ x := by
  classical
  by_contra hx
  let s : Set D := Set.range (algebraMap ℂ D) ∪ {x}
  let E := Subfield.closure s
  have hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b := by
    rintro a (⟨c, rfl⟩ | rfl) b (⟨d, rfl⟩ | rfl)
    · exact Algebra.commute_algebraMap_left c _
    · exact Algebra.commute_algebraMap_left c _
    · exact Algebra.commute_algebraMap_right d _
    · exact Commute.refl _
  let : Field E := { E.toDivisionRing with
    mul_comm := fun a b => Subtype.ext (commute_subfield_closure hs a.property b.property).eq }
  let scalar : ℂ →+* E :=
    (algebraMap ℂ D).codRestrict E.toSubring
      (fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩))
  let : Algebra ℂ E := scalar.toAlgebra
  let incl : E →ₐ[ℂ] D :=
    { E.subtype with commutes' := fun _ => rfl }
  let xE : E := ⟨x, Subfield.subset_closure (Or.inr rfl)⟩
  have hxE : Transcendental ℂ xE := by
    intro h
    exact hx ((isAlgebraic_algHom_iff incl Subtype.val_injective).2 h)
  have hli := hxE.linearIndependent_sub_inv.map' (ev.comp incl.toLinearMap)
    (LinearMap.ker_eq_bot.mpr (hev.comp Subtype.val_injective))
  have hcard := hli.cardinal_lift_le_rank
  have hbound : Cardinal.lift.{_} (Cardinal.mk ℂ) ≤ Cardinal.aleph0 :=
    hcard.trans (by simpa using hrank)
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) (by simpa using hbound)

universe uG uV

/-- Schur's lemma for irreducible complex representations of countable algebraic dimension. -/
theorem countableDimensionalSchur
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    CountableDimensionalSchurStatement (G := G) (V := V) := by
  classical
  intro rho hrank hirr f
  let : rho.IsIrreducible := hirr
  let : Nontrivial rho.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : rho.asModule)
  let D := Module.End (MonoidAlgebra ℂ G) rho.asModule
  let ev : D →ₗ[ℂ] V :=
    { toFun := fun a => rho.asModuleEquiv (a v)
      map_add' := fun a b => rho.asModuleEquiv.map_add (a v) (b v)
      map_smul' := fun c a => rho.asModuleEquiv.map_smul c (a v) }
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra h
    have hz : (a - b) v = 0 :=
      sub_eq_zero.mpr (rho.asModuleEquiv.injective hab)
    exact hv (LinearMap.injective_of_ne_zero (sub_ne_zero.mpr h)
      (hz.trans (map_zero (a - b)).symm))
  let : Algebra.IsIntegral ℂ D :=
    ⟨fun x => (countableDivisionAlgebra_algebraic ev hev hrank x).isIntegral⟩
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := D)
  let e := Representation.IntertwiningMap.equivAlgEnd (ρ := rho)
  have scalar (c : ℂ) : e (c • Representation.IntertwiningMap.id rho) =
      algebraMap ℂ D c := e.commutes c
  obtain ⟨c, hc⟩ := hbij.2 (e f)
  refine ⟨c, e.injective ((scalar c).trans hc).symm, ?_⟩
  intro d hd
  apply hbij.1
  calc
    algebraMap ℂ D d = e (d • Representation.IntertwiningMap.id rho) := (scalar d).symm
    _ = e f := congrArg e hd.symm
    _ = algebraMap ℂ D c := hc.symm

end Langlands
