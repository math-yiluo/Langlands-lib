import Langlands.BaseChange.TwistedCharacter.EquivariantLine
import Langlands.BaseChange.TwistedCharacter.LinearIndependence

/-! # Restriction of visible twisted characters to a fixed Hecke corner -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis Hecke MeasureTheory

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (θ : G ≃* G)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- If a representation has zero fixed space, its twisted distribution vanishes on
the corresponding Hecke corner, for every supplied endomorphism. -/
theorem twistedDistribution_eq_zero_on_biInvariant_of_fixedVectors_eq_bot
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (hπ : IsAdmissible π) (hfix : fixedVectors π K.toSubgroup = ⊥) (A : Module.End ℂ V)
    (f : TestFunction.biInvariant K.toSubgroup K.toSubgroup) :
    twistedDistribution μ π hπ A f.val = 0 := by
  have h0 : Hecke.integratedAction μ π hπ.1 f.val = 0 := by
    ext v
    have hv := Hecke.integratedAction_mem_fixedVectors μ π hπ.1 f.property v
    rw [hfix, Submodule.mem_bot] at hv
    exact hv
  rw [twistedDistribution_apply]
  have h : Character.finiteRankIntegratedAction μ π hπ f.val = 0 := by
    apply Subtype.ext
    exact h0
  rw [h]
  exact (FiniteRankEnd.trace : _ →ₗ[ℂ] ℂ).map_zero

include hK in
/-- Every test has the same twisted traces as some bi-invariant test on a finite
family of visible pairs. Equivalent representations are allowed in the family. -/
theorem exists_biInvariant_test_same_twisted_traces
    (hθK : ∀ k ∈ K, θ.symm k ∈ K)
    {I : Type uI} [Finite I] {V : I → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ G (V i)) (hπ : ∀ i, IsAdmissible (π i))
    (hirr : ∀ i, (π i).IsIrreducible) (hfix : ∀ i, fixedVectors (π i) K.toSubgroup ≠ ⊥)
    (A : ∀ i, (π i).Equiv ((π i).comp θ.toMonoidHom)) (f : SchwartzBruhat G) :
    ∃ g : TestFunction.biInvariant K.toSubgroup K.toSubgroup, ∀ i,
      twistedDistribution μ (π i) (hπ i) (A i).toLinearMap g.val =
        twistedDistribution μ (π i) (hπ i) (A i).toLinearMap f := by
  classical
  let R : Setoid I := {
    r i j := Nonempty ((π i).Equiv (π j))
    iseqv := ⟨fun i => ⟨Representation.Equiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩ }
  let : Fintype (Quotient R) := Fintype.ofFinite _
  have hdist : Pairwise fun i j : Quotient R => ¬ Nonempty ((π i.out).Equiv (π j.out)) := by
    intro i j hne he
    apply hne
    exact (Quotient.out_eq i).symm.trans ((Quotient.sound he).trans (Quotient.out_eq j))
  obtain ⟨g, hg⟩ := exists_twistedDistribution_corner_values μ θ K hK hθK
    (fun i : Quotient R => π i.out) (fun i => hπ i.out) (fun i => hirr i.out) hdist
    (fun i => hfix i.out) (fun i => (A i.out).toLinearMap)
    (fun i a => (A i.out).isIntertwining' a) (fun i => (A i.out).injective)
    (fun i => twistedDistribution μ (π i.out) (hπ i.out) (A i.out).toLinearMap f)
  refine ⟨HeckeAlgebra.Corner.toBiInvariant μ K hK g, fun i => ?_⟩
  let j : Quotient R := Quotient.mk R i
  obtain ⟨e⟩ : Nonempty ((π j.out).Equiv (π i)) :=
    Quotient.exact (Quotient.out_eq j)
  obtain ⟨a, ha⟩ := exists_twistedDistribution_eq_smul_of_equiv μ θ
    (hπ j.out) (hirr j.out) (hπ i) e (A j.out) (A i)
  rw [ha, LinearMap.smul_apply, LinearMap.smul_apply]
  exact congrArg (a • ·) (hg j)

/-- The linear span of visible twisted distributions injects into the dual of the
bi-invariant test space. The generating distributions may live on any carriers
in the specified common universe. -/
def HeckeCornerRestrictionStatement : Prop :=
  IsCompact (K : Set G) → (∀ k ∈ K, θ.symm k ∈ K) →
    ∀ (S : Set (Distribution G)),
      (∀ d ∈ S, ∃ (V : Type uV) (iAdd : AddCommGroup V),
        letI := iAdd
        ∃ (iMod : Module ℂ V),
          letI := iMod
          ∃ (π : Representation ℂ G V) (hπ : IsAdmissible π)
            (A : π.Equiv (π.comp θ.toMonoidHom)),
            π.IsIrreducible ∧ fixedVectors π K.toSubgroup ≠ ⊥ ∧
              d = twistedDistribution μ π hπ A.toLinearMap) →
      Function.Injective ((Module.Dual.transpose (R := ℂ)
        (TestFunction.biInvariant K.toSubgroup K.toSubgroup).subtype).comp
          (Submodule.span ℂ S).subtype)

theorem injective_restrict_biInvariant_on_visible_span :
    HeckeCornerRestrictionStatement.{uG,uV} μ θ K := by
  classical
  intro hK hθK S hS
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  obtain ⟨s, hs, hxS⟩ := Submodule.mem_span_finite_of_mem_span x.property
  choose V iAdd iMod π hπ A hirr hfix hd using fun j : s => hS j.val (hs j.property)
  obtain ⟨g, hg⟩ := exists_biInvariant_test_same_twisted_traces μ θ K hK hθK π hπ hirr hfix A f
  have he : Set.EqOn (Module.Dual.eval ℂ (SchwartzBruhat G) g.val)
      (Module.Dual.eval ℂ (SchwartzBruhat G) f) (s : Set (Distribution G)) := by
    intro d hd'
    change d g.val = d f
    have hdj : d = _ := hd ⟨d, hd'⟩
    rw [hdj]
    exact hg ⟨d, hd'⟩
  have hzero := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) g
  exact (LinearMap.eqOn_span he hxS).symm.trans hzero

end Langlands.BaseChange
