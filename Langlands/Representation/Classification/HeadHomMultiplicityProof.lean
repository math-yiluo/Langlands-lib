import Langlands.Representation.Classification.HeadHomMultiplicityStatement
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Length

/-! Algebraic head/Hom multiplicity bridge. -/

noncomputable section

namespace Langlands.Classification

open scoped MonoidAlgebra

attribute [local instance] Classical.propDecidable

universe uG uU uV uW uZ

section Hom

variable {G : Type uG} [Group G]
  {U : Type uU} {V : Type uV} {W : Type uW} {Z : Type uZ}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ G U} {σ : Representation ℂ G V}
  {γ : Representation ℂ G W} {τ : Representation ℂ G Z}

private def homPrecomp (f : ρ.IntertwiningMap σ) :
    (σ.IntertwiningMap τ) →ₗ[ℂ] (ρ.IntertwiningMap τ) where
  toFun g := g.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

private def homPrecompEquiv (e : ρ.Equiv σ) :
    (σ.IntertwiningMap τ) ≃ₗ[ℂ] (ρ.IntertwiningMap τ) where
  __ := homPrecomp e.toIntertwiningMap
  invFun f := f.comp e.symm.toIntertwiningMap
  left_inv f := by
    ext x
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  right_inv f := by
    ext x
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]

private theorem hom_of_subsingleton [Subsingleton U] :
    FiniteDimensional ℂ (ρ.IntertwiningMap τ) ∧
      Module.finrank ℂ (ρ.IntertwiningMap τ) = 0 := by
  let : Subsingleton (ρ.IntertwiningMap τ) :=
    ⟨fun f g => by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]⟩
  exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩

private theorem homPrecomp_injective (q : σ.IntertwiningMap γ)
    (hq : Function.Surjective q) :
    Function.Injective (homPrecomp (τ := τ) q) := by
  intro f g h
  ext y
  obtain ⟨x, rfl⟩ := hq y
  exact congrArg (fun t : σ.IntertwiningMap τ => t x) h

private theorem homPrecomp_exact (i : ρ.IntertwiningMap σ)
    (q : σ.IntertwiningMap γ) (hq : Function.Surjective q)
    (hex : Function.Exact i q) :
    Function.Exact (homPrecomp (τ := τ) q) (homPrecomp i) := by
  intro f
  constructor
  · intro hf
    let qM := Representation.IntertwiningMap.equivLinearMapAsModule σ γ q
    let fM := Representation.IntertwiningMap.equivLinearMapAsModule σ τ f
    have hqM : Function.Surjective qM := hq
    have hker : LinearMap.ker qM ≤ LinearMap.ker fM := by
      intro x hx
      obtain ⟨y, hy⟩ := (hex x).mp hx
      change f x = 0
      rw [← hy]
      exact congrArg (fun t : ρ.IntertwiningMap τ => t y) hf
    let gM := ((LinearMap.ker qM).liftQ fM hker).comp
      (qM.quotKerEquivOfSurjective hqM).symm.toLinearMap
    refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule γ τ).symm gM, ?_⟩
    ext x
    change ((LinearMap.ker qM).liftQ fM hker)
      ((qM.quotKerEquivOfSurjective hqM).symm (qM x)) = f x
    erw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  · rintro ⟨g, rfl⟩
    ext x
    have hqi : q (i x) = 0 := (hex (i x)).mpr ⟨x, rfl⟩
    change g (q (i x)) = 0
    rw [hqi, map_zero]

private theorem homPrecomp_surjective (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i)
    (hσ : Representation.IsSemisimpleRepresentation σ) :
    Function.Surjective (homPrecomp (τ := τ) i) := by
  let : IsSemisimpleModule ℂ[G] σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hσ
  intro f
  let iM := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ i
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ f
  obtain ⟨g, hg⟩ := IsSemisimpleModule.extension_property iM hi fM
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule σ τ).symm g, ?_⟩
  ext x
  exact congrArg (fun t : ρ.asModule →ₗ[ℂ[G]] τ.asModule => t x) hg

private theorem hom_finite_add (i : ρ.IntertwiningMap σ)
    (q : σ.IntertwiningMap γ) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q)
    (hσ : Representation.IsSemisimpleRepresentation σ)
    (hρ : FiniteDimensional ℂ (ρ.IntertwiningMap τ))
    (hγ : FiniteDimensional ℂ (γ.IntertwiningMap τ)) :
    FiniteDimensional ℂ (σ.IntertwiningMap τ) ∧
      Module.finrank ℂ (σ.IntertwiningMap τ) =
        Module.finrank ℂ (ρ.IntertwiningMap τ) +
          Module.finrank ℂ (γ.IntertwiningMap τ) := by
  let := hρ
  let := hγ
  have he := homPrecomp_exact (τ := τ) i q hq hex
  have hs := homPrecomp_surjective (τ := τ) i hi hσ
  have hj := homPrecomp_injective (τ := τ) q hq
  let : Module.Finite ℂ (σ.IntertwiningMap τ) := Module.Finite.of_exact he hs
  refine ⟨inferInstance, ?_⟩
  have h := Module.length_eq_add_of_exact
    (homPrecomp (τ := τ) q) (homPrecomp i) hj hs he
  simp only [Module.length_eq_finrank] at h
  exact_mod_cast h.trans (add_comm _ _)

end Hom

section Simple

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U : Type uU} {Z : Type uZ}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ G U} {τ : Representation ℂ G Z}

private theorem simple_hom (hρ : Representation.IsIrreducible ρ)
    (hτ : Representation.IsIrreducible τ) (ha : IsAdmissible τ) :
    FiniteDimensional ℂ (ρ.IntertwiningMap τ) ∧
      Module.finrank ℂ (ρ.IntertwiningMap τ) =
        if Nonempty (ρ.Equiv τ) then 1 else 0 := by
  classical
  let := hρ
  let := hτ
  by_cases he : Nonempty (ρ.Equiv τ)
  · obtain ⟨e⟩ := he
    obtain ⟨L⟩ := admissibleSchur_homEquiv ρ
      (isAdmissible_of_equiv e.symm ha) hρ τ e
    refine ⟨(Module.Finite.equiv_iff L).mpr inferInstance, ?_⟩
    rw [ite_eq_left (show Nonempty (ρ.Equiv τ) from ⟨e⟩), L.finrank_eq]
    exact Module.finrank_self ℂ
  · let : IsEmpty (ρ.Equiv τ) := ⟨fun e => he ⟨e⟩⟩
    exact ⟨inferInstance, by rw [ite_eq_right he]; exact Module.finrank_zero_of_subsingleton⟩

end Simple

section Filtration

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : Rep.{uV} ℂ G} {τ : Rep.{uW} ℂ G}

omit [TopologicalSpace G] in
private theorem semisimple_subrepresentation
    (hA : Representation.IsSemisimpleRepresentation A.ρ) (S : Subrepresentation A.ρ) :
    Representation.IsSemisimpleRepresentation S.toRepresentation := by
  let : IsSemisimpleModule ℂ[G] A.ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hA
  let i : S.toRepresentation.IntertwiningMap A.ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (IsSemisimpleModule.of_injective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ i)
      (Submodule.injective_subtype _))

omit [TopologicalSpace G] in
private theorem filtration_hom_step {n : ℕ} (s : ObjectRepFiltration A n)
    (i : Fin n) (hA : Representation.IsSemisimpleRepresentation A.ρ)
    (hl : FiniteDimensional ℂ
      ((s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap τ.ρ))
    (hg : FiniteDimensional ℂ
      ((s.gradedRepresentation i).ρ.IntertwiningMap τ.ρ)) :
    FiniteDimensional ℂ
      ((s.subrepresentation i.succ).toRepresentation.IntertwiningMap τ.ρ) ∧
      Module.finrank ℂ
        ((s.subrepresentation i.succ).toRepresentation.IntertwiningMap τ.ρ) =
      Module.finrank ℂ
        ((s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap τ.ρ) +
      Module.finrank ℂ ((s.gradedRepresentation i).ρ.IntertwiningMap τ.ρ) := by
  have hle : s.subrepresentation i.castSucc ≤ s.subrepresentation i.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ i)
  let f : (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
      (s.subrepresentation i.succ).toRepresentation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' := fun _ => rfl }
  let q := (s.gradedProjection i).hom
  refine hom_finite_add f q (Submodule.inclusion_injective hle)
    (s.gradedProjection_surjective i) ?_
    (semisimple_subrepresentation hA _) hl hg
  intro ⟨v, hv⟩
  constructor
  · intro hq
    change Submodule.Quotient.mk _ = 0 at hq
    have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨⟨v, hq'⟩, rfl⟩
  · rintro ⟨⟨w, hw⟩, hwv⟩
    have hvw : v = w := (congrArg Subtype.val hwv).symm
    subst hvw
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw

private theorem filtration_hom {n : ℕ} (s : ObjectRepFiltration A n)
    (hs : s.HasSimpleFactors) (hA : Representation.IsSemisimpleRepresentation A.ρ)
    (ha : IsAdmissible τ.ρ) (hi : Representation.IsIrreducible τ.ρ) :
    FiniteDimensional ℂ (A.ρ.IntertwiningMap τ.ρ) ∧
      Module.finrank ℂ (A.ρ.IntertwiningMap τ.ρ) =
        ∑ i : Fin n, if Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.ρ) then 1 else 0 := by
  classical
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      FiniteDimensional ℂ
        ((s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation.IntertwiningMap τ.ρ) ∧
      Module.finrank ℂ
        ((s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation.IntertwiningMap τ.ρ) =
        ∑ i : Fin j, if Nonempty ((s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ.Equiv τ.ρ) then 1 else 0 := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [show s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ from s.subrepresentation_zero]
      let : Subsingleton (⊥ : Subrepresentation A.ρ).toSubmodule :=
        ⟨fun x y => Subtype.ext <| (show (x : A) = 0 from x.property).trans
          (show (y : A) = 0 from y.property).symm⟩
      simpa using (hom_of_subsingleton
        (ρ := (⊥ : Subrepresentation A.ρ).toRepresentation) (τ := τ.ρ))
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      obtain ⟨hf, hr⟩ := ih hjn.le
      obtain ⟨hg, hgr⟩ := simple_hom (hs ⟨j, hjn⟩) hi ha
      obtain ⟨hf', hr'⟩ := filtration_hom_step s ⟨j, hjn⟩ hA hf hg
      refine ⟨hf', ?_⟩
      rw [Fin.sum_univ_castSucc]
      exact hr'.trans (by erw [hr, hgr]; rfl)
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last] at h
  let e : (⊤ : Subrepresentation A.ρ).toRepresentation.Equiv A.ρ :=
    { toLinearMap := (⊤ : Subrepresentation A.ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let L := homPrecompEquiv (τ := τ.ρ) e
  refine ⟨(Module.Finite.equiv_iff L).mpr h.1, ?_⟩
  exact L.finrank_eq.trans h.2

end Filtration

/-- Finite-length semisimple multiplicity is the dimension of actual intertwiners
to an admissible irreducible target. -/
theorem semisimpleHomMultiplicity :
    SemisimpleHomMultiplicityStatement.{uG, uV, uW} := by
  intro G _ _ A τ hfin hA ha hi
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
  obtain ⟨s, hs⟩ := LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries
    (A := A) c h₀ h₁
  obtain ⟨hf, hr⟩ := filtration_hom s hs hA ha hi
  refine ⟨hf, c.length, s, hs, ?_⟩
  rw [hr]
  simp [ObjectRepFiltration.factorMultiplicity, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.sum_boole]

/-- The actual head universal property transports the semisimple-source count
to the intertwiner space of the original finite-length representation. -/
theorem headHomMultiplicity :
    HeadHomMultiplicityStatement.{uG, uV, uW} := by
  intro G _ _ A τ hfin ha hi
  obtain ⟨hf, hm⟩ := semisimpleHomMultiplicity G (Rep.of (head A.ρ)) τ
    (isFiniteLength_head hfin) (isSemisimpleRepresentation_head hfin) ha hi
  have hτ := isSemisimpleRepresentation_of_isIrreducible hi
  let L : ((head A.ρ).IntertwiningMap τ.ρ) ≃ₗ[ℂ] (A.ρ.IntertwiningMap τ.ρ) :=
    LinearEquiv.ofBijective (homPrecomp (toHead A.ρ))
      ⟨homPrecomp_injective (toHead A.ρ) (toHead_surjective A.ρ),
        fun f => ⟨headLift f hτ, headLift_comp_toHead f hτ⟩⟩
  refine ⟨(Module.Finite.equiv_iff L).mp hf, ?_⟩
  rw [← L.finrank_eq]
  exact hm

/-- Both forms of the published finite-length head/Hom multiplicity statement,
with independent group, source, and target universes. -/
theorem finiteLengthHeadHomMultiplicity :
    FiniteLengthHeadHomMultiplicityStatement.{uG, uV, uW} :=
  ⟨headHomMultiplicity, semisimpleHomMultiplicity⟩

end Langlands.Classification
