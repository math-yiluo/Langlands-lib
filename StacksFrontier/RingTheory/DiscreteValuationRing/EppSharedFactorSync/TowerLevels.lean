module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.PrescribedFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The levels of the family layer recursion

Mixed levels with terminal and carried members, prime-degree terminal layers, terminal bottom
layers, and the per-member trichotomy: carried, terminal, or splittable.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe u

section TowerFamily

open IsDiscreteValuationRing

/-- Over a fraction field of `A`, a field `L` of the residue characteristic `p` of `A` has
characteristic zero or `p`. -/
private theorem charZero_or_charP_of_isFractionRing (A K L : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsFractionRing A K] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    CharZero L ∨ CharP L p :=
  charZero_or_charP_of_injective (algebraMap A L)
    (by rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
    (IsLocalRing.residue A) p

/-- A nontrivial finite purely inseparable extension has a purely inseparable intermediate field
of degree `p`. -/
private theorem exists_isPurelyInseparable_finrank_eq (L M : Type u) [Field L] [Field M]
    [Algebra L M] [Module.Finite L M] [IsPurelyInseparable L M] (p : ℕ) [Fact p.Prime]
    [ExpChar L p] (h1 : 1 < Module.finrank L M) :
    ∃ E : IntermediateField L M, IsPurelyInseparable L E ∧ Module.finrank L E = p := by
  have hbot : (⊥ : IntermediateField L M) ≠ ⊤ := by
    intro hb
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at hb
    omega
  obtain ⟨y, -, hy⟩ :=
    IsDiscreteValuationRing.exists_intermediateField_finrank_eq_of_isPurelyInseparable L M p hbot
  exact ⟨IntermediateField.adjoin L {y}, IsPurelyInseparable.tower_bot L _ M, hy⟩

/-- **The carried-member mechanism, at the shape the recursion's branches actually produce.**

`familyTowerSolvable_of_forall_terminal` takes the carried alternative as
`Module.finrank (L i) (M i) = 1`. Two of the recursion's four branches do not produce that: the
inertia branch, when the inertia group's fixed field is everything, concludes
`IsWeaklyUnramified A (C i)` with the degree unconstrained. So the hypothesis shape, not the
mechanism, was the restriction — `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField`
makes **any** finite base change a weak solution at a weakly unramified member, and the degree
plays no part in it.

This is that lemma with the first disjunct weakened to `IsWeaklyUnramified A (C i)`, which subsumes
the old one through `isWeaklyUnramified_of_finrank_eq_one`. Checked before writing the recursion,
because a carried mechanism that did not cover the inertia branch would have meant that branch
needed a second argument of its own inside the same theorem. It does cover it. -/
theorem familyTowerSolvable_of_forall_terminal_or_isWeaklyUnramified (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (hepp : ∀ i, EppCondition A (B i) p)
    (halt : ∀ i, IsWeaklyUnramified A (C i) ∨
      (IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime)) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  obtain ⟨K₂, _, _, _, _, _, hsol⟩ :=
    hprime {i : ι // ¬ IsWeaklyUnramified A (C i)} A K (fun j => B j.1) (fun j => C j.1)
      (fun j => L j.1) (fun j => M j.1) (fun j => hweak j.1) (fun j => hepp j.1)
      (fun j => (halt j.1).resolve_left j.2)
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  by_cases hw : IsWeaklyUnramified A (C i)
  · exact ⟨canonicalBaseChange A (C i) K (M i) K₂,
      isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A (C i) K (M i) K₂ _ hw⟩
  · exact hsol ⟨i, hw⟩

/-- **The per-member trichotomy of the layer recursion: carried, terminal, or splittable.**

For a member `A ⊆ B ⊆ C` over `K ⊆ L ⊆ M` with `M / L` finite and normal and `B / A` weakly
unramified, exactly one of three things is available:

* `IsWeaklyUnramified A C` — the member is **carried**, and is then solved over *any* finite
  extension of `K` by `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField`;
* `M / L` is **terminal** — purely inseparable of degree `p`, or Galois of prime degree — which is
  what `Stacks.EppTheorem.FamilyPrimeDegreeSolvable` consumes;
* there is a **proper normal intermediate field**, with both degrees `> 1` and hence both `<
  Module.finrank L M`, which is what the induction hypothesis consumes at two smaller degrees.

This is the branch analysis of Tag 09F8's `normalTowerSolvable` with the *solving* removed, and
removing it is what makes the statement separable from the rest of the recursion: nothing in the
conclusion mentions an integral closure, a weak-solution package, or a produced extension, so it
needs no `letI`-threaded existential bundle. One cannot
separate a *terminal bottom layer* instead, since that is **not** closed under its own
recursion; the third alternative here asks only for a proper normal intermediate field, and that
is.

Note what it does **not** need: no `hresidue`, no `IsAlgClosed`, no `PerfectField`, and no
cyclotomic parameter. Those are consumed by 09F8's solving steps, not by its case split, which is
why this holds over a merely perfect residue field — indeed over no hypothesis on the residue field
beyond the characteristic.

The proof is 09F8's, branch for branch: the degree-one case from
`ramificationIdx_dvd_finrank_of_isLocalRing`; the separable closure, being normal over `L`, is `⊥`
or `⊤` once there is no proper normal intermediate field; `⊥` gives purely inseparable of degree
`p`; `⊤` gives Galois, and then the fixed field of the inertia subgroup is normal
(`normal_inertia_maximalIdeal`), so it too is `⊥` or `⊤` — `⊥` makes the Galois group solvable
(`isSolvable_inertia`) and hence the degree prime, and `⊤` makes `B → C` formally unramified
(`formallyUnramified_integralClosure_fixedField_inertia`) and hence the member carried. -/
theorem isWeaklyUnramified_or_terminal_or_exists_properNormal (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M] [Normal L M]
    (hweak : IsWeaklyUnramified A B) :
    IsWeaklyUnramified A C ∨
      (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
        IsGalois L M ∧ (Module.finrank L M).Prime) ∨
      ∃ E : IntermediateField L M, Normal L E ∧
        1 < Module.finrank L E ∧ 1 < Module.finrank E M := by
  classical
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
  -- the carried alternative, from weak unramifiedness of the upper step
  have hcarried (hBC : IsWeaklyUnramified B C) :
      IsWeaklyUnramified A C ∨
        (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
          IsGalois L M ∧ (Module.finrank L M).Prime) ∨
        ∃ E : IntermediateField L M, Normal L E ∧
          1 < Module.finrank L E ∧ 1 < Module.finrank E M :=
    Or.inl (isWeaklyUnramified_trans A B C hweak hBC)
  by_cases h1 : Module.finrank L M = 1
  · refine hcarried ?_
    have hd := ramificationIdx_dvd_finrank_of_isLocalRing B C
    rw [← IsFractionRing.finrank_eq B L C M, h1] at hd
    exact (isWeaklyUnramified_iff_ramificationIdx_eq_one B C).mpr (Nat.dvd_one.mp hd)
  have hnontriv : 1 < Module.finrank L M := lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
  by_cases hproper : ∃ E : IntermediateField L M, Normal L E ∧ E ≠ ⊥ ∧ E ≠ ⊤
  · obtain ⟨E, hE, hbot, htop⟩ := hproper
    exact Or.inr (Or.inr ⟨E, hE,
      lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => hbot (IntermediateField.finrank_eq_one_iff.mp h)),
      lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => htop (IntermediateField.finrank_eq_one_iff_eq_top.mp h))⟩)
  have htriv (E : IntermediateField L M) [Normal L E] : E = ⊥ ∨ E = ⊤ := by
    by_contra h
    push Not at h
    exact hproper ⟨E, inferInstance, h⟩
  rcases htriv (separableClosure L M) with hsep | hsep
  · -- purely inseparable, and with no proper normal intermediate field the degree is `p`
    let : IsPurelyInseparable L M := separableClosure.eq_bot_iff.mp hsep
    have hchar : CharP L p := by
      rcases charZero_or_charP_of_isFractionRing A K L p with hc | hc
      · let := hc
        exact False.elim (h1 (Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
          (IsPurelyInseparable.bijective_algebraMap_of_isSeparable L M)))
      · exact hc
    let := hchar
    obtain ⟨E, hEpi, hE⟩ := exists_isPurelyInseparable_finrank_eq L M p hnontriv
    have hEtop : E = ⊤ := (htriv E).resolve_left fun h =>
      (Fact.out : p.Prime).ne_one (hE.symm.trans (IntermediateField.finrank_eq_one_iff.mpr h))
    have hdeg : Module.finrank L M = p := by
      have he : Module.finrank L E = Module.finrank L M := by rw [hEtop]; simp
      exact he.symm.trans hE
    exact Or.inr (Or.inl (Or.inl ⟨inferInstance, hdeg⟩))
  · -- Galois; split on the fixed field of the inertia subgroup, which is normal over `L`
    let : Algebra.IsSeparable L M := (separableClosure.eq_top_iff L M).mp hsep
    let : IsGalois L M := ⟨⟩
    let R := integralClosure B M
    let : IsDiscreteValuationRing R :=
      (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).1
    let := IsIntegralClosure.MulSemiringAction B L M R
    let P := IsLocalRing.maximalIdeal R
    let I := P.inertia Gal(M/L)
    let : I.Normal := normal_inertia_maximalIdeal Gal(M/L) R
    let E := IntermediateField.fixedField I
    rcases htriv E with hE | hE
    · -- the inertia group is everything, so the Galois group is solvable and the degree is prime
      have hI : I = ⊤ := by
        have h := IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mp hE
        simpa only [IntermediateField.fixingSubgroup_bot] using h.symm
      let : CharP (IsLocalRing.ResidueField B) p := charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective p
      have hsolI : Group.IsSolvable I := isSolvable_inertia B L M p P
      rw [hI] at hsolI
      let := hsolI
      let : Group.IsSolvable Gal(M/L) := Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup Gal(M/L)) ≃* Gal(M/L)).toMonoidHom)
        Subgroup.topEquiv.surjective
      obtain ⟨E', hgal, hp, hcyc, -, -, -⟩ :=
        exists_intermediateField_prime_finrank_of_isSolvable L M hnontriv
      let := hgal
      have htopE : E' = ⊤ := (htriv E').resolve_left fun h =>
        hp.ne_one (IntermediateField.finrank_eq_one_iff.mpr h)
      have hp' : (Module.finrank L M).Prime := by
        have he := ((IntermediateField.equivOfEq htopE).trans
          (IntermediateField.topEquiv : (⊤ : IntermediateField L M) ≃ₐ[L]
            M)).toLinearEquiv.finrank_eq
        exact he ▸ hp
      exact Or.inr (Or.inl (Or.inr ⟨inferInstance, hp'⟩))
    · -- the inertia group is trivial, so `B → C` is formally unramified and the member is carried
      let eE : E ≃ₐ[L] M := (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
      let eR := (eE.restrictScalars B).mapIntegralClosure
      let : IsLocalRing (integralClosure B E) := eR.symm.toRingEquiv.isLocalRing
      let : Algebra.FormallyUnramified B (integralClosure B E) :=
        formallyUnramified_integralClosure_fixedField_inertia B L M inferInstance
      let : Algebra.FormallyUnramified B C := Algebra.FormallyUnramified.of_equiv
        (eR.trans (IsIntegralClosure.equiv B R M C))
      exact hcarried (isWeaklyUnramified_of_formallyUnramified B C)

end TowerFamily

end Stacks.EppTheorem

end
