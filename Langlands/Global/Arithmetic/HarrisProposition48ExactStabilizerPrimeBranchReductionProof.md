# Proof of the reduction of the exact-stabilizer prime branch of Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionProof`.

## Results

- `proposition48ExactStabilizerPrimeBranchReduction :
  Proposition48ExactStabilizerPrimeBranchReductionStatement.{uF, uV}`, the
  exact target of module
  `HarrisProposition48ExactStabilizerPrimeBranchReductionStatement` (unchanged),
  for arbitrary universes `uF`, `uV`.
- `proposition48ExactStabilizerPrimeBranch_of_inputs`: the argument common to
  this reduction and its totally complex form (proved in
  `HarrisProposition48ExactStabilizerPrimeBranchReductionTCProof`). Its
  hypotheses are interfaces 1–6 and 8–12 of the statement's table, the totally
  complex forms `CyclicRegularInductionTCStatement` (B2) and
  `CyclicWeakInductionSupercuspidalTCStatement` (B4),
  `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7), the
  bridge `CuspidalComplexParameterBridgeTCStatement`, and `hcsd`, which is the
  conclusion of interface 7 once its rigidity premise is discharged; it then
  concludes the body of `Proposition48ExactStabilizerPrimeBranchStatement` for
  given `Q`, `D` and the branch hypotheses.
- A private lemma `finitePlaceEquiv_apply_symm_apply`:
  `finitePlaceEquiv e (finitePlaceEquiv e.symm v) = v`, from
  `finitePlaceEquiv_trans`, `RingEquiv.self_trans_symm` and
  `finitePlaceEquiv_refl`.

No hypothesis is added to the target, and no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` is used.

## The target theorem

The proof introduces the twelve interfaces and the eight premises of the branch
and applies `proposition48ExactStabilizerPrimeBranch_of_inputs`, with
`h7 hRig` (interface 7 applied to the premise `CuspidalSpectralRigidityStatement`)
as `hcsd`. The general B2 and B4 are passed as their totally complex forms by
`fun F E _ _ _ _ _ _ _ _ _ => hB2 F E` (forgetting the instance
`[NumberField.IsTotallyComplex F]`). Harris's Theorem 1.2, isobaric invariance
(`Proposition48IsobaricInvarianceStatement`) and B3
(`CyclicRegularOrbitLiftStatement`) are introduced and not used.

## The common argument

The numbering of the interfaces is that of the table in
`HarrisProposition48ExactStabilizerPrimeBranchReductionStatement.md`; the steps
are those of its proof route. Fix `Q`, `D` and the hypotheses of the branch; the
compactness instance on `AdeleQuotient D` is `compactSpace_adeleQuotient D`.
From `Q.IsAuxiliaryExactStabilizerValid` the proof takes
`IsSplitImaginaryQuadratic Q.p Q.K₀`, `IsNormalClosure Q.E Q.E' Q.L` (hence
`Normal Q.E Q.L` by `IsNormalClosure.normal`), `(Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal`,
the two `HasUniquePlaceAbove` conditions, and `IsAlgebraicAfterTwist`,
`IsRelativelyRegular`, `IsConjugateInverse` for `Q.ξ`; from
`Q.IsPrimeCyclicStep D` it takes `IsGalois Q.E D`, `IsCyclic (D ≃ₐ[Q.E] D)` and
the primality of `[D : Q.E]`.

1. **Fibres.** Interface 1 gives `D ≤ Q.conjugateField 1` and the description of
   the double cosets as fibres of restriction to `D`.
2. **The child of `1`.** The children hypothesis at `a = 1` gives `R`, `S` with
   `Q.IsAuxiliaryMackeyChild D 1 R`, `R.IsUntwistedSolution ν S T` and
   `R.HasInducedComplexPlaceParameters S.isoClass`. The child relation is
   unfolded by a type ascription (the paddings change only `P` and `χ`, so this
   is definitional) to `e : R.E ≃+* D`, `e' : R.E' ≃+* Q.mackeyField D 1`, the
   compatibility of `e`, `e'`, the identification of `R.ξ` and
   `(finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal`. The other
   children are not used.
3. **The constituent `T₀ := S.arithmeticComap e.symm` over `D`.** Interface 3
   makes `T₀.isoClass` a Mackey constituent of `1` and gives, at every complex
   place of `D`, a parameter of `T₀.isoClass` that is the induced Mackey
   parameter. Interface 10 over `R.E` and interface 8 make `T₀` unitary;
   interface 9 makes it supercuspidal at `w₀ := finitePlaceEquiv e.symm R.Ps.v`.
   The places of `D` above `Q.Ps.v` and above `conjPlace Q.E Q.Ps.v` form
   subsingletons (`finitePlacesAbove_subsingleton`, `HarrisUniquePlace`). With
   the local algebra `Q.E → R.E` given by `e.symm ∘ algebraMap Q.E D`,
   `finitePlaceEquiv_liesOver` (`HarrisProposition48StabilizerComparison`) along
   `e` shows that `R.Ps.v` lies above `Q.Ps.v`; `HarrisDatum.conjPlace_liesOver`
   (`HarrisDatumCharacterRealizationProof`) moves this to the conjugate places,
   and `finitePlaceEquiv_liesOver` along `e.symm` gives
   `wc := finitePlaceEquiv e.symm (conjPlace R.E R.Ps.v)` above
   `conjPlace Q.E Q.Ps.v`. Interface 11 over `R.E` followed by interface 9 makes
   `T₀` supercuspidal at `wc`.
4. **Trivial stabilizer.** Every `σ' : D ≃ₐ[Q.E] D` extends to
   `τ := σ'.liftNormal Q.L` (`AlgEquiv.liftNormal_commutes`). If `σ' ≠ 1`, the
   double cosets of `1` and `τ * 1` differ, since by step 1 equality would make
   `σ'` fix `D`. If `T₀.isoClass` were stable under `σ'`, then by
   `isGaloisStable_iff` and interface 2 it would be a Mackey constituent of
   `τ * 1`, and `HasDistinctMackeyComponents` with `T = U = T₀`, the place `w₀`
   and twice the same presentation `P` of `T₀` (supercuspidal at `w₀`, from
   `hasSupercuspidalComponent_iff`) would give a component different from
   itself.
5. **The class `Π` (B2).** A generator `σ` of `Gal(D/Q.E)`
   (`IsCyclic.exists_generator`) has order `[D : Q.E]`
   (`orderOf_eq_card_of_forall_mem_zpowers`, `IsGalois.card_aut_eq_finrank`), so
   `σ ^ i ≠ 1` for `0 < i < [D : Q.E]` (`pow_ne_one_of_lt_orderOf`). A character
   with norm kernel exists by `HeckeCharacter.cyclicNormKernelCharacter`. B2 at
   `F = Q.E`, `E = D` (the instance `[IsTotallyComplex Q.E]` comes from the CM
   structure) gives a class `Π` over `Q.E` that weakly induces `T₀.isoClass`;
   `IsoClass.exists_representative` gives a realization `S_Π` of it.
6. **Weak induction of `ξ`.** Interface 5.
7. **Conjugate self-duality.** `hcsd` with `IsConjugateInverse Q.ξ`.
8. **Supercuspidal at `Q.Ps.v` (B4).** B4 at `v = Q.Ps.v`, the unique place
   `w₀`, `S_Π`, `T₀` and `P`. For `0 < i < [D : Q.E]` the conjugate is
   `U := T₀.arithmeticComap (σ ^ i).toRingEquiv.symm`, whose class is
   `galoisConj (σ ^ i) T₀.isoClass` by definition
   (`isGaloisConjugate_galoisConj`). It is unitary by interface 8 and
   supercuspidal by interface 9 at `finitePlaceEquiv (σ ^ i).toRingEquiv.symm w₀`,
   which lies above `Q.Ps.v` (`finitePlaceEquiv_liesOver`, as `(σ ^ i).symm`
   fixes `Q.E`) and therefore equals `w₀`. Its presentation at `w₀` differs from
   `P` by `HasDistinctMackeyComponents` for the double cosets of `τ * 1` and `1`,
   where `τ` extends `σ ^ i` (step 4, interface 2).
9. **The auxiliary conjugate pair.** Interface 10 over `Q.E` makes `S_Π` unitary,
   interface 11 makes `Π` supercuspidal at `conjPlace Q.E Q.Ps.v`, and interface
   12 gives `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v`.
10. **Parameters (restricted B7(2)).** Clause (2) of restricted B7 at
    `F = Q.E`, `E = D`, `v₀ = Q.Ps.v`, `w₀`, `wc`, for `S_Π` and `T₀` (steps 3, 4,
    5, 8, 9). At a complex place `v` of `Q.E`, the places of `D` above `v` are
    enumerated by `Fintype.equivFin`, and the list at each such place `w` is the
    one chosen (`choose`) from step 3 at `complexPlaceAbove v w`. Restricted B7
    gives `Π` the parameter `complexPlaceLanglandsSum v en ds`, and interface 4,
    whose hypothesis is exactly the data chosen in step 3, shows that it is an
    induced parameter of `Q`. So `Q.HasInducedComplexPlaceParameters Π`.
11. **Regular algebraicity.** Interface 6 with the bridge and the three
    properties of `Q.ξ` from validity.
12. Steps 6, 11, 7 and 8 give `Q.IsSolution Π`; with step 10 this is
    `Q.HasParameterSolution`.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, Proposition 4.8, proof of the case where the set of
Mackey classes is a principal homogeneous space under `Gal(E_{t-1}/E)`, printed
p.203 (registered source `harris-1998-local-langlands`; arXiv source
`math_9611226v1.tex`, lines 1646–1664). Harris takes a base point `Π(e, t-1)`, its
conjugates under a generator `α`, `Π = AI_{E_{t-1}/E} Π(e, t-1)` by
[Arthur–Clozel, Lemma III.6.4], and supercuspidality at the auxiliary place by
[Henniart–Herb, Proposition 5.5] because the conjugate local components are
distinct. The Lean proof follows this argument with the following differences,
recorded in the statement's Markdown: distinctness of the conjugate components
comes from `HasDistinctMackeyComponents` (with interface 2) instead of the
irreducibility of the induced local representation; only the child of the trivial
double coset is used; and the complex-place parameters of `Π` come from
restricted B7(2) with interfaces 3 and 4.
