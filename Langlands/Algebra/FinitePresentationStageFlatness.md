# Flatness at a prime descends to a finite stage

Author: Worker 866.

This helper module proves the pointwise step in the proof of Stacks Project,
Algebra, Lemma 10.168.1, part (1) (Tag 02JO), in the case `M = S`. Let `B`
be an `A`-algebra with a presentation `P` with finitely many variables and
relations, and assume `B` is flat over `A`. For every prime `Q` of `B`, some
finite stage `t` (module `Langlands.Algebra.FinitePresentationStages`) has its
model, localized at the prime under `Q`, flat over the stage base ring. All
declarations live in `Langlands.Algebra.FinitePresentationStages`, and the
module adds no axioms.

## Provenance

- Stacks, proof of Lemma 10.168.1(1): write `R → S` as the directed colimit
  of the stages `R_λ → S_λ` of Lemma 10.127.18. For a prime `q` of `S` with
  traces `p`, `q_λ` and `p_λ`, the localizations
  `((R_λ)_{p_λ}, (S_λ)_{q_λ})` form a system as in Lemma 10.127.13, "as seen
  in the proof of Theorem 10.129.4". Lemma 10.128.3 (Tag 00R6) then gives a
  stage `λ` at which `S_λ` is flat over `R_λ` at `q_λ`.
- The Lean proof follows this route. The stages are those of
  `Langlands.Algebra.FinitePresentationStages`, indexed by finite subsets
  `t ⊆ A`. The local system is a Library `LocalAlgebraSystem` (module
  `Langlands.Algebra.LocalApproximationSystem`), and Lemma 10.128.3 is the
  Library theorem `Langlands.Algebra.localApproximationFlatnessDescent`.
  The module of the system is the regular module, `M = S`.
- Stacks only cites the proof of Theorem 10.129.4 for the system property.
  Here it is proved directly. The colimit property is
  `bijective_lift_locι`. The tensor transitions are localizations at primes
  by `isLocalization_tensor_of_isPushout`, which uses that the global stage
  transitions are pushouts (`isPushout` in the stage module).
- The remaining lemmas are standard internal steps (functoriality of
  localization at compatible primes, inclusions of subalgebras), stated
  separately.

## Localized directed systems

Section `LocalizedSystem` fixes a directed system of commutative rings `G i`
with transition maps `f`, a compatible cocone `g i : G i →+* R`, a prime `p`
of `R`, and primes `P i` of `G i` with `P i = p.comap (g i)`.

`comap_locPrime`: `P i` is the preimage of `P j` under the transition from
`i` to `j`.

`locMap`, `locι`: the induced local homomorphisms
`(G i)_{P i} → (G j)_{P j}` and `(G i)_{P i} → R_p`
(`Localization.localRingHom`). `locMap_algebraMap` and `locι_algebraMap`
compute them on fractions with denominator one. `locι_locMap` is the cocone
compatibility, and `directedSystem_locMap` says the localizations form a
directed system. Both are proved by `IsLocalization.ringHom_ext`.

`bijective_lift_locι`: assume every element of `R` comes from some `G i`,
and every element of `G i` that maps to zero in `R` already maps to zero in
some `G j`. Then the induced map from the direct limit
`Ring.DirectLimit` of the localizations to `R_p` is bijective. Injectivity:
a fraction `a / s` of `G i` mapping to zero is killed in `R` by some
`u ∉ p`; lift `u` to a stage, kill `u a` at a later stage, and observe that
the lift of `u` is outside the prime there. Surjectivity: lift numerator and
denominator of a fraction of `R_p` to a common stage.

Section `Inclusion`: `algebraMap_inclusion` and `directedSystem_inclusion`
are the compatibility and directed-system facts for a monotone family of
subalgebras and the inclusions between them.

## Localizing a pushout

`isLocalization_tensor_of_isPushout`: let `E : S ⊗[R] R' ≃+* S'` be a ring
isomorphism sending `x ⊗ c` to `α x * β c`. Let `S_M`, `R'_N` and `S'_M'` be
localizations of `S`, `R'` and `S'` with `α M ⊆ M'` and `β N ⊆ M'`, and let
`R_p → S_M` and `R_p → R'_N` be compatible with `R → S` and `R → R'`
through a localization `R → R_p`. Assume `S'_M'` is local, and let
`f : S_M ⊗[R_p] R'_N →+* S'_M'` send `s ⊗ r` to `μ s * ν r`, where `μ` and
`ν` extend `α` and `β`. Then `S'_M'` is the localization of
`S_M ⊗[R_p] R'_N` at the prime under its maximal ideal.

Proof: the tensor product of the localization maps and `E⁻¹` give a ring map
`φ : S' → S_M ⊗[R_p] R'_N` with `f ∘ φ` the localization map of `S'`
(`K1`, by tensor induction). Every element `a` of the tensor product
satisfies `a * φ w = φ y` for some `w ∈ M'` (`K2`, by tensor induction: on
pure tensors clear the denominators of both factors). The Library criterion
`isLocalization_atPrime_of_fractions` (module
`Langlands.Algebra.PrimeLocalizationCriterion`) then applies. Every element
of `S'_M'` is a fraction `f (φ m) / f (φ s)` with `s ∈ M'`. If `f a = 0`,
then `φ y` maps to zero for the `y` of `K2`, so `c y = 0` in `S'` for some
`c ∈ M'`, and `φ (c w)` is a unit denominator killing `a`.

## The local system of stages

Section `Stage` fixes a presentation `P` of `B` over `A` and a prime `Q`
of `B`.

`basePrime P Q t` and `modelPrime P Q t`: the primes of `base P t` and
`model P t` under `Q` (through `A` and through `toB P t`). `modelPrime_eq`
rewrites the second as `Q.comap (toB P t)`. An instance records that
`modelPrime` lies over `basePrime`.

`baseLoc P Q t` and `modelLoc P Q t`: the localizations at these primes.
Instances give the local algebra `baseLoc P Q t → modelLoc P Q t`
(`Localization.AtPrime.algebraOfLiesOver`), its locality, and the scalar
tower `base P t → baseLoc P Q t → modelLoc P Q t`.

`baseIncl`, `algebraMap_baseIncl` and two `DirectedSystem` instances: the
stage base rings with their inclusions, and the stage models with the
transitions `trans P h`, are directed systems compatible with the maps to
`A` and `B` (`toB_trans'` is `toB_trans` for the underlying ring maps).

`baseLocMap`, `modelLocMap`, `baseLocι`, `modelLocι`: `locMap` and `locι`
for these two systems, with the values on fractions with denominator one in
the four `_algebraMap` lemmas.

`localAlgebra`: `B_Q` as an algebra over `A_p`, `p = Q ∩ A`, a local
instance in the rest of the module. Instances give its locality and the
scalar tower `A → A_p → B_Q`. `map_comm_stage` and `ι_comm_stage` say that
the localized transitions and cocone maps commute with the structure maps
(proof by `IsLocalization.ringHom_ext`).

`stageSystem P Q`: the Library `LocalAlgebraSystem (Finset A) A_p B_Q` with
base rings `baseLoc P Q t`, algebras `modelLoc P Q t`, the localized
transitions and the localized cocone maps.

`stageSystem_isColimit`: for finitely many relations, both cocones are
colimits. This is `bijective_lift_locι` twice. For the bases, every `a ∈ A`
lies in the stage `{a}`, and the bases are subrings of `A`. For the models,
the inputs are the stage lemmas `exists_lift` and `exists_trans_eq_zero`.

`rbc`, `rbc_tmul`: the Library tensor transition
`(stageSystem P Q).ringBaseChangeMap` for `t ≤ t'`, a ring map
`modelLoc P Q t ⊗[baseLoc P Q t] baseLoc P Q t' → modelLoc P Q t'`, and
its value on pure tensors.

`isLocalization_rbc`: `modelLoc P Q t'` is the localization of this tensor
product at the prime under its maximal ideal. This is
`isLocalization_tensor_of_isPushout` for the pushout square of the stages,
with `E` the isomorphism `Algebra.IsPushout.equiv`. The submonoids are the
complements of `modelPrime P Q t`, `basePrime P Q t'` and
`modelPrime P Q t'`. `stageSystem_isPrimeLocalization` restates it as the
Library predicate `IsPrimeLocalization`.

`essFiniteType_int_of_subsingleton`: essential finite type over `ℤ` does not
depend on the `ℤ`-algebra structure, since there is only one.

`stageSystem_isApproximation`: for finitely many variables and relations,
`stageSystem P Q` satisfies the Library predicate `IsApproximation`:
colimit, `baseLoc P Q t` essentially of finite type over `ℤ` (a localization
of the finite type `ℤ`-algebra `base P t`), `modelLoc P Q t` essentially of
finite type over `baseLoc P Q t` (by `Algebra.EssFiniteType.of_comp`, since
it is essentially of finite type over `base P t`), and the prime
localization property.

`exists_flat_stage`: **pointwise step of Stacks 10.168.1(1).** Let `P` have
finitely many variables and relations, let `B` be flat over `A`, and let `Q`
be a prime of `B`. Then for some stage `t`, the localization of `model P t`
at `Q.comap (toB P t)` is flat over `base P t`. Proof: `B_Q` is essentially
of finite presentation over `A_p`. Both are localizations of finitely
presented `A`-algebras (Library `essFinitePresentation_of_isLocalization`),
and the Library tower cancellation `essFinitePresentationTowerCancellation`
applies. `B_Q` is flat over `A_p` by Mathlib. The Library theorem
`localApproximationFlatnessDescent` (Stacks 00R6), applied to
`stageSystem P Q` and its regular module system (Library
`regularModuleSystem`, approximation by
`regularModuleSystem_isApproximation`), gives a stage `t` with
`modelLoc P Q t` flat over `baseLoc P Q t`. Flatness over `base P t`
follows by transitivity, since the localization `baseLoc P Q t` is flat over
`base P t`.
