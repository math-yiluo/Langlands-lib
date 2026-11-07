# Absolute upper ramification: inertia, wild inertia and the complete family

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.InertiaProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof`,
`Langlands.Galois.Local.AbsoluteProof` and `Langlands.LocalField.Normalization.Proof`.

## What the module proves

Fix a prime `p` with `[Fact p.Prime]` and `F : PadicField.{u} p`. We use these names:

- `Ω` is `AlgebraicClosure F.Carrier` and `G` is `Field.absoluteGaloisGroup F.Carrier`.
- `G^v` is `absoluteUpperRamificationGroup F v` and `r_L` is `absoluteFiniteRestriction F L`.
- `L` ranges over all `FiniteGaloisIntermediateField F.Carrier Ω`.
- `T_L` is the canonical realization `(absoluteFiniteExtension F L).canonicalTopologicalData`,
  and `G_L^v` is `canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v`.

The module proves the three remaining clauses of the Library module `AbsoluteStatement`. It
then assembles the complete family. There are no further hypotheses.

- `absoluteUpperInertia F T : Padic.AbsoluteUpperInertia F T` for every
  `T : F.TopologicalData`. That is, `G^0 = F.absoluteInertia T`, the existing inertia group
  of the spectral valuation ring of `Ω` for the realization `T`.
- `absoluteUpperCanonicalInertia F : Padic.AbsoluteUpperCanonicalInertia F`. This is the case
  `T = F.canonicalTopologicalData`.
- `absoluteUpperWildInertia F : Padic.AbsoluteUpperWildInertia F`. The Krull closure of
  `⨆ (w : ℝ) (_ : 0 < w), G^w` equals
  `⨅ L, (Padic.lowerRamificationGroup T_L F.Carrier 1).comap r_L`.
- `absoluteHerbrandArithmetic : Padic.AbsoluteHerbrandArithmetic.{u}`. All seven clauses
  hold for every prime and every `F : PadicField.{u} p`. The other four clauses are the
  theorems `absoluteUpperFiniteImage`, `absoluteUpperEndpoint`, `absoluteUpperLeftContinuity`
  and `absoluteUpperClosedRightImage` of `AbsoluteProof`.

The one named definition is `IsPadicIntegral F x` for `x : Ω`. It says that `x` is integral
over the integer ring `(ValuativeRel.valuation (Padic p)).integer` of `Padic p`, acting on `Ω`
through `Padic p`. This predicate is an internal device. Both kinds of integer ring are compared
through it.

Supporting results:

- `subring_isUnit_iff A a` and `valuationSubring_isUnit_iff A a`. Here `A` is a subring, or a
  valuation subring, of a field `K`, and `a : A`. Then `a` is a unit of `A` if and only if
  `(a : K) ≠ 0` and `(a : K)⁻¹ ∈ A`.
- `subring_mem_maximalIdeal_iff A a`. If `A` is a local subring of a field `K`, then
  `a ∈ maximalIdeal A` if and only if `(a : K) = 0` or `(a : K)⁻¹ ∉ A`.
- `valuationSubring_residue_eq_iff A a b`. For a valuation subring `A`, `a` and `b` have the
  same residue if and only if `(a : K) - b = 0` or `((a : K) - b)⁻¹ ∉ A`.
- `mem_closureIntegers_iff F T x`. For every realization `T`, `x ∈ F.closureIntegers T` if and
  only if `IsPadicIntegral F x`.
- `mem_canonicalIntegers_iff F L x`. For `x : L`, `x ∈ T_L.Integers` if and only if
  `IsPadicIntegral F (x : Ω)`.
- `canonical_mem_maximalIdeal_iff F L a`. For `a : T_L.Integers`, `a` lies in the maximal ideal
  if and only if `((a : L) : Ω) = 0` or `¬IsPadicIntegral F ((a : L) : Ω)⁻¹`.
- `absoluteFiniteRestriction_apply_coe F L σ x`. For `x : L`, the element `r_L σ x` of `L` is
  `σ x` in `Ω`.
- `mem_absoluteInertia_iff F T σ`. `σ ∈ F.absoluteInertia T` if and only if, for every
  `x : Ω` with `IsPadicIntegral F x`, either `σ x - x = 0` or
  `¬IsPadicIntegral F (σ x - x)⁻¹`.
- `mem_canonicalInertia_iff F L τ`. For `τ : Gal(L/F.Carrier)`,
  `τ ∈ Padic.inertia T_L F.Carrier` if and only if the same condition holds for all `x : L`,
  with `σ x` replaced by `τ x` read in `Ω`.
- `iSup_upperRamificationGroup_pos T K`. Let `T : F.TopologicalData` be any realization of a
  finite p-adic field `F` with a field `K` below it. Then
  `⨆ (w : ℝ) (_ : 0 < w), Padic.upperRamificationGroup T K w = Padic.lowerRamificationGroup T K 1`.
  No Galois hypothesis is needed.
- `iInf_comap_map_absoluteFiniteRestriction F H hH`. Let `H` be a subgroup of `G` that is
  closed in the Krull topology. Then `⨅ L, (H.map r_L).comap r_L = H`.

## Sources

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. The relevant passages are
the ones cited by the Library statement module `AbsoluteStatement`:

- Chapter IV, §1, Proposition 1 (printed p. 62): the group of index `0` is the inertia group.
- §2, Proposition 7 and Corollaries 1 and 3 (printed pp. 67–68): the group of index `1` is the
  wild part.
- §3, the upper numbering (printed pp. 73–74) and Remark 1 (printed p. 75): the filtration of
  an infinite Galois group.

Printed page `n` is PDF page `n + 7`. As `AbsoluteStatement` records, the inertia comparison
across realizations and the wild-inertia formula are derived assertions. The lemma that a
closed subgroup is the intersection of the preimages of its finite images is the standard
Galois correspondence for closed subgroups. It is Mathlib's
`InfiniteGalois.fixingSubgroup_fixedField`. All supporting results above are internal steps of
the implemented proof.

## Proof (as implemented)

1. **Units in subrings.** If `a` is a unit with inverse `b`, then `(a : K) * b = 1`. So `a ≠ 0`
   and `(a : K)⁻¹ = b ∈ A`. Conversely `a * ⟨a⁻¹, _⟩ = 1` (`IsUnit.of_mul_eq_one`). The maximal
   ideal of a local ring consists of its nonunits. Equal residues means the difference lies
   in the maximal ideal (`IsLocalRing.residue_eq_zero_iff`).
2. **Integers as p-adic integral elements.** Let `A` be the integer ring of `Padic p`.
   - In `Ω`: the Library lemma `LocalGalois.closureIntegers_integral` identifies the spectral
     closure integers of `T` with the elements integral over `T.Integers`. The ring
     `T.Integers` is finite over `A` (`T.integers_finite`, with `T.integerAlgebra`), hence
     integral. The tower `A → T.Integers → Ω` commutes by
     `IsScalarTower.algebraMap_apply (Padic p) F.Carrier Ω`. Transitivity of integrality
     (`isIntegral_trans`) gives one direction and `IsIntegral.tower_top` the other.
   - In `L`: `isIntegral_iff_mem_integers` for `T_L` identifies `T_L.Integers` with the
     elements of `L` integral over `A`. The inclusion `L → Ω` is an injective `A`-algebra map,
     so integrality transfers (`isIntegral_algHom_iff`).
3. **Inertia by integrality.** For the absolute group, the Library lemma
   `LocalGalois.absoluteInertia_mem` says that `σ` is inertial exactly when `σ x` and `x` have
   the same residue for every closure integer `x`. Steps 1 and 2 rewrite this as
   `mem_absoluteInertia_iff`. For `L`, `Padic.lowerRamificationGroup_zero` identifies inertia
   with the lower group of index `0`. Its defining condition is
   `integerAutomorphism τ x - x ∈ maximalIdeal ^ 1`. Steps 1 and 2 rewrite this as
   `mem_canonicalInertia_iff`.
4. **The inertia clause.** By `mem_absoluteUpperRamificationGroup_iff`, the finite lemma
   `Padic.upperRamificationGroup_zero` (`G_L^0` is the inertia group) and step 3, both sides
   become integrality conditions. With `absoluteFiniteRestriction_apply_coe` they are:
   - for `G^0`: for every `L` and every `x : L`, the condition holds at `x`;
   - for `F.absoluteInertia T`: for every `x : Ω`, the condition holds at `x`.

   The second implies the first because `L ⊆ Ω`. For the converse, take
   `L = FiniteGaloisIntermediateField.adjoin F.Carrier {x}`, which contains `x`. The canonical
   clause is the case `T = F.canonicalTopologicalData`.
5. **Finite wild lemma** (`iSup_upperRamificationGroup_pos`). Write `ψ = Padic.herbrandPsi T K`.
   - Upper bound: for `w > 0` we have `ψ(w) > 0` (`herbrandPsi_pos`), so `⌈ψ(w)⌉ ≥ 1`. Hence
     the upper group `G_{⌈ψ(w)⌉}` lies in the integer lower group of index `1`, by
     antitonicity (`lowerRamificationGroupInt_antitone`).
   - Attained: at `w = φ(1) > 0` (`herbrandPhi_pos`), `upperRamificationGroup_phi` gives the
     real lower group of index `1`.
   - The real, integer and natural lower groups of index `1` agree by
     `lowerRamificationGroupReal_int` and `lowerRamificationGroupReal_nat`.
6. **Closed subgroups** (`iInf_comap_map_absoluteFiniteRestriction`). One inclusion is
   `Subgroup.le_comap_map`. For the other, let `σ` lie in every `(H.map r_L).comap r_L`. Since
   `H` is closed and `Ω/F.Carrier` is Galois (characteristic zero),
   `InfiniteGalois.fixingSubgroup_fixedField` writes `H` as the fixing group of its fixed field.
   So it suffices that `σ x = x` for every `x` fixed by `H`. Let `L` be the finite Galois field
   `adjoin F.Carrier {x}`. Some `τ ∈ H` has `r_L τ = r_L σ`. Then, by
   `absoluteFiniteRestriction_apply_coe` at `x ∈ L`, `σ x = τ x = x`.
7. **The wild-inertia clause.** Apply step 6 to the closure `R` of `⨆ (w : ℝ) (_ : 0 < w), G^w`,
   which is closed (`Subgroup.isClosed_topologicalClosure`). It remains to identify
   `R.map r_L` for each `L`. By `absoluteUpperClosedRightImage F L 0` it is
   `⨆ (w : ℝ) (_ : 0 < w), G_L^w`. Step 5 for `T_L` turns this into the first lower group of
   `L`.
8. **The complete family.** `absoluteHerbrandArithmetic` is the conjunction of the seven
   theorems, in the order of `Padic.AbsoluteHerbrandArithmetic`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
