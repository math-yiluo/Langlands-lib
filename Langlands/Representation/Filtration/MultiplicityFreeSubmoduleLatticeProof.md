# Proof of the constituent-support lattice of a multiplicity-free representation

Author: Worker 893.
Provenance: internal algebraic proof of the existing statement; the route
differs in part from the source proof (see the last section).

`Langlands.multiplicityFreeSubmoduleLattice` proves exactly
`Langlands.MultiplicityFreeSubmoduleLatticeStatement.{uK, uG, uA}` from
`Langlands.Representation.Filtration.MultiplicityFreeSubmoduleLatticeStatement`.
The statement pair and everything it imports are used unchanged. The proof
module imports, in addition, the published
`Langlands.Representation.Filtration.MultiplicityAdditivityProof` and
`Langlands.Representation.Filtration.MultiplicityTransportProof`. The
auxiliary results below live in the namespace
`Langlands.MultiplicityFreeSubmoduleLatticeProof`; they are lemmas of this
proof and are not separate published statements. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The field `k`, the monoid `G` and the universes `uK`, `uG`, `uA` remain
arbitrary and independent. No group inverses, finite dimension, smoothness,
admissibility or nonzero ambient object is assumed. The helper lemmas are
stated for targets `τ : Rep.{uT} k G` in a fourth free universe and are
applied with `uT := uA`, the target universe fixed by the statement.

## Setting and the multiplicity function

The proof introduces `k`, `G`, `A` and the premise
`HasMultiplicityFreeCompositionSeries A`, and destructs the premise into an
actual series `s : ObjectRepFiltration A N` with `s.HasSimpleFactors` and the
injectivity condition `hfree`: two graded representations of `s` are
equivalent only when their indices are equal. The local `let support` of
the statement is unfolded by `dsimp only`, so each support is literally
`jordanHolderSupport (Rep.of S.toRepresentation)`.

Inside the proof, `choose` fixes for every invariant subspace `S` and every
target `τ : Rep.{uA} k G` a natural number `m S τ` with
`HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ (m S τ)`. Each
value is thus witnessed by an actual finite simple series of `S`. The
existence of such a value is the finite-length step below. This choice is
used only inside the proof and does not alter the published
positive-actual-series meaning of the support. By the published
`HasJordanHolderMultiplicity.unique`, every other witnessed count of the same
`S` and `τ` equals `m S τ`. Therefore, in `mem_iff`,
`τ ∈ jordanHolderSupport (Rep.of S.toRepresentation)` holds if and only if
`0 < m S τ`.

## Finite length of invariant subspaces

`exists_series_sub` shows that every invariant subspace `S` has an actual
finite composition series. The published `repLength_eq_of_hasSimpleFactors`
gives `repLength A.ρ = N` from the ambient series. The published
`repLength_eq_subrepresentation_add_quotient` writes this length as the
length of `S` plus the length of the quotient representation. Hence the
length of `S` is at most `N`, so it is finite. Mathlib's
`Module.length_ne_top_iff` turns this into finite module length over the
monoid algebra. The published `MultiplicityAdditivityProof.exists_series`
then produces an actual `ObjectRepFiltration` of `Rep.of S.toRepresentation`
with irreducible graded representations. `exists_mult_sub` takes the factor
count of this series for a given target. This gives, for every `S` and
every target, a multiplicity witnessed by an actual series.

## Four multiplicity laws

1. **At most one** (`factorMultiplicity_le_one`, `mult_le_one`). The ambient
   count `s.factorMultiplicity τ` is the cardinality of the indices whose
   graded representation is equivalent to `τ`. Two such indices `i` and `j`
   have equivalent graded representations, via an equivalence to `τ` and the
   inverse of another. Then `hfree` forces `i = j`, so the index type is a
   subsingleton and Mathlib's `Finite.card_le_one_iff_subsingleton` bounds
   the count by one. For an invariant subspace `S`, the inclusion `subtype S`
   is an injective intertwiner into `A`. The published
   `jordanHolderInjectiveMonotonicity` bounds the count of `S` by the ambient
   count, so every multiplicity of every invariant subspace is at most one.
2. **Monotonicity** (`mult_mono`). For `S ≤ R`, `inclusion h` is the injective
   inclusion intertwiner, and `jordanHolderInjectiveMonotonicity` gives
   `m S τ ≤ m R τ`.
3. **Modular law** (`mult_modular`). For all `S` and `R`,
   `m (S ⊓ R) τ + m (S ⊔ R) τ = m S τ + m R τ`. This uses the Mayer–Vietoris
   short exact sequence of actual intertwiners

   ```
   S ⊓ R --diagonal--> S × R --difference--> S ⊔ R
   ```

   where `diagonal S R x = (x, x)` is built with Mathlib's
   `Representation.IntertwiningMap.prod` from the two inclusions, and
   `difference S R (a, b) = a - b` is the difference of the two inclusions
   composed with the projections `fst` and `snd`. `diagonal_injective`
   reads off the first component. `difference_surjective` writes an element
   of `S ⊔ R` as `y + w` with `y ∈ S` and `w ∈ R` (`Submodule.mem_sup`) and
   uses the preimage `(y, -w)`. `range_diagonal` proves exactness: a pair
   `(a, b)` with `a - b = 0` has `a = b` in `A`, so this vector lies in both
   subspaces and is the image of an element of the meet. The published
   `jordanHolderProductAdditivity` gives the product representation the
   count `m S τ + m R τ` with an actual series. The published
   `jordanHolderShortExactDecomposition` then splits this count into counts
   of the meet and of the join with actual series. Uniqueness identifies
   these counts with `m (S ⊓ R) τ` and `m (S ⊔ R) τ`. The sequence avoids the
   second isomorphism theorem; multiplicity freeness is not used in this law.
4. **Strict growth** (`exists_mult_lt`). Let `T ≤ S` with `¬ S ≤ T`, where
   `S` has an actual series of some length `N'`. Let `C` be the actual
   quotient of `S` by the range of `inclusion hTS`, and let `q` be the
   quotient map. Together with the injective inclusion, it forms a short
   exact sequence `T → S → C`, exactly as in the published proof of
   `jordanHolderInjectiveMonotonicity`. A first application of
   `jordanHolderShortExactDecomposition` to the series of `S` produces an
   actual composition series `rC` of `C` of some length `nC`. If `nC = 0`,
   then `repLength_eq_of_hasSimpleFactors` gives `C` length zero, and
   `repLength_eq_zero_iff` makes the carrier of `C` a subsingleton. Then
   every vector of `S` maps to zero in `C`, so by exactness it lies in the
   range of the inclusion and hence in `T`, contradicting `¬ S ≤ T`. So
   `nC > 0`, and the target is the actual first graded representation
   `τ := rC.gradedRepresentation ⟨0, _⟩`. As a graded representation of a
   series of `C : Rep.{uA} k G`, it lies in `Rep.{uA} k G`, the target
   universe of the statement. A second decomposition, now for `τ`, writes
   any count of `S` as a count of `T` plus a count of `C`. The count of `C`
   is `rC.factorMultiplicity τ` by uniqueness. It is positive because index
   `⟨0, _⟩` is equivalent to `τ` by the identity equivalence
   (`Nat.card_pos_iff`). Hence every count of `T` for `τ` is strictly
   smaller than every count of `S` for `τ`.

## The six clauses

1. **Actual finite series.** For each `S`, `exists_series_sub` supplies `n`
   and an actual `ObjectRepFiltration (Rep.of S.toRepresentation) n` with
   simple factors.
2. **Order embedding.** If `S ≤ R`, monotonicity turns `0 < m S τ` into
   `0 < m R τ`, so `support S ⊆ support R`. For order reflection, assume
   `support S ⊆ support R` but `¬ S ≤ R`. Then `S ⊓ R ≤ S`, and
   `¬ S ≤ S ⊓ R`, since that would give `S ≤ R`. Strict growth, applied with
   the actual series of `S` from `exists_series_sub`, gives a target `τ` with
   `m (S ⊓ R) τ < m S τ`. Hence `0 < m S τ`, so `τ ∈ support S ⊆ support R`
   and `0 < m R τ`. The modular law
   `m (S ⊓ R) τ + m (S ⊔ R) τ = m S τ + m R τ`, together with
   `m S τ ≤ 1` and `m (S ⊓ R) τ < m S τ`, forces `m S τ = 1` and
   `m (S ⊓ R) τ = 0`, hence `m (S ⊔ R) τ = 1 + m R τ ≥ 2`. This contradicts
   `m (S ⊔ R) τ ≤ 1`; `omega` closes the arithmetic. This is the
   only use of strict growth.
3. **Join identity.** By `mem_iff`, the identity says that
   `0 < m (S ⊔ R) τ ↔ 0 < m S τ ∨ 0 < m R τ`. The backward direction is
   monotonicity along `S ≤ S ⊔ R` and `R ≤ S ⊔ R`. For the forward direction,
   if both `m S τ` and `m R τ` vanish, the modular law forces
   `m (S ⊔ R) τ = 0`. This clause uses only the modular law and monotonicity,
   not the bound by one.
4. **Meet identity.** The identity says that
   `0 < m (S ⊓ R) τ ↔ 0 < m S τ ∧ 0 < m R τ`. The forward direction is
   monotonicity along `S ⊓ R ≤ S` and `S ⊓ R ≤ R`. Conversely, if both
   counts are positive, the modular law and `m (S ⊔ R) τ ≤ 1` give
   `m (S ⊓ R) τ ≥ 1`. Here multiplicity freeness is essential.
5. **Bottom.** The chosen witness for `⊥` is an actual simple series of
   length `n` of the zero subspace. By `repLength_eq_of_hasSimpleFactors`
   its length is `n`, and by the published `repLength_bot` it is `0`.
   Thus `n = 0`, and the index type `Fin 0` of the count is empty
   (`Nat.card_eq_zero`). So `m ⊥ τ = 0` for every target, and the support is
   empty.
6. **Top.** The subspace inclusion of `⊤`, with inverse `v ↦ ⟨v, trivial⟩`,
   is an actual representation equivalence `φ` from
   `(⊤ : Subrepresentation A.ρ).toRepresentation` to `A.ρ`. It is built
   exactly as in the published proof of `repLength_top`. Membership in both
   sides is `∃ m, HasJordanHolderMultiplicity _ τ m ∧ 0 < m`. The published
   `equivJordanHolderMultiplicityTransport`, applied with `φ` and the
   identity equivalence of `τ`, makes the two multiplicity predicates
   equivalent for every `m`, so the two supports in `Set (Rep.{uA} k G)` are
   equal.

## Zero ambient representation and the empty series

No case split on the ambient representation is needed. If `A` is zero, its
multiplicity-free witness is the empty series. Every invariant subspace then
has length zero, so every series supplied by `exists_series_sub` is empty,
all multiplicities are zero, and all six clauses hold by the same argument. The
empty series also occurs in clause 5 for every `A`, and in clause 1 for the
zero subspace.

## Relation to the source

The statement is the internal algebraic formulation of A. V. Zelevinsky,
*Induced representations of reductive p-adic groups II. On irreducible
representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), §2.4, Proposition,
printed p.177 / PDF page 14. The multiplicity-free definition is §2.1(c),
printed p.176 / PDF page 13. Literature ID: `zelevinsky-1980-induced-ii`,
SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The text of these pages of the retained original was read directly for this
proof.
Searches of the Library notes and wiki found no project erratum for this
source.

The implemented route differs in part from the source proof:

- Step (1) of the source deduces `π₁ ⊂ π₂` from `𝒥(π₁) ⊂ 𝒥(π₂)` because
  `Hom(π₁, π/π₂) = 0`. The Lean proof instead uses strict growth along the
  proper inclusion `S ⊓ R < S`, together with the modular law and the
  bound by one.
- Step (2) of the source glues `π₁ + π₂` from `π₁` and
  `π₂/(π₁ ∩ π₂)` (second isomorphism theorem). The Lean proof uses the
  Mayer–Vietoris sequence, which gives the modular law for all counts at
  once. As in the source, the join identity does not use multiplicity
  freeness.
- Step (3) of the source finds a factor of multiplicity at least two in
  `π₁ + π₂`; the Lean proof is the same count argument through the modular
  law.
- The source uses implicitly that submodules of a finite-length module have
  finite length; `exists_series_sub` proves this with actual series.

The source works with composition-factor classes. The Lean supports are sets
of actual representations in `Rep.{uA} k G`, saturated under equivalence.
The proof never chooses class representatives. Each count is attached to a
target `τ` itself, and independence of the chosen series is the published
`HasJordanHolderMultiplicity.unique`. The arbitrary field and monoid are the
internal generality of this purely finite-length argument over the monoid
algebra. No representation-theoretic classification is claimed in that
generality.

## Scope

The proof establishes exactly the six clauses of the statement. It does not
show that every subset of the ambient support is the support of an invariant
subspace. It does not show that a support is a finite set of actual
representations. It provides no segment support labels, no Basic Lemma 2.6,
no edge-halfspace realization and no description of the submodule lattice of
a particular induced representation.
