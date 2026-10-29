# Local central transpose-to-primal conversion

This module states one proposition,
`Langlands.AdmissibleCentralDualToPrimalStatement.{uG,uA,uV}`. It is a
statement only; the module contains no proof of it. The three universes
`uG` (group), `uA` (central parameter group) and `uV` (representation
carrier) are independent.

## Quantifiers and hypotheses

The proposition is closed. It quantifies over

- a group `G : Type uG` with a topology and `IsTopologicalGroup G`;
- the cofinality hypothesis
  `∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H`:
  every open subgroup contains a compact open subgroup;
- a commutative group `A : Type uA` (`[CommGroup A]`), with no topology;
- a complex vector space `V : Type uV`, with no topology or finiteness
  condition, and an actual representation `ρ : Representation ℂ G V`;
- a homomorphism `c : A →* Subgroup.center G` into the actual centre, with
  no continuity condition;
- the hypothesis `IsAdmissible ρ`, the project predicate of
  `Langlands.Representation.Smooth.Definitions`: `ρ` is smooth and its
  space of `K`-fixed vectors is finite dimensional for every open subgroup
  `K`;
- a character `χ : A →* ℂˣ`, with no continuity or open-kernel condition.

Write `ρ_A` for `ρ.comp ((Subgroup.center G).subtype.comp c)`, the
restriction of `ρ` along `c`, so `ρ_A a = ρ (c a)`. The final hypothesis is

`commutativeCharacterSpace (commutativeTranspose ρ_A) χ 1 ≠ ⊥`.

Here `commutativeTranspose ρ_A` is the published transpose action of the
commutative group `A` on the full algebraic dual `Module.Dual ℂ V`; by
`commutativeTranspose_apply` it sends `φ` to `v ↦ φ (ρ (c a) v)`, with no
inverse of `a`. By `mem_commutativeCharacterSpace_one`, a functional lies
in the displayed order-one character space exactly when
`commutativeTranspose ρ_A a φ = (χ a : ℂ) • φ` for every `a`. The
hypothesis therefore says that some nonzero functional `φ` on all of `V`
satisfies `φ (ρ (c a) v) = χ a * φ v` for all `a` and `v`. The functional
need not be smooth.

## Conclusion

The conclusion is `IsGeneralizedEigencharacter ρ_A χ`, the published
predicate of `Langlands.Representation.Exponents.Jacquet`. By
`isGeneralizedEigencharacter_iff` it means: there exist one natural number
`k` and one nonzero vector `v : V` such that
`((ρ (c a) - (χ a : ℂ) • 1) ^ k) v = 0` for every `a : A`. The character is
the same `χ`, with no inversion or complex conjugation, and the power `k`
is uniform over `A` for this vector.

The statement asserts nothing about the entire generalized component of
`χ`: no bound on its nilpotence order, no spanning, spectral finiteness or
decomposition of the full carrier, and nothing about the full dual. It
supplies no open-kernel or continuity conclusion; in applications that
need an open kernel in a supplied topology, that condition remains a
separate input or the conclusion of a different result.

Nothing else is assumed. There is no irreducibility, finite length,
finite generation over the group algebra, finiteness of the span of the
action operators, finite spectrum, supplied primal vector, scalar central
character of the whole representation, or decomposition premise.

The cofinality hypothesis is the one prescribed for this interface and
used by the sibling statement `Langlands.CentralDualEigenQuotientStatement`
and by the reverse-direction theorem cited below. Since the Library's
`IsAdmissible` already requires finite-dimensional fixed spaces for every
open subgroup, the intended route below can also use the open subgroup
fixing the detected vector directly. Applications to Levi subgroups of
`GL_n` over p-adic fields can supply the hypothesis from
`Langlands.UnitaryDualJacquetSupport.levi_compactOpen_cofinal`.

## Intended proof route (not part of this statement)

This is an intended route, not proof evidence and not an extra premise.
Choose a nonzero transpose eigenfunctional `φ` and a vector `v` with
`φ v ≠ 0`. Smoothness gives an open subgroup fixing `v`, and the
cofinality hypothesis gives a compact open subgroup `K` inside it. The
`K`-fixed space is finite dimensional by admissibility. Since `c` lands in
the centre, each `ρ (c a)` commutes with `ρ k` for `k ∈ K`, so this fixed
space is stable under the restricted `A` action. Restricting `φ` to it
gives a nonzero ordinary transpose eigenfunctional with the same `χ`.

On this finite-dimensional space, the published
`Langlands.finiteActionCommutativeSpectrum` (from
`Langlands.Representation.Exponents.FiniteActionSpectrumProof`), applied
with a temporary discrete topology on `A` so that the action is locally
constant, shows that generalized character spaces span. The restricted
functional cannot vanish on all of them, so it is nonzero on a vector `w`
of some component with character `ψ` and some uniform power `k`. By
`commutativeTranspose_defect_pow_apply`, evaluating the defect power at
`w` gives `(χ a - ψ a) ^ k * φ w = 0`, so `ψ = χ`. The inclusion into `V`
carries `w` and the same uniform defect power to the original carrier.

## Provenance

The statement is project-internal and derived; it is not a translation of
a literature statement. It localizes the spectral argument of the existing
`Langlands.ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent`
in `Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly`.
That theorem requires `Representation.IsIrreducible` of the ambient `GL_n`
representation in order to obtain global finiteness; it is unchanged and
not generalized here. The present interface replaces that global step by
one finite-dimensional compact-open fixed space. The reverse direction,
from a primal generalized eigencharacter to a nonzero full-dual
eigenfunctional, is the published
`Langlands.DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter`
in `Langlands.Representation.Exponents.DualEigenfunctionalExistence`; it is
not restated.

Worker 429 formulated this local interface and drafted this statement
pair (shared draft of TaskHub task
`529397b1-c0d9-41a3-95a5-049391c47589`), following finite-fixed-space
discussions with Workers 84 and 728. Worker 944 prepared it for
submission. Worker 84's irreducible-source adapter, task
`cbdc573c-6e54-47c7-abf3-3964703ac5a4`, retains its irreducible scope.

The intended consumer is the general-source pointwise opposite-Jacquet
cone route, statement task `b6bc7ad9-2ad5-40a0-af80-2581a3fd920e`, for the
supported regular comparison proof task
`b8ecf398-d8ff-48bd-a6b3-5da6557b7655`. The separate scalar-subquotient
detector task `5c8bae1a-7ee8-4582-bd59-1294781f2982` runs in the opposite
direction and is not replaced.

This statement supplies no Jacquet admissibility theorem, analytic
exponent criterion, scalar-subquotient detection, opposite-to-upper or
Weyl transport, Jacquet-class inheritance, cone estimate, branch
continuation, multiplicity comparison, composition series, quotient or
head theorem.
