# Formal-degree comparisons

`Langlands.Plancherel.representationFormalDegree` constructs the formal degree
from an actual irreducible representation and its existing
square-integrability witness, without a separately selected scalar character.
It uses the published Schur formal degree on the same quotient with the same
measure. The accompanying laws prove its characterization, positivity,
invariance under representation equivalence and invariance under smooth
norm-one twists.

## Source and provenance

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), registered as
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
III.1 (3), printed p.265 / PDF p.31, characterizes the positive formal degree
by the integral of two coefficients with crossed evaluation pairings.
The proof of III.7.1, printed p.275 / PDF p.41, uses equality of formal degrees
when an irreducible discrete-series representation is equivalent to a unitary
unramified twist of another.

This module is a derived normalization adapter. Schur existence, convergence,
positivity and uniqueness are already proved in
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality`.
The new definition removes its independent scalar-character argument; the
comparison laws follow from that characterization and identities of the
actual quotient integrands. The source uses the rational points of the maximal
split central torus. Here the central subgroup is explicit, and no
identification with that source subgroup is asserted.

## Data and constructed degree

Let `G : Type uG` be a topological group, and let `A` be a subgroup with a
`Normal` instance and an explicit proof `hA : A ≤ Subgroup.center G`.
The quotient `G ⧸ A` has a Borel measurable space, and `μ` is a Haar measure
on that quotient invariant under inversion. The compact-open cofinality
argument `hcof` states that every open subgroup of `G` contains an open
subgroup compact as a subset of `G`.

The representation `ρ : Representation ℂ G V` has independent carrier
universe `uV`, with `AddCommGroup V` and `Module ℂ V`. The inputs are
`hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ` and
`hi : ρ.IsIrreducible`. The existing `hsq` predicate includes admissibility
(hence smoothness), a unitary smooth scalar character of the full center, and
the `L²(μ)` condition for the norms of every actual coefficient with a smooth
dual functional. No finite-dimensional-carrier hypothesis is used.

The definition chooses a full-central-character witness `c` from `hsq.2`,
restricts `c.character` along the actual homomorphism
`Subgroup.inclusion hA : A →* Subgroup.center G`, and invokes the existing
`formalDegree` with the scalar-action proof `c.acts` restricted in the same
way. This defines a real number from the already proved existence theorem;
there is no free degree or extra coefficient-integral hypothesis.
`representationFormalDegree_pos` applies the existing positivity theorem.
Proof irrelevance makes the output independent of the proofs supplied as
`hsq`, `hi` and `hcof`.

For any character `χ : A →* ℂˣ` and any proof
`h : ∀ a v, ρ a v = (χ a : ℂ) • v`,
`orthogonalityIntegral_eq_representationFormalDegree` proves

```text
∫_{G/A} ℓ₁(ρ(g)v₁) ℓ₂(ρ(g⁻¹)v₂) dμ
  = (representationFormalDegree : ℂ)⁻¹ · ℓ₂(v₁) · ℓ₁(v₂).
```

Here both functionals belong to `SmoothDual ρ`, and the integral is exactly
the existing `orthogonalityIntegral A μ h h`. The character witnesses occur
only in the proof that the group function descends to the quotient; changing
them leaves that quotient function definitionally unchanged. The proof applies
the published characterization using the restricted chosen witness.
`representationFormalDegree_eq_formalDegree` then uses
`formalDegree_unique` to identify this value with the existing degree for
every separately supplied scalar-action witness.

## Equivalence comparison

`orthogonalityIntegral_equiv` takes an actual equivalence `e : ρ.Equiv σ`,
where `σ` may have an independent carrier universe `uW`. It pulls a vector of
`σ` back through `e.symm` and a smooth functional of `σ` back through the
published `contragredientMap e.toIntertwiningMap`. It proves equality of the
two integrals for these four transported arguments. Separate characters on
`A` may be used for the two representations.

The proof compares the descended integrands at every quotient point by choosing
a group representative. The intertwining identity and
`e (e.symm w) = w` identify both coefficient factors pointwise, so the integral
equality requires no convergence argument. This law needs only the measurable
quotient and the measure: normality, centrality, Borel compatibility, Haar
invariance, inversion invariance and compact-open cofinality are absent from
its type.

`representationFormalDegree_equiv` retains the full degree assumptions and
takes square-integrability and irreducibility proofs for both representations.
Their scalar witnesses are obtained separately from these proofs. Transporting
the first characterization to the second representation gives the same crossed
evaluation pairings, and `formalDegree_unique` proves equality of the two real
degrees. The quotient and its measure are fixed throughout.

## Smooth unitary twists

`orthogonalityIntegral_twist` takes a character `χ : G →* ℂˣ` whose kernel is
open. It identifies the Schur integral for `twist χ ρ` with the original
integral after applying `smoothContragredientTwistEquiv χ ρ hχ` to both
functionals. That published comparison preserves each underlying linear
functional. On a representative `g`, the two scalar factors are
`χ(g)` and `χ(g⁻¹)`, whose product is one. Linearity and this cancellation
identify the integrands pointwise. This integral comparison has the same
reduced measure assumptions as the equivalence comparison and needs no
norm-one condition.

`representationFormalDegree_unitaryTwist` additionally assumes
`∀ g, ‖(χ g : ℂ)‖ = 1`. It constructs square-integrability of the twist using
`isSquareIntegrableModCentralSubgroup_unitaryTwist` on the same quotient and
measure, and irreducibility using `isIrreducible_twist_iff`. The integral
comparison and uniqueness of the Schur normalization prove equality of the
constructed degrees. The open-kernel and norm-one hypotheses are explicit;
the character need not be unramified for this generic law.

## Remaining scope

The result applies to the displayed generic topological-group data. It does
not establish the required data for rational points of every reductive group,
identify `A` with the source's split center, choose or compare quotient Haar
normalizations, or construct a degree function on representation classes or
their unitary unramified orbits. Those are separate comparisons or
constructions. The Fourier calculation, polynomial operators and decomposition
in III.7, and the actual transform and Plancherel inversion, remain separate
obligations. No irreducibility of parabolically induced representations is used
or inferred.
