# Actual local components and supercuspidal support of isobaric data

This module supplies internal attachment vocabulary connecting actual global
cuspidal realizations and spectral presentations to actual local smooth
representations and their supercuspidal supports. Its provenance is the
composition of the published objects in `IsobaricData`,
`CuspidalSpectralPresentation`, `CompletionPadicTower`,
`SupercuspidalRelations`, `FieldTransport`, and `SupercuspidalSupport`.
The attachments and the conversion below are internal definitions, rather than
new assertions attributed to a source.

For the global relations, `F : Type uF` is a number field with
`CompactSpace (AdeleQuotient F)`, `v : FinitePlace F`, `p` is prime,
`hp : CompletionPadic.residuePrime v = p`, and `K : PadicField.{uK} p`.
The algebra equivalence has the direction

```lean
α : letI := (CompletionPadic.padicFieldAt v hp).algebra
  K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hp).Carrier
```

The explicit `letI` installs the canonical completion algebra needed to
elaborate this type. The carrier remains the actual completion; it is not
identified definitionally with `K.Carrier`. Both local fields use their
canonical topological data.

In namespace `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass`,
`HasPadicLocalComponent.{uF,uP,uK,uR} c v hp K α ρ` returns `Prop`.
Here `c : IsoClass F r`, while `ρ` is an actual
`SmoothRep.{0,uK,uR} ℂ (GeneralLinear (r+1) K.Carrier)` for the canonical
topology. The witnesses are an actual full cuspidal realization `S`, a
`CuspidalSpectralPresentation.{uF,uP} S`, and `S.isoClass = c`, together
with a `Representation.Equiv` between the precomposed action of
`P.localComponent v` and `ρ.representation`. On a matrix `g` over `K`,
the action is that of the actual component evaluated at the matrix with
entries `α (g i j)`. This follows directly from the reused
`GeneralLinear.fieldEquiv` and its `fieldEquiv_apply` computation. Its
continuity hypotheses are the published p-adic algebra-equivalence
continuity proofs, in both directions.

The universe parameters occur in the exact order `uF,uP,uK,uR`. They are
independent: `Representation.Equiv` compares the actual form-space carrier
in `uF` with the representation carrier in `uR`, while the spectral
presentation uses `uP`. No shrinking of form spaces is required.

In the same namespace,
`HasPadicSupercuspidalClass.{uF,uP,uK,uV} c v hp K α π` returns `Prop`,
where `π : Correspondence.SupercuspidalAutomorphicClass.{uK,uV} K r.succPNat`.
It asserts that an actual `GeneralLinear.SupercuspidalRep.{uK,uV}` has
`isoClass = π` and satisfies `HasPadicLocalComponent`. Thus the class is the
published genuine quotient of actual supercuspidal representations. The
universe arguments are ordered `uF,uP,uK,uV`. No additional field-pullback
operation on classes is introduced.

In namespace `Langlands.Correspondence`,
`supercuspidalSupportDatum.{uK,uV} K` converts

```lean
Σ k : ℕ, SupercuspidalAutomorphicClass.{uK,uV} K k.succPNat
```

to `K.canonicalTopologicalData.CuspidalDatum.{uV,uK}`. For `a = ⟨k,π⟩`,
its rank is `k+1`, its positivity proof is `Nat.succ_pos k`, and its class
is exactly `π`. The theorem `supercuspidalSupportDatum_rank.{uK,uV}`
is proved by reflexivity. This conversion only changes the published
presentations of the same positive rank and class; it preserves the
supercuspidal representation universe `uV`.

In namespace `Langlands.Automorphic.IsobaricData`,
`HasLocalSupercuspidalSupport.{uF,uP,uK,uV} D v hp K α s` returns `Prop`.
Its last argument has the exact type

```lean
Multiset (Σ k : ℕ,
  Correspondence.SupercuspidalAutomorphicClass.{uK,uV} K k.succPNat)
```

This is exactly the target-field multiset codomain specified for Task 7375's
`CyclicBaseChangeMap`; its successor index records a positive local rank,
and its second component is the genuine supercuspidal class at that rank.
The module writes this published sigma type directly and does not import
Task 7375's work.

The witnesses comprise a length `b`, a full enumeration
`σ : Fin b → PositiveRankCuspidalClass F`, actual local representations
`ρ j`, and local support multisets `t j`. The exact equality
`Finset.univ.val.map σ = D` retains every global occurrence. Each `ρ j`
is a smooth representation of `GL_((σ j).rank)(K)` with carrier universe
`max uK uV`, attached to `(σ j).2` by `HasPadicLocalComponent`. For each
`j`, the published relation
`K.canonicalTopologicalData.IsSupercuspidalSupport (ρ j)
  ((t j).map (supercuspidalSupportDatum K))` holds: some ordering of those
actual supercuspidal classes has `ρ j` as an irreducible subquotient of
their normalized parabolic induction. Finally `s = ∑ j, t j`, as a
multiset sum. Repeated classes are retained in both the enumeration and
this sum. A global cuspidal constituent's local component can have several
support terms, each of smaller rank than the component. The definition
uses the support relation, not the chosen support function that defaults
to zero without an existence hypothesis.

For the zero global datum, take `b = 0`, the empty enumeration and empty
families; the attachment and local-support conditions are vacuous, and
`s = 0`. For `D = IsobaricData.ofCuspidal c`, take `b = 1` and the constant
enumeration `σ j = c`. Given an attached actual local representation `ρ`
and its support `t`, use the constant families to obtain `s = t`. This is
a conditional specialization, not an assertion that every `c` has such
a representation or support. Repeated global constituents are permitted
because `σ` need not be injective; each occurrence has its own local
representation and support witnesses.

The theorem `HasLocalSupercuspidalSupport.sum_rank.{uF,uP,uK,uV}` proves
`(s.map (fun a => a.1+1)).sum = D.rank`. The implemented proof distributes
the rank-sum additive homomorphism over `s = ∑ j, t j`, applies the
published `IsSupercuspidalSupport.sum_rank` to each `ρ j`, simplifies the
conversion's rank by reflexivity, then rewrites the sum of global ranks
using the exact enumeration of `D`. Both levels of multiplicity contribute
to the rank sum.

The motivating source is `operator-external-inputs-plan-2026-11-16`,
Section 4.6, Interface and final recommendation, TeX lines 726–773.
Arthur–Clozel (1989), `arthur-clozel-1989-base-change`, III.4.1 and
III.4.2(c), printed p.202 / registered PDF p.216, supply the intended
unitary isobaric scope; III.5.1, printed p.212 / PDF p.226, motivates the
later weak-to-strong compatibility statement. These passages source the
intended consumer, rather than a theorem of this module. The reused local
support relation follows Zelevinsky (1980),
`zelevinsky-1980-induced-ii`, Proposition 1.10, printed p.174 / PDF p.11.
Its existence and uniqueness assertions are not proved here.

No existence or uniqueness of the attachment relations, local or global
base-change theorem, character identity, weak-base-change premise, E2 map,
or realized isobaric automorphic representation is asserted or constructed.
The relations impose neither regular algebraicity nor a supercuspidality
condition on the local components of the global isobaric constituents.
Unitarity is a separate published condition on `IsobaricData`, for a later
consumer to supply.
