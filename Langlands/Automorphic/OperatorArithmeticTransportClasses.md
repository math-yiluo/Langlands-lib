# Arithmetic transport of full automorphic classes and the Galois action

This module is an internal construction. It descends the actual arithmetic
pullback of `OperatorArithmeticTransport` to the published quotient types:

- `OperatorRealization.IsoClass K n`: realizations up to full equivalence;
- `CuspidalOperatorRealization.IsoClass K r`: actual irreducible cuspidal
  realizations of rank `r + 1` up to full equivalence;
- `PositiveRankCuspidalClass K`: such classes of all positive ranks, with the
  rank retained.

It connects the result to the relation of `ArithmeticTransportRelation` and
defines the Galois action on cuspidal classes. Arthur and Clozel (1989),
Chapter III, Theorem 4.2 (p.202) and Lemmas 6.3 and 6.4 (p.217), use this
action through the conjugates `Π^σ` of cuspidal representations. The
construction generalizes the published `OperatorCMTransportClasses` from the
CM involution to arbitrary isomorphisms `e : K ≃+* L` of number fields in
independent universes.

## Full-operator classes

- `OperatorRealization.arithmeticComap_equivalence_iff`: two realizations over
  `L` are fully equivalent exactly when their pullbacks over `K` are.

  The proof uses only the transport relation. By
  `isArithmeticTransport_arithmeticComap`, `S.arithmeticComap e` is transported
  to `S`. By `isArithmeticTransport_iff`, it is transported to `T` exactly when
  it is equivalent to `T.arithmeticComap e`. Uniqueness of transport targets
  and invariance under equivalence give both directions.
- `OperatorRealization.IsoClass.arithmeticComap e`, defined by `Quotient.lift`,
  is the induced map of classes. `arithmeticComap_isoClass` evaluates it at a
  representative. The identity, contravariant composition and the two inverse
  laws hold. `arithmeticComapEquiv e` is the resulting bijection
  `IsoClass L n ≃ IsoClass K n`.

## Cuspidal classes

With `[CompactSpace (AdeleQuotient K)]` and `[CompactSpace (AdeleQuotient L)]`
explicit:

- `CuspidalOperatorRealization.IsoClass.arithmeticComap e` is the induced map
  on cuspidal classes. `toOperatorClass_arithmeticComap` says that it commutes
  with forgetting to full-operator classes. The identity, composition and
  inverse laws are proved through the injectivity of that forgetful map.
  `arithmeticComapEquiv e` is the resulting bijection.
- `isArithmeticTransport_iff_eq`: `IsArithmeticTransport e c d` holds exactly
  when `c = arithmeticComap e d`. So the transport of a class `c` over `K` along
  `e` is the class `arithmeticComap e.symm c`, its pullback along `e⁻¹`. This
  is `isArithmeticTransport_arithmeticComap_symm`.
- `exists_isArithmeticTransport`: every cuspidal class has an arithmetic
  transport along every field isomorphism.

## Galois action

Let `F` be a field with `[Algebra F K]` and let `σ : K ≃ₐ[F] K`.

- `galoisConj σ c = arithmeticComap σ.toRingEquiv.symm c` is the class of
  `c ∘ σ⁻¹`. Its functions are those of `c` precomposed with the entrywise
  action of `σ⁻¹` on `GL_{r+1}(𝔸_K)`. This matches the published convention
  that automorphisms act on functions by pullback along their inverse
  (`AmbientArithmeticTransport.galoisAut`).
- `isGaloisConjugate_iff`: `c.IsGaloisConjugate σ d ↔ d = galoisConj σ c`.
  `isGaloisConjugate_galoisConj` is the special case `d = galoisConj σ c`.
- `isGaloisStable_iff`: `c.IsGaloisStable σ ↔ galoisConj σ c = c`. Thus the
  stability condition `Π ≅ Π ∘ σ` used in the Arthur–Clozel statements is the
  fixed-point condition of this action.
- `galoisConj_one` and `galoisConj_mul`: `galoisConj (σ * τ) = galoisConj σ ∘ galoisConj τ`.
  The second follows from transitivity of the transport relation and
  uniqueness of transport targets.
- `galoisAction : MulAction (K ≃ₐ[F] K) (IsoClass K r)` packages these laws. It
  is an installable action marked `@[instance_reducible]`. No global instance
  is installed.

## Mixed positive-rank classes

`PositiveRankCuspidalClass K` (published in `CuspidalOperatorRealization`) is
the sigma type `Σ r, CuspidalOperatorRealization.IsoClass K r` of cuspidal
classes of all positive ranks. It is the type of constituents used by isobaric
data. The constructions above act fiberwise and keep the rank index:

- `PositiveRankCuspidalClass.arithmeticComap e c = ⟨c.1, c.2.arithmeticComap e⟩`,
  with `rankIndex_arithmeticComap`, `rank_arithmeticComap` and
  `arithmeticComap_ofFixedRank`. The identity, composition and inverse laws
  follow from the fixed-rank laws. `arithmeticComapEquiv e` is the resulting
  bijection `PositiveRankCuspidalClass L ≃ PositiveRankCuspidalClass K`.
- `PositiveRankCuspidalClass.galoisConj σ c = ⟨c.1, IsoClass.galoisConj σ c.2⟩`.
  `galoisConj_eq_arithmeticComap` identifies it with pullback along `σ⁻¹`, and
  `rank_galoisConj` and `rankIndex_galoisConj` say that it preserves rank.
  `galoisConj_ofFixedRank` evaluates it on a fixed-rank class, and
  `galoisConj_one` and `galoisConj_mul` are the action laws.
- `isGaloisStable_iff_galoisConj_ofFixedRank`: a fixed-rank class `c` is
  `σ`-stable exactly when `ofFixedRank c` is fixed by `galoisConj σ`.
- `PositiveRankCuspidalClass.galoisAction` is the installable action
  `MulAction (K ≃ₐ[F] K) (PositiveRankCuspidalClass K)`. It is marked
  `@[instance_reducible]`, and no global instance is installed.

## Scope

Only classes of actual realizations are acted on, with complex coefficients.
Nothing is asserted about the existence of cuspidal classes, their local
components, base change or descent. Those are the statements of
`Langlands.Automorphic.Unramified.CyclicTransferStatement` and related
modules, which remain separate obligations.
