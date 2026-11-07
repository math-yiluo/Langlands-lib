# Weak automorphic induction and weak association of induced Weil representations

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1, unit U3a of the H3 assembly
(Henniart 2000, §3). Workers 116 (first executor), 44 and 64 raised no objection
to this unit, and no existing statement or task covers it.

The module has one auxiliary definition and one proposition definition. Nothing is
proved and nothing is assumed.

The target is
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement`.
Informally: let `F ⊆ E' ⊆ L` be number fields with `L / F` Galois, and let `ξ` be a
Hecke character of `E'`. Every cuspidal class of `GL_n(𝔸_F)` that is a weak
automorphic induction of `ξ` is weakly associated with the representation
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` of the relative Weil group.

The Library states Harris's Proposition 4.8 (`Langlands.Global.Harris.Proposition48Statement`)
with the conclusion "weak automorphic induction of `ξ`". Henniart's associated pairs
(published `WitnessedGenerator`) need weak association with a Weil representation.
This statement connects the two.

## Declarations

Notation. `c : FundamentalClass.ClassFamily.{u}` is a class family, and
`W_{L/F} = RelativeWeilGroup c F L` is the published extension of `Gal(L/F)` by
`C_L`. `C_{E'}` is `NumberField.IdeleClassGroup (𝓞 E') E'`. A Hecke character of
`E'` is the published `HeckeCharacter E'`, a continuous homomorphism `C_{E'} → ℂˣ`.

- `inducedReciprocityRepresentation c F E' L h ξ`, a definition for
  `h : FundamentalClass.Restriction c` and a continuous character
  `ξ : C_{E'} →ₜ* ℂˣ`. It is a finite-dimensional complex representation of
  `W_{L/F}` with carrier universe `max u uV`. It is the published algebraic
  induction `FiniteRepresentation.induceAlong` along the published injective
  intermediate-field inclusion
  `restrictionInclusion c F L E' h : W_{L/E'} → W_{L/F}`. Its inducing representation
  is the published line `characterLine (reciprocityCharacter c E' L ξ)`. The
  published `reciprocityCharacter c E' L ξ` is
  `w ↦ ξ(transfer c E' L w)⁻¹`, that is `ξ ∘ τ_{E'}` with `τ_{E'}` the pointwise
  inverse of the transfer `W_{L/E'} → C_{E'}`. The definition is elaborated with
  the published discrete topology `relativeGaloisTopology` as a local instance,
  because `restrictionInclusion` is a continuous homomorphism for that topology. The
  representation itself involves no topology.
- `WeakInductionAssociationStatement` (the target, universe parameters
  `u uV uP`). For every class family `c` with the published
  `IsArithmeticClassFamily c`, every proof `h` of `FundamentalClass.Restriction c`,
  all number fields `F E' L : Type u` with `[Algebra F E'] [Algebra F L]
  [Algebra E' L] [IsScalarTower F E' L] [IsGalois F L]`, every instance
  `[CompactSpace (AdeleQuotient F)]`, every `r`, every cuspidal class
  `π : CuspidalOperatorRealization.IsoClass F r` and every `ξ : HeckeCharacter E'`:
  if `π.IsWeakAutomorphicInductionOf.{u, u, uP} ξ`, then
  `IsWeaklyAssociatedClass.{u, max u uV, uP}
    (inducedReciprocityRepresentation c F E' L h ξ) π`.

The published `IsWeakAutomorphicInductionOf ξ` (Harris 1998, Definition 1.3(b), in
the corrected form of the published `WeakInduction` module) says: some spectral
system `s` attached to `π` has rank `[E' : F]`. At all but finitely many finite
places `v` of `F`, the places of `E'` above `v` are unramified, `ξ` is unramified
there, and the Euler polynomial of `s` at `v` is
`∏_{u | v} (1 - ξ_u(ϖ_u) X^{f(u|v)})`.

The published `IsWeaklyAssociatedClass S π` says: some spectral system `s` attached
to `π` (in presentation universe `uP`) is weakly associated with `S`. That is, `S`
is continuous of rank `r + 1`, and at all but finitely many finite places `v` the
following holds at every place `w` of `L` above `v`: local maps
`ι : W_{F_v} → W_{L/F}` with `IsLocalRelativeWeilMap` exist, and for each of them
`S ∘ ι` is unramified with `det(1 - X S(ι Fr_v))` equal to the Euler polynomial of
`s` at `v`. Here `Fr_v` is the published geometric Frobenius.

## Relation to the source

Henniart (2000), §3.4, p.449: for a character `X` of `𝔸_L^×/L^×`, `S(X)` is the
unitary representation of `W_F` induced from the character `X_L` of `W_L`
corresponding to `X`. Harris's theorem there gives a unitary cuspidal automorphic
representation `Π(X)` associated with `S(X)`. In Harris (1998), Proposition 4.8,
p.201, the automorphic representation is a weak automorphic induction of the Hecke
character (Definition 1.3(b), p.186). The association with `S(X)` is the step
formalized here. In this file Henniart's `F`, `L` and `X` are `F`, `E'` and `ξ`.

1. *Relative Weil groups.* Henniart induces from `W_L` to the absolute `W_F`. Here
   the induction is from `W_{L/E'}` to `W_{L/F}` for a Galois `L / F` containing
   `E'`. `X_L` is a character of `W_{E'}`, so it factors through `W_{E'}^{ab}`, a
   quotient of `W_{L/E'}`. The induced representation is the same representation
   read on `W_{L/F}`. Any Galois `L` containing `E'` may be used. U2's proof
   needs this freedom, because the published Harris-datum statements give the
   fields `E'` separately.
2. *The character.* The Weil character of `ξ` is `reciprocityCharacter c E' L ξ`.
   This is the same convention as the published
   `PresentedDeterminantAssociationStatement` (Henniart 2000, §2.2), which says
   `det S = reciprocityCharacter c F E ω` for the central character `ω`. With the
   published `LocalTransferReciprocityStatement` it gives
   `reciprocityCharacter c F L χ (ι g) = χ_v(rec_v g)` for a geometric local
   reciprocity `rec_v` (see the proof sketch).
3. *Arithmetic class family.* Weak association asks for local maps at almost all
   places. For arithmetic `c` they exist by the published
   `LocalRelativeWeilMapExistenceStatement`, whose hypotheses are those of
   `IsArithmeticClassFamily c`. The hypothesis also makes `W_{L/F}` Tate's relative
   Weil group.
4. *The restriction proof.* `restrictionInclusion` needs a proof of
   `FundamentalClass.Restriction c`. It is a conjunct of `IsArithmeticClassFamily c`,
   but there it sits inside an existential. The target therefore quantifies over
   `h`. The quantifier costs nothing, because `Restriction c` is a proposition and
   all its proofs are equal.
5. *Unitarity is not assumed.* In the source the character is unitary. Henniart
   calls `S(X)` and `Π(X)` unitary (§3.4, p.449). Harris's Proposition 4.8
   (p.201) requires `ξ = ξ⁻¹ ∘ c` on the CM field, and this forces `|ξ| = 1`:
   the norm-one idele classes form a compact group (Tate 1979, §1.4.6, p.7, where
   it is the kernel `W^1` of `w ↦ ‖w‖`), so `|ξ|` is trivial on them and factors
   through the idele norm. Complex conjugation preserves that norm, so
   `|ξ| = |ξ ∘ c| = |ξ|⁻¹`. The target is broader. Neither `ξ` nor `π` is assumed unitary,
   because the implication from weak induction to weak association uses only the
   rank and the Euler-polynomial identities.
6. *Compactness instance.* As in `IsWeaklyAssociatedClass`, the target quantifies
   over `[CompactSpace (AdeleQuotient F)]`. The published theorem
   `Langlands.Global.compactSpace_adeleQuotient` proves it, so the quantifier is
   harmless.

## Why the target is true

This is a sketch of the expected proof. Nothing here is proved in the module.

Let `S = inducedReciprocityRepresentation c F E' L h ξ`. Let `s` witness the weak
automorphic induction; the same `s` witnesses the association.

- *Continuity and rank.* `S` is induced from a continuous character of an open
  subgroup of finite index, so it is continuous. Its rank is the index
  `[Gal(L/F) : Gal(L/E')] = [E' : F]`. By the published
  `IsWeakAutomorphicInductionOf.rank_eq` this is `r + 1`.
- *Places.* Exclude the finitely many `v` where `L / F` ramifies, where the weak
  induction condition fails, or where `v ∈ s.exceptional`.
- *Local maps exist.* At each place `w` of `L` above `v`, local CFT gives a
  geometrically normalized reciprocity candidate of `L_w`. The published
  `LocalRelativeWeilMapExistenceStatement` then gives a local map `ι`.
- *Local component.* Fix any local map `ι`. The published
  `LocalInducedRestrictionStatement` (Tate 1979, (2.3.5) and (1.6.1)) gives local
  maps `ι_u : W_{E'_u} → W_{L/E'}`, one for each place `u` of `E'` above `v`. It
  gives `transfer(ι_u y) = i_u(rec_u y)⁻¹`, and `S ∘ ι` is the sum over `u` of the
  inductions to `W_{F_v}` of `reciprocityCharacter c E' L ξ ∘ ι_u`. The first
  identity gives `reciprocityCharacter c E' L ξ (ι_u y) = ξ_u(rec_u y)`.
- *Euler polynomial.* `ξ_u` is unramified and `E'_u / F_v` is unramified, so each
  summand is unramified. Its Euler polynomial is `1 - ξ_u(ϖ_u) X^{f(u|v)}`, by the
  published proved `eulerPolynomial_induceAlong_characterLine`
  (`Langlands/Global/Factors/RelativeWeilLocalEuler.lean`, Tate 1979, (3.3)). A
  geometric reciprocity map sends the geometric Frobenius to the class of a
  uniformizer. The product over `u` is the Euler polynomial of `s` at `v`.

## Intended use

U2 (the published `Langlands.Global.HenniartGlobalizationStatement`) needs witnessed pairs built from Harris's output. Harris gives a
cuspidal class that is a weak automorphic induction of `ξ`. The target makes it
weakly associated with `S = Ind (ξ ∘ τ)`, which is what the published constructor
`WitnessedGenerator.ofUnitaryInduction` needs, together with its other inputs.

## Sources

- Henniart (2000), *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139: §3.4, p.449 (`S(X)`, Harris's theorem).
- Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134: Definition 1.3(b), p.186; Proposition 4.8, p.201.
- Tate (1979), *Number theoretic background*, Corvallis Proc. Symp. Pure Math. 33,
  part 2: §1.4.6, p.7; (1.6.1), p.8; (2.3.5), p.12; (3.3), p.14.
