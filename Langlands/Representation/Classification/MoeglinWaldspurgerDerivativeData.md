# The concrete highest left derivative relation on a cuspidal line

Module `Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeData`, namespace
`Langlands.MoeglinWaldspurger.Derivation`.

Fix a cuspidal datum `ρ` and a real `x`.

* `cuspRep F T ρ x c` is a chosen actual supercuspidal representative (`Quotient.out`) of the
  twist `ν^{x+c} ρ`; `cuspRep_represents` records that it represents that twist.
* `LDrel F T ρ x c cls K S` (for irreducible classes `cls` of rank `n` and `S` of rank `m`)
  holds when `powerRank ρ.rank K m = n` and some representative `π` of `cls` is a subrepresentation of
  `A^K × D` (`powerProduct` of `LeftCuspidalDerivativeStatement`, transported along the rank
  equality), where `A = cuspRep F T ρ x c` and `D` is an irreducible representative of `S` that
  is left `A`-reduced. This is the relation "`(K, S)` is the highest left `ν^{x+c} ρ`-derivative
  of `cls`" used abstractly as `LD` in `MoeglinWaldspurgerLabelInduction`.

## Results

* `powerProductIso`: `A^K × -` carries an isomorphism `Y ≅ Y'` to an isomorphism, by
  induction on `K` (apply the binary product functor to the identity of `A` and the previous
  isomorphism).
* `isSubrepresentation_of_iso`: a subrepresentation of `B` is a subrepresentation of every
  representation isomorphic to `B` (compose the injective morphism with the isomorphism).
* `LDrel_unique`: assuming `LeftCuspidalDerivativeLemma`, the class `cls` is determined by
  `(c, K, S)`. Proof: after identifying the rank equalities, transport the second embedding
  along the isomorphism of the two representatives of `S` (`powerProductIso`),
  then apply the uniqueness clause (clause 4) of the lemma, which says that two irreducible
  subrepresentations of `A^K × S` are isomorphic when `S` is irreducible and left reduced.
  This is the field `unique` (F1) of `DerivativeFacts`.
