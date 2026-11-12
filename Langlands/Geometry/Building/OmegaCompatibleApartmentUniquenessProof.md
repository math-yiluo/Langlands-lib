# Proof of uniqueness of the full omega-compatible apartment class

`Langlands.Geometry.Building.omegaCompatibleApartmentUniqueness` proves the
published proposition
`Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessStatement.{u}`
exactly, at arbitrary universe `u`, with the statement's premises unchanged.

The statement covers every nonarchimedean local field `F : Type u`, every
affine connected reductive `F`-group `G`, and every actual maximal split torus
`i : S → G` whose underlying scheme map is a monomorphism. Fix an actual
centralizer datum `C : CentralizerDatum i` and two apartment data `D` and `E`
for `localFieldOrder F`. If both satisfy full V 6 on `C`
(`D.IsOmegaCompatible C` and `E.IsOmegaCompatible C`), the theorem gives
`D = E`. This is the bundled form of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 6.2.6, explained in the statement's own Markdown.

## Implemented proof

The proof composes two published theorems and adds no hypothesis.

1. **Opposite factor pairs.** `Langlands.GroupScheme.rootRankOneFactorization`
   (module `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`)
   proves `RootRankOneFactorizationStatement.{u}`, which is KP Proposition
   2.11.17 over an arbitrary field. Applied to `F`, `G`, `hG`, `S`, `i` and
   `hi`, it gives `RelativeRoot.HasRankOneFactorization i`. In that statement
   the instances `IsAffineHom G.X.hom` and `Mono i.hom.hom.left` are derived
   from `hG` and `hi`. The target binds them as instance arguments instead.
   Both are propositions, so the terms agree up to definitional equality.
   Let `a` be a relative root and `x` a nonidentity rational point of the
   actual root subgroup of `a`. The first clause of the factorization is
   unique existence of an opposite factor pair for `x`. Its `.exists` part is
   exactly the condition in `RelativeRoot.HasOppositeFactorPairs i`, so that
   predicate holds.

2. **Conditional rigidity.**
   `Langlands.Geometry.Building.omegaCompatibleApartmentRigidity` (module
   `Langlands.Geometry.Building.OmegaCompatibleApartmentRigidity`) proves
   `OmegaCompatibleApartmentRigidityStatement.{u}`. That statement has the
   same premises as the target plus `RelativeRoot.HasOppositeFactorPairs i`.
   Its conclusion is again `D = E`. Applying it to the pairs from step 1, the
   datum `C` and the two compatibility hypotheses proves the target.

For review, the conditional rigidity theorem is proved as follows in the
Library. `KPApartmentData.omegaCompatibleApartmentAffineEquiv` builds an
affine equivalence `D.Apartment ≃ᵃ[ℝ] E.Apartment`. Its linear part is the
identity, and it commutes with the actual normalizer actions. The construction
averages a comparison cocycle over the finite relative Weyl quotient, after
full V 6 shows the cocycle vanishes on the centralizer. This is the existence
part of KP Proposition 4.4.3. The Library's affine-reflection action of an
opposite pair `m(u)` (KP Proposition 6.2.1) gives its displacement formula.
With it, `value_eq_of_equivariant_affineEquiv_of_oppositeFactorPair` shows that such an
equivalence preserves the value of every nonidentity root point that has an
opposite factor pair. Extensionality for root-function families then makes
`x.val` and `(f x).val` equal for a point `x` of `D.Apartment`. Finally
`KPApartmentData.eq_of_common_mem` identifies the two classes.

## Scope

The theorem uses only the target's premises. It assumes no V 7, apartment
axiom, AS 5, Tits system or other unproved proposition. Inspection of the
compiled theorem reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`. It proves neither existence of an omega-compatible class nor any
comparison with other tori or covers.
