# Proof of closed-immersion preservation for finite-type Weil restriction

Worker 105 wrote the proof of `WeilRestrictionClosedImmersionProperties A B`;
Worker 1330 checked it against the published target and constructions.
This is the closed-immersion preservation step in Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 2.4,
printed page 3 (registered source
`conrad-2011-weil-grothendieck-adelic-points`).
The algebraic proof adapts the Tau Ceti contributors' range-factorization
and `map_surjective` arguments from
`Langlands/TauCeti/RingTheory/WeilRestriction/Basic.lean`, upstream commit
`8428d6217f74afa72531df0bc85d7b57ab72810f`. Its Apache 2.0 attribution
is retained; the license is in `licenses/TauCeti/`. The old
finite-presentation declarations remain unchanged.

The proof uses the finite-type representing equivalence instead of the
old finite-presentation equivalence. First, for a map from the representing
algebra to `T` and a subalgebra `S` of `T`, it proves that the map has image
in `S` exactly when its classified tensor-valued point has image in the
image of `B ⊗[A] S`. One implication follows by naturality. For the other,
flatness of the projective `A`-module `B` makes
`B ⊗[A] S → B ⊗[A] T` injective. The tensor-valued point therefore lifts
uniquely into `B ⊗[A] S`; its classifying map to `S`, followed by inclusion
into `T`, equals the original map by injectivity of the representing
equivalence.

Apply this criterion to the range of the map induced by a surjection
`φ : C →ₐ[B] D`. Universal-point naturality shows that the universal
point of `D` takes values in the tensor image of that range: each element
of `D` is `φ c` for some `c`. The criterion then makes the identity of
the representing algebra of `D` factor through that range, so the range
is the whole algebra. This proves `map_surjective` for finite-type inputs
without a finite-presentation assumption.

For an actual closed immersion `f : X ⟶ Y` between the specified affine
schemes, Mathlib gives surjectivity of the actual global-section pullback.
The algebraic result gives surjectivity of its Weil-restriction map.
Mathlib's spectrum-of-a-surjection theorem then proves that the actual
map `affineWeilRestrictionMap A B f` is a closed immersion. The final
theorem assembles the algebraic and scheme assertions of the target.

All rings are arbitrary commutative rings, with `B` finite projective
over `A`. No topology, faithfulness, field, Noetherianity or finite
presentation is used.

The arbitrary finite-projective algebra scope extends Conrad's ring-extension
formulation: tensor injectivity uses flatness, so injectivity of `A → B` is
unnecessary for this algebraic conclusion. This derived extension is already
part of the published target.
