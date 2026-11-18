# The finite-germ comparison from the local structure of the finite pieces

Author: Worker 387 (Task 7655, `6f1f9bc0-d74b-4295-81e0-ccba71f22745`, jointly with Worker 930).

The main theorem `AffineAnalytification.finiteGermComparison_of_finitePieceLocal` proves the
implication

`AffineAnalytificationFinitePieceLocalStatement → AffineAnalytificationFiniteGermComparisonStatement`

in all universes `u, v, w`. It is a conditional result: the hypothesis is the statement of local
structure for the finite pieces. That statement is Worker 930's, and it is proved separately.
Once it is proved, the target statement follows by applying this theorem.

## Setting and conventions

`K` is a complete, ultrametric, nontrivially normed field. `A` and `B` are commutative
`K`-algebras with finite polynomial presentations `P` and `Q`, and `f : A →ₐ[K] B`.
`g := saturatedHom K P Q f` is the analytification map. For a point `s` of the `m`-th chart
algebra, `y := chart K Q m s`, and `q` is the prime of `B` given by the kernel of `s` pulled back
to `B`. Both statements are quoted unchanged from their own modules.

## Declarations

### Algebra (namespace `TensorStalkBaseChange`)

* `flat_atPrime_reflect` and `formallyUnramified_atPrime_reflect` take a pushout square
  `R → T`, `R → S`, `S → D`, `T → D` and a prime `p` of `D` with contraction `q` to `S`. If
  `T` is flat over `R`, `D` is flat over `S`, and `D_p` is flat over `T`, then `S_q` is flat over
  `R`. If `D` is flat over `S` and `D_p` is formally unramified over `T`, then `S_q` is formally
  unramified over `R`. These are the two halves of the published
  `TensorStalkBaseChange.etale_atPrime_reflect` (module `TensorStalkReflection`), stated
  separately; the proofs are the halves of that proof. The flatness half does not use the pushout
  hypothesis, and that hypothesis is omitted there.
* `localRingHom_flat_iff`: for a ring map `f : A → B` and a prime `q` of `B`, the local map
  `A_{f⁻¹ q} → B_q` is flat if and only if `B_q` is flat over `A`. This is Mathlib's
  `Module.flat_iff_of_isLocalization`.
* `localAlgEquivOfBijective`: let `χ : C → S` be a ring map compatible with `R`-algebra
  structures, and let `𝔰` be a prime of `S`. If the local map `C_{χ⁻¹ 𝔰} → S_𝔰` is bijective,
  it is an `R`-algebra isomorphism.
* `flat_and_formallyUnramified_iff_of_localBijective` is the algebraic core. Let `R` be a flat
  `A`-algebra, `φ : R → S` a ring map, and `χ : R ⊗[A] B → S` a ring map with
  `χ (r ⊗ 1) = φ r`. Let `𝔰` be a prime of `S` such that `(R ⊗[A] B)_{χ⁻¹ 𝔰} → S_𝔰` is
  bijective, and let `q` be the prime of `B` under `χ⁻¹ 𝔰`. Then `S_𝔰` is flat over `R` if and
  only if `B_q` is flat over `A`, and `S_𝔰` is formally unramified over `R` if and only if `B_q`
  is formally unramified over `A`.
  The proof first transfers both properties along the isomorphism from `localAlgEquivOfBijective`
  to `(R ⊗[A] B)_{χ⁻¹ 𝔰}`. In the pushout square `A → R`, `A → B`, `B → R ⊗[A] B`,
  `R → R ⊗[A] B`, the map `B → R ⊗[A] B` is flat by base change of `A → R`. The forward
  implications are the two reflection lemmas above. The backward implications are the published
  `TensorStalkBaseChange.flat_atPrime` and `formallyUnramified_atPrime` (module
  `TensorStalkBaseChange`).

### Unfolding finite pieces (namespace `AffinoidAtlasPresentation.StrongHom`)

* `hasFinitePiecesAt_iff_of_pieces`: suppose `g` is finite at `y`, and fix a proposition `Pr`.
  Suppose also that, for every finite piece of `g` (open sets `V`, `U` over which `g` is finite, a
  recognized subset `W` with `W.locus ⊆ U`, and a recognized subset `V'` with
  `V'.locus = V ∩ g⁻¹(W.locus)`), the pointwise property `Q` of the piece at every point `s`
  over `y` is equivalent to `Pr`. Then `g.HasFinitePiecesAt Q y ↔ Pr`.
  Forward: the neighbourhood condition in `HasFinitePiecesAt` gives a `W` in the finite family
  whose locus contains `g y`, finiteness over `W` gives `V'`, and `y` lies in the range of
  `V'.chart`. Backward: start from the witnesses of `IsFiniteAt y`, and take a finite family of
  recognized neighbourhoods inside `U` (published `exists_finite_recognized_nhds_subset`).

### The comparison (namespace `AffineAnalytification`)

* `finitePiece_iff`: assume `AffineAnalytificationFinitePieceLocalStatement`. Take one finite
  piece `φ := g.fullRecognitionPairs.pullback V' W h : W.algebra → V'.algebra` of the
  analytification map, and a point `s'` of `M(V'.algebra)` with `V'.chart s' = y`. Then
  `IsFlatAtPoint φ s'` holds if and only if `B_q` is flat over `A`, and `IsUnramifiedAtPoint φ s'`
  holds if and only if `Algebra.IsUnramifiedAt A q`.
  `IsFiniteOver` provides a recognized subset `V''` with the same locus as `V'` and a finite
  Banach piece. Recognized subsets are subsets of a type of subsets, so equal loci force
  `V'' = V'`, and the piece over `V'` is finite Banach. This finiteness is the hypothesis of the
  local structure statement, which then provides `α`, `β`, `χ` and the local bijectivity.
  Condition 3 of that statement, together with `pointSeminorm_chart` and `chartSeminorm_apply`,
  identifies `q` with the prime of `B` under `χ⁻¹(ker s')`. The algebraic core then applies.
  Finally, the published `BoundedAlgHom.isFlatAtPoint_iff_flat_atPrime` and
  `BoundedAlgHom.isUnramifiedAtPoint_iff_isUnramifiedAt` translate the pointwise properties.
  The second of these needs `φ` of finite type, which follows from finiteness.
* `finiteGermComparison_of_finitePieceLocal` is the main theorem. `StrongHom.IsUnramifiedAt` and
  `StrongHom.IsFlatAt` are `HasFinitePiecesAt` of the pointwise properties. Both equivalences
  follow from `hasFinitePiecesAt_iff_of_pieces` and `finitePiece_iff`, using
  `localRingHom_flat_iff` for the flatness clause.

## Provenance

The argument is adapted from Berkovich 1993, *Étale cohomology for non-Archimedean analytic
spaces*. In Proposition 3.2.10 (printed p.60/PDF p.57), flatness is transferred through faithfully
flat maps. There Zariski's Main Theorem reduces to a finite algebraic morphism, and the
base-change decomposition of Proposition 2.6.10 (printed p.54/PDF p.51) applies to it.
Proposition 3.3.11 (printed p.64/PDF p.61) compares unramifiedness through the sheaves of
differentials. Here both flatness and unramifiedness are derived from the single derived
hypothesis `AffineAnalytificationFinitePieceLocalStatement`. Its condition 4 is a prime-local
analogue, for the Library's recognized pieces of an analytically finite map, of the identity
`A_W = A_V ⊗_B C` used in the proof of Proposition 2.6.10. It is not that proposition.
The rest is the derived commutative algebra described above, proved with Mathlib's flatness,
faithful flatness, localization and Kähler differential results, and the Library's
`TensorStalkBaseChange` and `TensorStalkReflection` modules.
