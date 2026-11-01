# Assembly of the positive-rank right `Φ⁻` sequence from its two orbit pieces

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of the
published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). It proves no clause. It
reduces the clause, at given ranks `k, r`, to two natural isomorphisms: one for
each localized orbit piece of the plus-subgroup Mackey sequence. The identity
piece is constructed in `MirabolicProductMinusRightPhiIdentity`; the cyclic piece
is a separate obligation.

## Provenance

BZ77 (`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`),
Proposition 4.13(c), printed p.458 (PDF p.19), states for `τ ∈ Alg P_m` and
`ρ ∈ Alg G_k` the exact sequence `0 → Φ⁻(τ) × ρ → Φ⁻(τ × ρ) → Ψ⁻(τ) × (ρ|P_k) → 0`.
§7.2, printed p.471 (PDF p.32), proves it by restricting the induced
representation to `P_(n-1) V_n`, applying the geometric lemma (Theorem 5.2) to
two orbits, and localizing. All declarations here are derived internal content
for that argument: category-level lifting, the rank transport of the right mixed
product, and the assembly of the localized Mackey sequence of the published
`MirabolicPhiMinusMackey`.

## Generic category helpers

For a commutative ring `R` and a group `G`:

- `repTwistFunctor χ : Rep R G ⥤ Rep R G` twists by `χ : G →* Rˣ`; maps keep
  their linear maps (`twistIntertwining`).
- `exact_whiskerRight_repTwist`: pointwise short exactness survives
  whiskering by `repTwistFunctor`, since the linear maps are unchanged.

For a topological group `G` and a category `C`:

- `liftNatTrans η` lifts a natural transformation between the underlying
  algebraic functors of two functors `C ⥤ SmoothRep ℂ G` (full inclusion);
  `hom_liftNatTrans_app` is `rfl`;
- `exact_liftNatTrans`: the lift keeps pointwise short exactness;
- `exists_exact_lift i q eA eB eD h`: a pointwise short exact pair `i, q` of
  algebraic transformations, identified at the three positions with the
  underlying algebraic functors of smooth-valued functors by natural
  isomorphisms, gives a pointwise short exact pair between the smooth-valued
  functors. It uses the published `Mirabolic.exact_comp_isos`.

## The transported right mixed product

Fix `p` prime, `F : PadicField p` and `T : F.TopologicalData`.

- `rightPhiCast T k r : P_(k+r+3) ≃ₜ* P_((k+1)+(r+1)+1)` is the published
  entrywise `rankCast (totalRank_eq k r)`, inverted, with both continuities.
- `mirabolicCastHom_eq_rightPhiCast`: the published pullback
  `mirabolicCastHom (Nat.succ_add k (r+1))` is the same homomorphism, entry by
  entry.
- `rightOrbitInput T k r` is the coefficient of the right mixed product
  pulled back to `H = rightInducing k r` (published `MirabolicMixedOrbitData`):
  on `(τ, ρ)` it is `h ↦ χ_R(h) (τ(p) ⊗ ρ(a))`, `(p, a)` the blocks of the
  transported `h`, built from the published `externalFunctor`,
  `pullbackFunctor rightProjection`, `twistFunctor (T.rightCharacter (k+1) (r+1))`
  and `continuousPullbackFunctor (rightInducingHom k r)`.
- `rightPhiTransportEquiv T k r X`: the cast `τ × ρ` is compact induction
  from `rightInducing k r` of this coefficient, through the published
  `Induction.compactInducedTransport` along `rightPhiCast` with the identity of
  the carrier; `rightPhiTransportIso` is the natural isomorphism, naturality
  from `compactInducedTransport_natural`.

## Assembly

- `twistToRepIso`: twisting commutes with forgetting smoothness, on the nose.
- `rightPhiPiece T ψ k r w` is the normalized localized orbit piece at `w`:
  `rightOrbitInput`, then the published orbit piece `Geometric.orbitPiece`
  for `H = rightInducing k r` and `Q = plusSubgroup (k+r+1)` at `w` (the ambient
  group written `mirabolic (k+r+1+1)` as in the Mackey lemma), then
  `plusPhiLocalization ψ (k+r+1)`, then `repTwistFunctor` of the `Φ⁻`
  normalization `phiMinusCharacter T (k+r+1)`.
- `rightPhiMiddleIso`: the twisted localization of the compact induction
  from `H` is the algebraic functor underlying `rightPhiProduct T ψ k (r+1)`,
  through associators, `rightPhiTransportIso` and `twistToRepIso`.
- `rightPhiShortExact_of_pieces T ψ k r s hs E₀ E₁`: given an ordered
  enumeration `s` of the two `(H, Q)` orbits whose representatives are the
  published `rightRepresentative k r` (cycle at `0`, identity at `1`), and
  natural isomorphisms

  ```text
  E₀ : rightPhiPiece T ψ k r (rightRepresentative k r 0) ≅ rightPhiSubobject T ψ k r ⋙ toRep
  E₁ : rightPhiPiece T ψ k r (rightRepresentative k r 1) ≅ rightPhiQuotient T k (r+1) ⋙ toRep
  ```

  there are natural transformations
  `rightPhiSubobject T ψ k r ⟶ rightPhiProduct T ψ k (r+1) ⟶ rightPhiQuotient T k (r+1)`,
  injective, exact in the middle and surjective at every object: exactly the
  conclusion of `RightPhiShortExact` at `ψ, k, r`. The proof applies the
  published `exists_exact_phiMinusUnnormalized_compactInduction` to
  `H = rightInducing k r`, whiskers by `rightOrbitInput` and the twist, and
  lifts with `exists_exact_lift`. It uses `set_option maxHeartbeats 800000`.

## Imports

The direct imports are the published `MirabolicPhiMinusMackey`, the
compatibility statement module (for the functors `rightPhiProduct`,
`rightPhiSubobject`, `rightPhiQuotient` only), `MirabolicProductMinusRightBoundary`
(for lower lemmas; its clause theorem is not used),
`MirabolicProductRestrictionTransport` and `MirabolicMixedOrbitData`. The
complete import closure and the restriction audit of this unit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPhiIdentity.md`.
