# Natural cocycles on a finite Galois cover are determined by Galois values

Lean module: `Langlands.GroupScheme.Rational.FiniteGaloisCocycleValues`.

Let `K` be a field, `L/K` a finite Galois extension and `G` a group scheme over
`Spec K`. The cover is the relative scheme `ringTest K L`, i.e. `Spec L` over `Spec K`
(it is `Over.mk (Spec.map (algebraMap K L))`). Cocycles are the Library's natural
group-valued cocycles `Cocycle G (ringTest K L)` on pairs of points over all test schemes.

## Declarations

- `galoisPair σ : ringTest K L ⟶ ringTest K L ⊗ ringTest K L` is the point of the double
  cover with first coordinate the identity and second coordinate the spectrum map
  `ringTestMap K σ` of a Galois automorphism `σ`.
- `galoisPair_fst`, `galoisPair_snd`: its two projections.
- `galoisPair_ext`: two morphisms out of the double cover `Spec L ×_K Spec L` agree as
  soon as they agree after precomposition with every `galoisPair σ`.
- `toFun_eq_of_galois_eq`: two cocycles `ξ ζ` on `Spec L` with
  `ξ(𝟙, σ) = ζ(𝟙, σ)` for every `σ ∈ Gal(L/K)` (meaning the values on the pair
  `(𝟙, ringTestMap K σ)`) agree on every pair of points over every test scheme.
- `toFun_eq_coboundary_of_galois`: if `ξ(𝟙, σ) = c · (σ^* c)⁻¹` for a cochain
  `c : Spec L ⟶ G` and every `σ`, then `ξ(a, b) = c(a) · c(b)⁻¹` for all points `a, b`.
- `isTrivial_of_galois`: under the same hypothesis, `ξ.IsTrivial`.

## Proof

`galoisPair_ext` is the scheme form of the isomorphism `L ⊗_K L ≅ ∏_{σ} L`,
`a ⊗ b ↦ (a σ(b))_σ`: the Library's `Descent.finiteGaloisComponent K L i` are the
components of the double overlap, whose coproduct map
`Sigma.desc (finiteGaloisComponent K L)` is an isomorphism, hence an epimorphism.
Each component is identified with `(galoisPair σ).left` for
`σ = galoisIndexEquiv K L i` by comparing both pullback projections
(`finiteGaloisComponent_fst`, `finiteGaloisComponent_snd`). The underlying scheme of
the monoidal product in `Over (Spec K)` is that same pullback, so cancelling the
epimorphism and checking on coproduct injections gives the claim.

For the cocycle statements, naturality of a cocycle shows that its value at the universal
pair `(fst, snd)` precomposed with `galoisPair σ` is its value at `(𝟙, ringTestMap K σ)`.
So `galoisPair_ext` makes the universal values agree, and the Library lemma
`Cocycle.toFun_eq_of_universal_eq` spreads this to all pairs. The coboundary version
applies this to `ξ` and `Cocycle.coboundary c`.

The module sets `backward.isDefEq.respectTransparency false`, as the Library descent
modules do, because the monoidal product's underlying scheme is only definitionally,
not reducibly, equal to `Descent.Overlap`.

## Provenance

Internal helper for the proof of
`Langlands.GroupScheme.QuasiSplitCocycleTorusReductionStatement` (finite-field case).
The mathematical content is the standard fact that a Galois 1-cocycle for a finite Galois
extension is determined by its values on the Galois group, in the form
`(L ⊗_K L) ≅ ∏_{σ ∈ Gal(L/K)} L` (e.g. Serre, *Galois Cohomology*, or any treatment of
Galois descent). No literature statement is formalized verbatim.
