# Representations of a group of multiplicative type over a field

`Langlands.GroupScheme.MultiplicativeTypeRepresentationGaloisOrbitStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[IsAffineHom G.X.hom]`
and `IsMultiplicativeType G`. Let `Ks : Type u` be a field with
`[Algebra k Ks]` and `[IsSepClosure k Ks]`. Write
`G_s = (GroupScheme.baseChange (algebraBaseMap k Ks)).obj G` and
`Γ = Ks ≃ₐ[k] Ks`. (The `haveI` at the start of the statement only supplies
the instance `IsAffineHom G_s.X.hom`, by the existing instance for the second
projection of a pullback; it is needed to form `characterSpace` over `Ks`.)
The statement introduces two local `let`s:

- `weights ρ`, for `ρ : MatrixRepresentation G (Fin n)`, is the set of
  characters `χ : rationalCharacters G_s` with
  `(ρ.baseChange (algebraBaseMap k Ks)).characterSpace χ ≠ ⊥`: the weights of
  the representation `ρ ⊗ Ks` of `G_s` on `Ksⁿ`.
- `orbit χ`, for `χ : rationalCharacters G_s`, is the set of all
  `rationalCharacters.galoisRepresentation k Ks G σ χ` with `σ : Γ`: the
  `Γ`-orbit of `χ`.

Then the following five statements hold.

1. Semisimplicity. For every `n` and every
   `ρ : MatrixRepresentation G (Fin n)`,

   ```text
   sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
     ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
       U = ⊥ ∨ U = W} = ⊤,
   ```

   that is, `kⁿ` is the sum of its simple subrepresentations.
2. Simple representations give orbits. If `ρ.IsIrreducible`, then
   `weights ρ = orbit χ` for some `χ`.
3. Every orbit occurs. For every `χ : rationalCharacters G_s` there are `n`
   and an irreducible `ρ : MatrixRepresentation G (Fin n)` with
   `weights ρ = orbit χ`.
4. Orbits determine simple representations. For irreducible
   `ρ : MatrixRepresentation G (Fin n)` and
   `σ : MatrixRepresentation G (Fin m)`, there is a matrix
   `C : Matrix (Fin m) (Fin n) k` with `ρ.Intertwines σ C` and
   `Function.Bijective C.mulVecLin` if and only if `weights ρ = weights σ`.
5. Endomorphisms. Let `ρ : MatrixRepresentation G (Fin n)` be irreducible, let
   `χ ∈ weights ρ`, and let `H : Subgroup Γ` satisfy
   `σ ∈ H ↔ galoisRepresentation k Ks G σ χ = χ` for all `σ` (so `H` is the
   stabilizer of `χ`). Then there is a `k`-algebra homomorphism
   `f : IntermediateField.fixedField H →ₐ[k] Matrix (Fin n) (Fin n) k` that
   is injective and whose range is `{C | ρ.Intertwines ρ C}`.

In words: every finite-dimensional representation of `G` is semisimple;
`V ↦ (weights of V)` is a bijection from the isomorphism classes of simple
representations of `G` onto the set of `Γ`-orbits in `X^*(G) = X(G_{kˢ})`
(statement 2 says the map lands in orbits, 3 that it is surjective, 4 that it
is well defined on isomorphism classes and injective); and if `V` is the
simple representation with orbit `Ξ` and `χ ∈ Ξ`, then `End(V)` is
isomorphic, as a `k`-algebra, to the subfield `k_χ` of `kˢ` fixed by the
stabilizer of `χ`.

Every ingredient is an existing declaration, used without change:

- `IsMultiplicativeType G` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  there are a field `K : Type u` with `Algebra k K`, a finitely generated
  commutative group `Λ : Type u` (`AddGroup.FG Λ`) and an isomorphism of
  group schemes from the base change of `G` to `K` onto the diagonalizable
  group `Diagonalizable.groupScheme (CommRingCat.of K) Λ`, Milne's `D(Λ)`
  over `K`.
- `IsSepClosure k Ks` (Mathlib, `Mathlib.FieldTheory.IsSepClosed`) says that
  `Ks` is separably closed and separable algebraic over `k`. So `Ks` is a
  separable closure of `k`, and `Γ = Ks ≃ₐ[k] Ks` is its group of
  `k`-automorphisms, Milne's `Gal(kˢ/k)` as an abstract group.
- `algebraBaseMap k Ks` (from [`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map (CommRingCat.ofHom (algebraMap k Ks))`. `GroupScheme.baseChange`
  (from [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is
  base change of group schemes along a morphism of base schemes.
- `rationalCharacters G_s` (from [`Rational.Characters`](Characters.md)) is
  the group of homomorphisms `G_s ⟶ 𝔾_m` over `Spec Ks`, written additively:
  the characters of `G` defined over `kˢ`, Milne's `X^*(G) = X(G_{kˢ})`.
- `rationalCharacters.galoisRepresentation k Ks G` (from
  [`Rational.CharacterGaloisAction`](CharacterGaloisAction.md)) is the action
  of `Γ` on `rationalCharacters G_s` by transport along `Spec σ`. Its module
  proves `(σ χ)(σ x) = σ (χ x)` for every `Ks`-point `x`, so `σ χ` is the
  usual Galois conjugate of `χ`. Orbits and stabilizers do not depend on
  whether one uses `σ` or `σ⁻¹`, so the statement does not depend on this
  convention.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GL_n`, a representation of `G` on `kⁿ` with its
  standard basis. `MatrixRepresentation.baseChange` (from
  [`Rational.ValuedRepresentationBaseChange`](ValuedRepresentationBaseChange.md))
  is the base change of this homomorphism followed by the canonical
  isomorphism of the base change of `GL_n` with `GL_n`; for
  `b = algebraBaseMap k Ks` it is the representation `ρ ⊗ Ks` of `G_s` on
  `Ksⁿ`.
- `ρ'.characterSpace χ` (from
  [`MatrixRepresentation.CharacterSpaces`](../MatrixRepresentation/CharacterSpaces.md))
  is the subspace of vectors `v` with `ρ'(x) v = χ(x) v` at the universal
  point `x` of the group, hence (`characterSpace_affine`) at every point
  with values in every commutative algebra: the eigenspace with character
  `χ`. So `weights ρ` is the set of characters of `G_s` occurring in
  `Ksⁿ`.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says that `W` is a subrepresentation; the condition is checked on the
  points of `G` with values in every commutative `k`-algebra.
- `ρ.IsIrreducible` (from
  [`MatrixRepresentation.DenseRationalStability`](../MatrixRepresentation/DenseRationalStability.md))
  says that `kⁿ` is nonzero and that its only stable subspaces are `⊥` and
  `⊤`: the representation is simple.
- `ρ.Intertwines σ C` (from
  [`Lie.RepresentationSubquotient`](../Lie/RepresentationSubquotient.md))
  says that `C · ρ(x) = σ(x) · C` for every commutative `k`-algebra `S` and
  every point `x` of `G` with values in `S`. So `C` is a homomorphism of
  representations from `kⁿ` to `kᵐ`, and with `Function.Bijective
  C.mulVecLin` an isomorphism. `{C | ρ.Intertwines ρ C}` is the set of
  endomorphisms of the representation.
- `IntermediateField.fixedField H` (Mathlib) is the subfield of `Ks` of
  elements fixed by every element of `H`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Theorem 12.30, printed p. 241, preceded by "Let kˢ be a
separable closure of k and Γ = Gal(kˢ/k).":

"Let G be an algebraic group of multiplicative type over k. Then Rep(G) is a
semisimple abelian category, and the isomorphism classes of simple objects in
Rep(G) are classified by the orbits of Γ acting on X^*(G). Let (V, r) be the
representation corresponding to an orbit Ξ, and let χ ∈ Ξ; then
End(V, r) ≃ k_χ where k_χ is the subfield of kˢ fixed by the subgroup of
Gal(kˢ/k) fixing χ."

Conventions used:

- Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Definition 12.17, printed p. 236: "An algebraic group over k is of
  multiplicative type if it becomes diagonalizable over some field
  containing k." Diagonalizable groups: Theorem 12.8 (printed p. 233), "An
  algebraic group G is diagonalizable if and only if it is isomorphic to D(M)
  for some commutative group M", and Theorem 12.9(a) (same page), "The
  functor M ⇝ D(M) is a contravariant equivalence from the category of
  finitely generated commutative groups to the category of diagonalizable
  algebraic groups".
- Section 12g, printed p. 239: "For an algebraic group G, we let
  X^*(G) = X(G_{kˢ}). In other words, X^*(G) consists of the characters of G
  defined over kˢ. The group Γ acts on X^*(G)".
- Definition 12.16, printed p. 236 (for tori): "The characters χ of T such
  that the eigenspace V_χ ≠ 0 are called the weights of T on V".
- Section 12h, printed p. 241: "An abelian category is semisimple if every
  object is a finite sum of simple objects".
- Printed p. 165, in the paragraph headed "Notes" after the proof of
  Theorem 9.2: "Let G be an algebraic group over k and let Rep(G) (or
  Rep_k(G)) denote the category of representations of G on
  finite-dimensional k-vector spaces."
- Definition 4.15, printed p. 90: "A representation of an algebraic group is
  simple if it is ≠ 0 and its only subrepresentations are 0 and itself. It
  is semisimple if it is a sum of simple subrepresentations." Remark 4.18
  (same page): an endomorphism of (V, r) is a k-linear map V → V commuting
  with the action of G(R) on V_R for all R, and "If (V, r) is simple, then
  End(V, r) is a finite-dimensional division algebra D over k."

The provenance is derived for these reasons:

- The group. Milne's group is an affine algebraic group (finite type over
  `k`) of multiplicative type. The Lean statement assumes
  `[IsAffineHom G.X.hom]` (the affineness convention of Chapter 12) and
  `IsMultiplicativeType G`. The Library predicate asks that `G_K ≅ D(Λ)` for
  some field extension `K` and some finitely generated `Λ`; by Theorems 12.8
  and 12.9(a) this is Definition 12.17 for an algebraic group, whose
  diagonalizable base change is `D(Λ)` with `Λ = X(G_K)` finitely generated.
  Finite type is not a separate hypothesis: `G_K ≅ D(Λ)` is of finite type
  over `K`, and finite type descends along the faithfully flat morphism
  `Spec K → Spec k`.
- Rep(G) in coordinates. Objects of `Rep(G)` are finite-dimensional, and
  each is isomorphic to a matrix representation on `kⁿ` for some `n`.
  Semisimplicity of the category means that every object is a finite sum of
  simple objects; for a finite-dimensional representation this is
  Definition 4.15 (a sum of simple subrepresentations is a finite sum by
  dimension), which is statement 1. Simplicity and isomorphism classes are
  invariant under isomorphism, so statements 1–5 for matrix
  representations are statements about all of `Rep(G)`. Isomorphisms are
  intertwining matrices with bijective linear map; endomorphisms are the
  self-intertwining matrices (Remark 4.18), and the test algebras of
  `Intertwines` are all commutative `k`-algebras.
- The classification. Milne does not name the map from simple objects to
  orbits in the statement; his proof (printed p. 242) attaches to `V` the set
  of characters `χ` occurring in `K ⊗ V = ⊕ V_χ` for a finite Galois
  splitting field `K`, which is the set of weights of `V`. The Lean statement
  uses the extension to `Ks` itself: after extension to `Ks`, `G_s` is
  diagonalizable (Theorem 12.18(d), printed p. 237) and, `G` being of
  finite type, every character of `G_s` is defined over a finite
  subextension of `Ks/k`, so the
  weights over `Ks` are the characters occurring in Milne's decomposition.
  "Classified by the orbits" is expressed as the bijection described in
  statements 2–4. The representation "corresponding to an orbit `Ξ`" with
  `χ ∈ Ξ` is an irreducible `ρ` with `χ ∈ weights ρ`.
- Galois group. `Γ` is the group of all `k`-automorphisms of `Ks`; since
  `Ks/k` is a Galois extension, this is `Gal(kˢ/k)`. The Krull topology does
  not enter: orbits and stabilizers are defined for the abstract group.
- `End(V, r) ≃ k_χ`. The fixed field of the stabilizer `H` of `χ` is `k_χ`.
  The stabilizer is supplied as a subgroup `H` together with its defining
  property, which determines it uniquely. Milne's isomorphism is an
  isomorphism of `k`-algebras; the Lean statement asks for an injective
  `k`-algebra homomorphism from `k_χ` to the matrix algebra whose image is
  exactly the endomorphism algebra, which is the same thing.
- `k`, `Ks`, `G` and the test algebras in `IsStableSubspace` and
  `Intertwines` lie in one universe `u`. This is a formalization convention.

Relation to the Library. The Library has the Galois action on characters
(`rationalCharacters.galoisRepresentation`), character spaces of matrix
representations, and the character decomposition for split tori
(`iSup_characterSpace_eq_top_of_isSplitTorus` in
[`MatrixRepresentation.SplitTorusCharacterDecomposition`](../MatrixRepresentation/SplitTorusCharacterDecomposition.md)).
Theorem 12.30 is stated in this module and proved in
[`Rational.MultiplicativeTypeRepresentationProof`](MultiplicativeTypeRepresentationProof.md)
as `multiplicativeTypeRepresentationGaloisOrbit`; the representation theory of
a non-split group of multiplicative type used there is in modules it imports,
for instance `MatrixRepresentation.MultiplicativeTypeSemisimplicity`.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Theorem 12.30 on
printed p. 241 with the same wording, preceded by the same sentence "Let kˢ
be a separable closure of k and Γ = Gal(kˢ/k)."

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 12, corrections on p. 244 (12.41) and p. 249 (proof of 12.57) only,
and for Chapter 4 a correction on p. 95 (proof of 4.29); none concerns the
results used here, and there is no entry for Chapter 9 p. 165. The errata
snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 12, one entry, on p. 234: in the last sentence of Example 12.10 the
base field is algebraically closed. It does not concern Theorem 12.30, and
its Chapter 4 entry (p. 89, proof of 4.14) does not concern Definition 4.15.

## Notes for a proof (not part of this module)

The module `Rational.MultiplicativeTypeRepresentationProof` proves the
statement as `multiplicativeTypeRepresentationGaloisOrbit`.

Milne's proof (printed p. 242) uses Galois descent. One possible route:

- Choose a finite Galois extension `K ⊆ Ks` of `k` over which `G` becomes
  diagonalizable, `G_K ≅ D(M)` (Theorem 12.18(d) and finite type). Every
  character of `G_s` is then the base change of a character of `G_K`.
- For a representation `V` of `G`, `K ⊗ V = ⊕_χ V_χ` (Theorem 12.12 for the
  diagonalizable group `G_K`), and `τ ∈ Gal(K/k)`, acting on `K ⊗ V`
  through `K`, maps `V_χ` onto `V_{τχ}`. So the weights of `V` form a
  union of orbits.
- By Galois descent (A.64–A.66), the subrepresentations of `V` correspond
  to the `G_K`-stable, `Gal(K/k)`-stable `K`-subspaces of `K ⊗ V`. Such a
  subspace is the sum of its intersections with the `V_χ`, and is
  determined, orbit by orbit, by its intersection with `V_{χ₀}` for one `χ₀`
  in each orbit, a `K`-subspace stable under the semilinear action of the
  stabilizer `H₀` of `χ₀` in `Gal(K/k)`. By Galois descent for `H₀`, these
  correspond to the `K^{H₀}`-subspaces of `V_{χ₀}^{H₀}`. This gives
  semisimplicity, shows that the weights of a simple `V` form one orbit
  with one-dimensional weight spaces, and that two simple representations
  with the same orbit are isomorphic.
- For an orbit `Ξ`, the space `⊕_{χ∈Ξ} K·e_χ`, with `G_K` acting on `e_χ`
  through `χ` and `τ` acting semilinearly by `e_χ ↦ e_{τχ}`, descends to a
  simple representation of `G` with weights `Ξ`.
- For simple `V` with orbit `Ξ`, `K ⊗ End(V) = End_{G_K}(K ⊗ V)` is the
  algebra of functions `Ξ → K`, and its `Gal(K/k)`-invariants are the
  equivariant functions, which evaluation at `χ` identifies with
  `K^{H₀} = k_χ`.

The Library's `characterSpace_iSupIndep` (in
[`MatrixRepresentation.CharacterSpaces`](../MatrixRepresentation/CharacterSpaces.md))
gives the independence of the `V_χ`. The Library proves that the
character spaces span the whole space for split tori
(`iSup_characterSpace_eq_top_of_isSplitTorus`) and for a diagonalizable
group `D(M)` with torsion in `M` (`iSup_characterSpace_eq_top_diagonalizable`
in
[`MatrixRepresentation.DiagonalizableCharacterDecomposition`](../MatrixRepresentation/DiagonalizableCharacterDecomposition.md)).
