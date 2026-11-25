# Proof: for a group without characters, semisimplicity is tested in codimension one

This module proves the Library statement
`Langlands.GroupScheme.SemisimpleRepresentationCodimensionOneStatement` (Milne,
*Algebraic Groups* (2017), Lemma 22.40, printed pp. 476–477) at every universe `u`. The
theorem is

```text
theorem Langlands.GroupScheme.semisimpleRepresentationCodimensionOne :
    SemisimpleRepresentationCodimensionOneStatement.{u}
```

It uses no hypotheses beyond those of the statement. The hypothesis
`[LocallyOfFiniteType G.X.hom]` is not used. `[IsAffineHom G.X.hom]` is used to give
subrepresentations and quotient representations coordinates. The no-character hypothesis
`Subsingleton (G ⟶ (Gm _).toGrp)` is used only in (b) ⇒ (a). The proof follows Milne's
overall plan, but the route differs in two places, both explained below:

- (c) ⇒ (b) takes the quotient by a *simple* subrepresentation `U ⊆ W`, not by a maximal
  subrepresentation `W'` of `W`.
- (b) ⇒ (a) works with `End_k(V)` instead of `Hom_k(V, W)`. The subspace `W` is encoded
  by an idempotent matrix `P` with image `W`.

The theorem first `intro`s `k`, `G`, the instances and the no-character hypothesis. Then
`dsimp only` unfolds the statement's local `let`s `IsSimpleStable` and `HasStableComplement`.
The `List.TFAE` is proved with `tfae_have` for 1 → 2, 2 → 3, 3 → 2 and 2 → 1, closed by
`tfae_finish`.

Notation. Throughout, `k : Type u` is a field, `G` is a group scheme over
`Spec (CommRingCat.of k)`, and `n`, `m` are finite index types with decidable equality. For
`ρ : MatrixRepresentation G n`, a `k`-algebra `A` and a point
`x : Spec A ⟶ G.X`, write `g = ρ.affineMatrix A x`, an invertible `n × n` matrix over `A`.
For a constant matrix `P` over `k`, `P_A = P.map (algebraMap k A)`. A matrix `B` *intertwines*
`σ` with `ρ` (Library `Intertwines σ ρ B`) when `B_A · σ(x) = ρ(x) · B_A` for all `A` and
`x`. Every helper lemma lies in the namespace
`Langlands.GroupScheme.SemisimpleRepresentationCodimensionOne`.

## Stable subspaces

- `coefficientMap ρ A x ℓ` is the `k`-linear map `v ↦ (ℓ((ρ(x) v_A)_i))_i`, and
  `isStableSubspace_iff_le_comap` restates `ρ.IsStableSubspace V` as
  `V ≤ V.comap (coefficientMap ρ A x ℓ)` for all `A`, `x`, `ℓ`.
- `isStableSubspace_sSup`: a supremum of stable subspaces is stable, because each
  `comap` is monotone. `isStableSubspace_inf`: an intersection of two stable subspaces is
  stable.
- `IsSimpleStable ρ W` is the statement's local predicate, for an arbitrary finite index type
  `n`: `W` is stable and nonzero, and every stable `U ≤ W` is `⊥` or `W`. For `n = Fin N` it is
  definitionally the statement's `IsSimpleStable`.
- `exists_isSimpleStable_le`: every nonzero stable `W` contains a simple stable `S`. Take
  `S` to be a nonzero stable subspace of `W` of least dimension (`Nat.find`). A nonzero stable
  `U ≤ S` has `finrank U ≥ finrank S`, so `U = S`.
- `exists_subCoordinates`, with `[IsAffineHom G.X.hom]`: a stable `V ⊆ kⁿ` has coordinates.
  These are a representation `σ` on `k^d` and a matrix `B : Matrix n (Fin d) k` such that
  `B` intertwines `σ` with `ρ`, `v ↦ B v` is injective with range `V`, and `finrank V = d`.
  The proof uses the Library's split coordinates `exists_subspace_split_coordinates`, the
  restricted representation `restrictCoordinates` with `intertwines_restrictCoordinates`,
  and `range_coordinateInclusion_eq`.

## (a) ⇒ (b)

`hasComplement_of_sSup_eq_top`. Let `ρ` act on `k^N`, assume that the simple stable
subspaces span (`sSup = ⊤`), and let `W` be stable with `finrank W + 1 = N`. Then
`W ≠ ⊤`, so some simple stable `S` is not contained in `W`. Otherwise `⊤ = sSup ≤ W`.
`W ⊓ S` is a stable subspace of `S`, and it is not `S`, so it is `⊥`. Since
`W < W ⊔ S`, `finrank (W ⊔ S) ≥ finrank W + 1 = N`, so `W ⊔ S = ⊤`. Thus `S` is a stable
complement of `W`. This is a direct dimension argument in codimension one. It replaces
Milne's appeal to Proposition 4.17.

## (b) ⇒ (c)

This is a specialization: a simple stable subspace is stable. In Lean it is
`fun hb N ρ W hW hdim => hb N ρ W hW.1 hdim`.

## (c) ⇒ (b)

`hasComplement_of_simple`, with `[IsAffineHom G.X.hom]`. Assume (c). We show by strong
induction on `N` that every stable `W ⊆ k^N` with `finrank W + 1 = N` has a stable
complement.

1. If `W = ⊥`, then `⊤` is a stable complement.
2. Otherwise choose a simple stable `U ≤ W` (`exists_isSimpleStable_le`). Take the Library's
   quotient representation `q : QuotientRepresentation ρ U`
   (`nonempty_quotientRepresentation`). It has dimension `q.dimension`, representation
   `q.representation` on `k^{q.dimension}`, and a surjective intertwining projection `Q`
   with kernel `U`. The helper `finrank_map_add_finrank_ker` says that
   `finrank (X.map Q) + finrank (ker Q) = finrank X` whenever `ker Q ≤ X`. By this helper,
   `q.dimension + finrank U = N` and `finrank (W.map Q) + 1 = q.dimension`. Since `U ≠ ⊥`,
   `q.dimension < N`.
3. `W.map Q` is stable for `q.representation`. By the induction hypothesis it has a stable
   complement `Lb`. Put `P = Lb.comap Q`, a stable subspace of `k^N` containing
   `U = ker Q`. Since `W ⊇ ker Q`, `W = (W.map Q).comap Q`. Then complementarity of
   `W.map Q` and `Lb` gives `P ⊓ W = U` and `P ⊔ W = ⊤`, and hence
   `finrank U + 1 = finrank P`.
4. Give `P` coordinates `(τ, B)` by `exists_subCoordinates`. By `isSimpleStable_comap`, the
   subspace `U.comap B` is simple stable for `τ`. This lemma transports a simple stable
   subspace back along an injective intertwiner whose range contains it. Also
   `U.comap B` has codimension one in `k^{finrank P}`. Hypothesis (c) gives a stable
   complement `L'` of `U.comap B`.
5. `L = L'.map B` is stable for `ρ`. It satisfies `L ⊓ U = ⊥` and `L ⊔ U = P`. Since
   `L ≤ P`, `W ⊓ L ≤ (P ⊓ W) ⊓ L = U ⊓ L = ⊥`. Since `U ≤ W`,
   `W ⊔ L = (L ⊔ U) ⊔ W = P ⊔ W = ⊤`.
   So `L` is a stable complement of `W`.

Difference from Milne. Milne quotients by a maximal proper subrepresentation `W'` of `W`
and applies (c) to the simple quotient `W/W'` in `V/W'`, then induction inside `V'`. The
Lean proof does the opposite. It quotients by a simple `U ≤ W` and applies induction to the
codimension-one subspace `W/U` of `V/U`. That yields `P ⊇ U` with `P/U` a complement of
`W/U`. It then applies (c) to the simple codimension-one subspace `U` of `P`. Both routes
use only induction on dimension, quotients, sub-coordinates and (c).

## (b) ⇒ (a)

### One-dimensional representations are trivial

- `affineMatrix_eq_one_of_fin_one hX σ A x`: if `G` has only the trivial character, every
  `σ : MatrixRepresentation G (Fin 1)` has `σ.affineMatrix A x = 1`. The coordinate line `0`
  is stabilized: the scalar is the determinant, a unit. So the Library defines the
  character `σ.coordinateLineRationalCharacter 0`, an element of `rationalCharacters G`
  (`Additive` of the group of homomorphisms `G ⟶ (Gm _).toGrp`). By `Subsingleton`, it is
  `0`. The Library's `coordinateLineCharacter_action` with `characterEval_zero` then shows that
  the `(0,0)` entry of `σ.pointMatrix` at `x` is `1`. Transporting along
  `pointMatrix_eq_affineMatrix` and `Corepresented.affineSectionsAlgEquiv A` gives the claim.
- `exists_fixed_of_finrank_eq_one hX σ hL hdim`, with `[IsAffineHom G.X.hom]`. A stable line
  `L` (`finrank L = 1`) contains a nonzero vector `v` with `σ(x) v_A = v_A` for all `A`, `x`.
  Give `L` coordinates `(σ₂, B)` on `k¹` and take `v = B (1)`. By the previous lemma
  `σ₂(x) = 1`, so the intertwining relation gives `σ(x) B_A = B_A`.

### Projections and the representation on endomorphisms

- `exists_stableProjection ρ hW`, with `[IsAffineHom G.X.hom]`. A stable `W` has an
  idempotent matrix `P` (`P * P = P`) whose image lies in `W` and which fixes `W`. It
  satisfies `g P_A = P_A g P_A` for every `g = ρ.affineMatrix A x`. Take `P = B C` from the
  split coordinates `(B, C)` of `W`, with `C B = 1`. Then the relation follows from
  `ρ(x) B_A = B_A σ(x)` for the restricted representation `σ`.
- `map_functional_const_mul`, `map_functional_mul_const`: applying a `k`-linear functional
  `ℓ : A → k` entrywise commutes with left and right multiplication by constant matrices.
- `conj_shape`. Let `g h = 1`, and let both `g` and `h` satisfy `X P_A = P_A X P_A`. Let
  `M` satisfy `P M = M` and `M P = a • P`. Then `N = (g M_A h).map ℓ` satisfies `P N = N`
  and `N P = (a · ℓ 1) • P`. This is a direct matrix computation using the two previous
  lemmas.
- `unvec : (n × n → k) →ₗ[k] Matrix n n k` reads a vector indexed by pairs as a matrix.
- `endW P = {f | P · unvec f = unvec f ∧ unvec f · P = 0}` and
  `endV P = {f | P · unvec f = unvec f ∧ unvec f · P ∈ k P}`. Lemmas `mem_endW`, `mem_endV`
  restate membership.
- `tensorDual_mulVec`: the representation `τ = ρ.tensor ρ.dual` on `k^{n × n}` acts on
  `F`, viewed as a matrix, by `F ↦ g F g⁻¹`. This follows from the Library's
  `tensor_affineMatrix_entry`, `dual_affineMatrix` and
  `GeneralLinear.matrixContragredient_coe`.

### The complement

`hasComplement_of_codimOne hX hb ρ W hW`, with `[IsAffineHom G.X.hom]`. Assume (b). Then
every stable `W` of a representation `ρ` on `kⁿ` has a stable complement.

1. If `W = ⊥`, take `⊤`. Otherwise take `P` from `exists_stableProjection`. Then `P ≠ 0`
   because `P` fixes the nonzero `W`.
2. Since `ρ(x⁻¹) = ρ(x)⁻¹`, both `g = ρ(x)` and `g⁻¹` satisfy `X P_A = P_A X P_A`. With
   `tensorDual_mulVec`, `conj_shape` shows that `endV P` and `endW P` are stable for `τ`
   (with `a` arbitrary and `a = 0` respectively).
3. Let `vP` be the vector of `P`. Then `endV P = endW P ⊔ k·vP` and `endW P ⊓ k·vP = ⊥`.
   Indeed, `f ∈ endV P` with `unvec f · P = a • P` is `(f − a • vP) + a • vP`, and a scalar
   multiple `c • P` with `c P · P = 0` has `c = 0` as `P ≠ 0`. Hence
   `finrank (endW P) + 1 = finrank (endV P)`.
4. Give `endV P` coordinates `(σ, B)` on `k^d`. The subspace `(endW P).comap B` is stable
   and has codimension one. Hypothesis (b) gives a stable complement `L`, and
   `finrank L = 1`. By `exists_fixed_of_finrank_eq_one`, `L` contains a nonzero
   `G`-fixed `v`.
5. `f₀ = B v` lies in `endV P` but not in `endW P`, because `v ∉ (endW P).comap B ⊓ L = ⊥`.
   It is fixed by `τ`. Then `M₀ = unvec f₀` satisfies `g M₀ g⁻¹ = M₀`, so `M₀` intertwines
   `ρ` with itself. Also `P M₀ = M₀` and `M₀ P = a • P`, with `a ≠ 0` because
   `f₀ ∉ endW P`. Hence `M₀ M₀ = a • M₀`.
6. `K = ker M₀` (in Lean `⊥.comap M₀`) is stable because `M₀` intertwines `ρ` with itself
   (Library `IsStableSubspace.comap` of `isStableSubspace_bot`). For `w ∈ W`,
   `M₀ w = M₀ P w = a P w = a w`, so `W ⊓ K = ⊥`. Every `v` is
   `a⁻¹ M₀ v + (v − a⁻¹ M₀ v)`. The first summand lies in `W` because `M₀ = P M₀` and `P` has
   image in `W`. The second lies in `K` because `M₀ M₀ = a • M₀`. So `K` is a stable
   complement of `W`.

Difference from Milne. Milne uses `Hom_k(V, W)` with `V₁ = {f | f|_W ∈ k · id_W}` and
`W₁ = {f | f|_W = 0}`. The Lean proof uses `End_k(V) = V ⊗ V^∨` (the Library's `tensor` and
`dual`) and the subspaces `endV P`, `endW P` of endomorphisms with image in `W`. The
condition "image in `W`" is `P M = M`, and "restriction to `W` is `a · id`" is `M P = a P`.
These are the same spaces as Milne's, under composing `f : V → W` with the inclusion
`W ⊆ V`. The one-dimensional representation is shown trivial through the Library's
coordinate-line character instead of the isomorphism `GL_1 ≅ 𝔾_m`.

### Complements give semisimplicity

`sSup_eq_top_of_hasComplement ρ h`. If every stable subspace of `ρ` has a stable complement,
then the simple stable subspaces span. Let `T` be their supremum, which is stable
(`isStableSubspace_sSup`), and let `C` be a stable complement. If `T ≠ ⊤`, then `C ≠ ⊥`, and
`C` contains a simple stable `S` (`exists_isSimpleStable_le`). Then `S ≤ T ⊓ C = ⊥`, which
contradicts `S ≠ ⊥`. This replaces Milne's induction on `dim V`.

The direction 2 → 1 of the theorem combines these two steps: for each `N` and `ρ`,
`sSup_eq_top_of_hasComplement ρ (fun W hW => hasComplement_of_codimOne hX hb ρ W hW)`.

## Axioms

An axiom check of `Langlands.GroupScheme.semisimpleRepresentationCodimensionOne`
reports the axioms `propext`, `Classical.choice` and `Quot.sound` only.
