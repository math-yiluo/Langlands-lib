# Statement: universality of Weyl conjugation in Weyl families

This module defines the predicate `LocalSplitCell.WeylConjugationRelations`. It states,
without proof, that the Weyl families of two reductive groups over a local ring satisfy it.
It contains one definition and one `Prop`-valued statement, and no theorems.

## The predicate

Notation, from the imported modules:

- `weylFamily P W u α` is the map `𝔾ₐ → G` obtained from the simple root `(W α).simple` by
  conjugation along the word `(W α).word` (module `LocalSplitWeylFamily`);
- `rootWeylPoint P u c = weylPoint (u c) (u (-c)) = u_{-c}(-1) u_c(1) u_{-c}(-1)` is the
  Weyl point of the root `c`, where `-c` is the index `P.reflectionPerm c c`;
- `G.innerIso n` is conjugation by a global point `n` (`Ad(n)`), and `f ≫ g` is
  composition, first `f`;
- `scaleHom r : 𝔾ₐ → 𝔾ₐ` is multiplication by `r` (module
  `LocalWeylNormalizationStatement`).

Let `R` be a commutative ring and `G`, `H` group schemes over `Spec R`. Let
`P : RootDatum J (I → ℤ) (I → ℤ)`, `b` a base of `P`, `W` a choice of a simple root and a
word of simple reflections for every root, and `u : J → (𝔾ₐ ⟶ G)`,
`u' : J → (𝔾ₐ ⟶ H)`. Write `v = weylFamily P W u`, `v' = weylFamily P W u'`,
`n_c = rootWeylPoint P u c` and `n'_c = rootWeylPoint P u' c`.
`WeylConjugationRelations P b W u u'` says: for every simple root `c` of `b` and every root
`d`, there is a unit `κ ∈ Rˣ` such that

- `v_d ≫ Ad(n_c) = scaleHom κ ≫ v_{s_c d}` in `G`, that is
  `n_c v_d(x) n_c⁻¹ = v_{s_c d}(κ x)`, and
- `v'_d ≫ Ad(n'_c) = scaleHom κ ≫ v'_{s_c d}` in `H`, with the same `κ`.

Here `s_c d` is the index `P.reflectionPerm c d`.

## Statement

`LocalSplitWeylConjugationStatement.{u}` says the following. Let `R` be a commutative local
ring, `I` a finite type with decidable equality and `J` a type (all in universe `u`). Let
`G`, `H` be reductive group schemes over `Spec R` with affine structure morphisms, and
`i : T_I → G`, `i' : T_I → H` closed (`IsClosedSubgroup`) coordinate split tori that are
maximal on every residue-field fibre (`IsFibrewiseMaximalTorus`). Let
`P : RootDatum J (I → ℤ) (I → ℤ)` be a fibrewise root datum of both `(G, i)` and `(H, i')`
(`IsFibrewiseRootDatumOf`). Let `b` be a base of `P` and `W` descending words
(`IsDescendingWords P b W`, from module `LocalSplitIsomorphismAssembly`). Let
`u : J → (𝔾ₐ ⟶ G)` and `u' : J → (𝔾ₐ ⟶ H)` satisfy, for every simple root `a` of `b`:

- `u a`, `u (-a)` are root parametrizations of `i` for `P.root a`, `P.root (-a)`, and
  `rootWeylPoint P u a` is a Weyl point of `i` acting by `P.reflection a` (`IsWeylPoint`);
- the same for `u'` and `i'`;
- `RankOneNormal i P u a` and `RankOneNormal i' P u' a` (module
  `LocalSplitRankOneNormalStatement`).

Then `WeylConjugationRelations P b W u u'` holds.

The first two hypotheses on `u`, `u'` are those of the published
`LocalSplitWeylCommutatorStatement` (module `LocalSplitIsomorphismAssembly`). The rank-one
hypotheses are the conclusion of the separate statement `LocalSplitRankOneNormalStatement`.

## Provenance and scope

This is an internal statement, written for this project. It isolates the Weyl-conjugation
input of the proof of the Isomorphism Theorem over an arbitrary local ring. In SGA 3,
Exp. XXIII, Theorem 2.1, condition (i), and Lemma 2.1.3, the compatibility
`int(f_N(w_α)) ∘ f_β = f_{s_α(β)} ∘ int(w_α)` of a homomorphism with conjugation by the
simple Weyl elements is what allows the commutation relations of all pairs of positive
roots to be reduced to pairs in rank-two subsystems. Conrad, *Reductive group schemes*
(2014), proof of Lemma 6.2.3, uses the same reduction. Here no homomorphism is given;
instead the statement asks that the conjugation units of the two Weyl families coincide.
Each unit exists separately, by rigidity of root parametrizations over a local ring
(module `LocalRootParametrizationRigidity`); the content of the statement is that the
units of `G` and `H` are equal in `R`, including when `R` has nilpotents. The expected
proof is a height induction in the style of SGA 3, Exp. XXI, Lemma 5.2, combined with
rank-two computations as in SGA 3, Exp. XXIII, 3.1–3.4. The statement is not proved here.
