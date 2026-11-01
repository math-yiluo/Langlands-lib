# Signed type-A Solomon coefficients for block Weyl intersections

Author: Worker 379. The Lean proposition is the exact expression specified
by Worker 320 in the task contract, who also designed the source
dictionary below.

`Langlands.Geometric.TypeASolomonCoefficientStatement` is a proposition
with no parameters. It is a type-A form, written with the Library's actual
permutation data, of the Solomon identity that Aubert (1995) quotes after
equation (1.8). This module states the identity and proves nothing.

## The proposition

For every natural rank `n`, every ordered positive block shape
`B : BlockShape n` and every block shape `K : BlockShape n` with
`blockWeyl K ≤ blockWeyl B`, the proposition asserts

```text
∑_C (-1)^(n - C.length) · #{w ∈ MinimalRepresentatives B C |
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w) = blockWeyl K}
  = (-1)^(n - K.length)
```

as an equality of integers. Every ingredient is an existing Library
definition:

- `blockWeyl B` from `Geometric.WeylDefinitions` is the actual subgroup of
  `Equiv.Perm (Fin n)` of permutations that preserve the block of every
  coordinate, i.e. the Young subgroup `W_B` of the consecutive blocks of `B`.
- `MinimalRepresentatives B C` is the actual subtype of permutations `w`
  that are strictly increasing on each block of `B` and whose inverse is
  strictly increasing on each block of `C`.
- The sum runs over `Finset.univ` of `BlockShape n`, using the
  `Fintype` structure obtained by `Fintype.ofFinite` from the `Finite`
  instance of `CuspidalSupport.FiniteBlockShapes`. Every ordered positive
  shape `C` of rank `n` occurs exactly once. Because `Fintype` structures
  on a type are unique, the value does not depend on this choice.
- The coefficient of `C` is the integer cast of `Nat.card` of the actual
  subtype of `MinimalRepresentatives B C` cut out by the subgroup
  equality. This subtype is finite, so `Nat.card` is its number of
  elements. Every minimal permutation is counted individually; nothing is
  quotiented again, and no coefficient family or existence witness is
  supplied from outside.

## Subgroup orientation

For `w : Equiv.Perm (Fin n)`, `MulAut.conj w g = w * g * w⁻¹`. Hence
`g` lies in `(blockWeyl C).comap (MulAut.conj w).toMonoidHom` exactly
when `w * g * w⁻¹ ∈ blockWeyl C`, i.e. when `g ∈ w⁻¹ W_C w`. The tested
subgroup is therefore the source-side intersection

```text
W_B ∩ w⁻¹ W_C w  ⊆  W_B,
```

which is definitionally `intersectionSource (blockWeyl B) (blockWeyl C) w`
of `WeylDefinitions`. The proposition requires this actual subgroup to be
equal to the actual subgroup `blockWeyl K`; it is not a statement about
cardinalities of subgroups or about conjugacy classes of subgroups.

## Refinement hypothesis and signs

The hypothesis `blockWeyl K ≤ blockWeyl B` says that the Young subgroup of
`K` lies in that of `B`, i.e. that every block of `K` lies inside a block
of `B`: `K` is a standard refinement of `B`. No other hypothesis is
imposed. A shape `K` violating it cannot occur as an intersection, since
the intersection is contained in `W_B`.

A block of size `s` contains `s - 1` simple roots `e_a - e_{a+1}`, so a
shape of rank `n` contains `n - length` simple roots. Since
`length ≤ n` (`BlockShape.length_le`), the natural subtractions in both
exponents are exact. The summand sign `(-1)^(n - C.length)` is the source
sign `(-1)^|I|`, and the result `(-1)^(n - K.length)` is `(-1)^|K|`.

## Rank zero

At rank zero there is exactly one block shape, the empty one, and
`Equiv.Perm (Fin 0)` is trivial. The unique permutation is a minimal
representative, all three subgroups are the trivial group, and both signs
are `1`; the asserted identity reads `1 = 1`. This case is retained as the
elementary empty-root extension of the identity; it is not attributed to
the source, which works with a fixed reductive group. Rank one is the
source case of an empty set of simple roots.

## Source and derived correspondence

The source is Aubert, *Dualité dans le groupe de Grothendieck de la
catégorie des représentations lisses de longueur finie d'un groupe
réductif p-adique*, Trans. Amer. Math. Soc. 347 (1995), source
`aubert-1995-duality`. On printed p.2180 (PDF page 2) Aubert writes `W`
for the Weyl group, `S` for the simple roots, `L_I` and `W_I` for the
standard Levi subgroup and its Weyl group attached to `I ⊂ S`, puts
`L_I^w := w⁻¹ L_I w`, and defines

```text
𝒟(I, J) := {w ∈ W | w⁻¹(I) ⊂ Φ⁺ and w(J) ⊂ Φ⁺},
```

whose elements are the minimal-length representatives of the double
cosets `W_I w W_J`. On printed p.2182 (PDF page 4), after equation (1.8),
she fixes `K ⊂ J`, lets `a_{J,I,K}` be the number of `w ∈ 𝒟(I, J)` with
`L_J ∩ L_I^w = L_K`, and quotes a result of Solomon (via Carter,
Proposition 2.7.7):

```text
∑_{I ⊂ S} (-1)^|I| a_{J,I,K} = (-1)^|K|.
```

The present proposition is the derived specialization to the symmetric
group `W = Equiv.Perm (Fin n)` of `GL_n`, with simple roots
`e_a - e_{a+1}`. The dictionary is:

- A subset of simple roots corresponds to the ordered positive shape whose
  blocks are the maximal runs of coordinates joined by its roots, and its
  Weyl group `W_I` to `blockWeyl`. The source subset `J` is `B`, the
  summation subset `I` is `C`, and `K` is `K`; the sum over `I ⊂ S` is the
  sum over all shapes `C`. The inclusion `K ⊂ J` is the hypothesis
  `blockWeyl K ≤ blockWeyl B`.
- `w(e_a - e_{a+1}) = e_{w a} - e_{w (a+1)}` is positive exactly when
  `w a < w (a+1)`. So `w(J) ⊂ Φ⁺` says that `w` increases on each block of
  `B`, and `w⁻¹(I) ⊂ Φ⁺` says that `w⁻¹` increases on each block of `C`:
  `𝒟(I, J)` is `MinimalRepresentatives B C`, and its double cosets are
  `W_C \ W / W_B`.
- `L_J ∩ L_I^w = L_J ∩ w⁻¹ L_I w` is a standard Levi subgroup (Aubert's
  parenthetical remark under (1.3), printed p.2181, PDF page 3, citing
  Bernstein–Zelevinsky Lemma 2.11(b)), with Weyl group `W_J ∩ w⁻¹ W_I w`. A standard Levi
  subgroup `L_K` is determined by its Weyl group `W_K`, and conversely, so
  `L_J ∩ L_I^w = L_K` becomes the equality of actual subgroups
  `W_B ∩ w⁻¹ W_C w = W_K` above, in the same orientation.
- `|I|` is `n - C.length` and `|K|` is `n - K.length`.

The count `a_{J,I,K}` counts elements of `𝒟(I, J)`, one for each double
coset, which is the cardinality of the Lean subtype. The 1996 erratum
(`aubert-1996-duality-erratum`) concerns Proposition 3.2 and Theorem 3.6
only and does not affect this passage; no further correction for it is
recorded in the project literature, Library or notes. Carter's book is not
registered in the project literature and was not consulted.

## Scope

This finite identity is a lower input for a formal proof of induction
compatibility of Aubert's alternating operator: in the source it turns
(1.8) into `D_G ∘ i_{L_J} = i_{L_J} ∘ D_{L_J}`, the first identity of
Theorem 1.7(2). The proposition is purely combinatorial. It assumes no
field, topology, positivity, cuspidality or classification input, and is
not a statement about an abstract Coxeter datum. It proves neither the
geometric lemma (1.3) nor any representation-theoretic duality identity,
and it supplies no irreducibility, irreducible-image or classification
result.
