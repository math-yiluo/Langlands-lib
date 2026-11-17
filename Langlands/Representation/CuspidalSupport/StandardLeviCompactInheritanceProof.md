# Compact subgroups inherited by standard Levi subgroups

Module:
`Langlands.Representation.CuspidalSupport.StandardLeviCompactInheritanceProof`.
The exported theorem
`Langlands.CuspidalSupport.standardLeviCompactInheritance` has exactly the type
`Langlands.CuspidalSupport.StandardLeviCompactInheritanceStatement.{uF}`.
Its only universe parameter is the published field/group-scheme universe `uF`.
The target is imported from
`Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements`;
neither that module nor any of its dependencies is changed.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.10.6, the paragraph immediately before the Corollary,
printed pp.214–215 / PDF pp.220–221. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The author read PDF pp.219–221, including the preceding Theorem, Proposition,
inheritance sentence and Corollary. The internal lemmas below are derived group
and topology arguments implementing the published target; Renard does not give
this detailed proof in that paragraph.

The hypotheses and conclusion are exactly those of the published statement.
In particular, the topology on `G(F)` is `rationalPointTopology F G.X`;
`K₀` is compact, supplies the minimal Iwasawa factorization, contains `K`, and
normalizes `K`; and `K` has the literal ordered Iwahori decomposition along every
standard parabolic.

For each standard Levi `M_J`, the conclusion gives compactness and openness of
`K ∩ M_J` inside `M_J`, a compact subgroup of `M_J` containing and normalizing
`K ∩ M_J` and supplying its minimal Iwasawa factorization, and the ordered
Iwahori decompositions for every `I ⊆ J`. The proof constructs that compact
subgroup as `p_J(K₀ ∩ P_J)`, where `p_J` is the Levi projection. This is the
existential compact subgroup in the published statement. No assertion identifying
it with `K₀ ∩ M_J` is needed. The other two propositions in the target module,
concerning fixed vectors and Bernstein support, are outside this result.

## Generic subgroup arguments

All helper declarations in this module are private.

`iwahori_intersection` starts with a bijective ordered product for `K`
along subgroups `(L,U,V)`, in the order `V,L,U`. Suppose
`M ≤ P`, `L ≤ M`, `U ≤ P`, and every element of `V ∩ P` lies in `M`.
For `k ∈ K ∩ M`, take its original factorization `k = xyz`. Since
`y,z ∈ P`, the equation `x = k(yz)⁻¹` puts `x` in `P`, hence in `M`.
Then `z = (xy)⁻¹k` also lies in `M`. This proves surjectivity of the
restricted ordered product. Injectivity follows by forgetting the additional
membership proofs and applying injectivity of the original product.

`compact_levi_image` applies to a semidirect decomposition `P = M U` with
continuous projection `p : P → M`. It defines the ambient subgroup

```text
Q = (K₀.comap P.subtype).map (M.subtype.comp p).
```

Closedness of `P` and compactness of `K₀` make the preimage
`K₀.comap P.subtype` compact; its continuous image is compact and lies in `M`.
Given the ambient factorization `g = abc` of an element `g ∈ M`, where
`a` belongs to the minimal Levi and `b` to the minimal radical, the assumed
containments put `a,b` in `P`. Thus `c = (ab)⁻¹g` is in `P`, and projection
gives `g = a p(b) p(c)`. Projection preservation of the minimal radical
gives the required Iwasawa factorization in `M`.

The projection fixes `M`, so `K ∩ M ≤ Q`. To prove normalization, write an
element of `Q` as `p(c)` for `c ∈ K₀ ∩ P` and let `x ∈ K ∩ M`.
Then `cxc⁻¹ ∈ K ∩ P`, since `K₀` normalizes `K`. If projection preserves
`K ∩ P`, its image is `p(c)x p(c)⁻¹ ∈ K ∩ M`. The subgroup normalizer
criterion yields `Q ≤ normalizer (K ∩ M)`.

## Standard subgroup specialization

`rootSet_exists` uses `finite_simpleRoot` and the finite set of those simple
roots whose characters lie in `J` to express every
`J ⊆ simpleRelativeRoots i ν` as `rootSet i ν T`. This permits use of the
published finite-index topology and projection lemmas without changing the
set-indexed quantifiers of the target.

`standard_nested_structure` uses the published
`GroupScheme.standardLeviIntersection` for `I ⊆ J`. Its all-test Levi
containment gives `M_I ≤ M_J`. Its rational radical product gives

```text
N_I = (M_J ∩ N_I) N_J,
```

which implies `N_I ≤ P_J`.

For the opposite radical, `relativeRootNegation`,
`neg_mem_simpleRelativeRoots` and `IsGenericCocharacter.neg` allow the same
intersection theorem in the reversed chamber with faces `-I ⊆ -J`.
`standardSubgroups_reversedChamber`, using a standard cocharacter for `J`,
identifies the reversed Levi with `M_J`. Thus

```text
Nbar_I = (M_J ∩ Nbar_I) Nbar_J.
```

If `x ∈ Nbar_I ∩ P_J`, write `x = ab` in this order. Since
`a ∈ M_J ≤ P_J`, also `b = a⁻¹x ∈ P_J`.
The published
`eq_one_of_mem_standardOppositeUnipotent_of_mem_standardParabolic`
gives `b = 1`; hence `x ∈ M_J`. These three conclusions supply the
containments required by `iwahori_intersection`. This argument uses the
displayed product order directly.

`standard_projection_minimal` specializes the same rational radical product
to `I = ∅`. For an element `n = ab` of `N_∅`, with
`a ∈ M_J ∩ N_∅` and `b ∈ N_J`, the semidirect projection identity
`projection_mul` gives `p_J(n) = a`. Thus the projection preserves `N_∅`.

## Final assembly

The final theorem constructs the published
`Jacquet.standardBernsteinFamily i ν hG hi hν` and uses its semidirect
decomposition at the finite index for `J`.

Openness of `K ∩ M_J` is the preimage of the open set `K` under the continuous
subtype inclusion. For compactness the proof uses
`isClosed_levi_of_isNonarchimedeanLocalField` and compact preimage under the
closed subgroup embedding.

The compact-image helper uses
`isClosed_standard_parabolic`,
`continuous_standard_projection`, and
`Jacquet.standard_projection_mem_of_iwahoriIntersection`.
The last lemma proves preservation of `K` under the actual Levi projection
from the assumed Iwahori decomposition at `J`. The minimal cases of
`standard_nested_structure` and `standard_projection_minimal` supply the
remaining inputs. Finally, for each set `I ⊆ J`, the nested subgroup lemma and
the original Iwahori decomposition at `I` give the required restricted ordered
product by `iwahori_intersection`.

No additional premise, representation-theoretic assumption, proof hole or new
axiom is introduced.
