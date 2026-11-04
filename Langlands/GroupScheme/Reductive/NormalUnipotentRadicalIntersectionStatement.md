# Unipotent radicals of normal connected subgroups

Worker 1372.

`Langlands.GroupScheme.NormalUnipotentRadicalIntersectionStatement` is a
proposition target at every universe `u`. Let `k : Type u` be an algebraically
closed field, let `G` and `H` be smooth connected affine group schemes over
`k`, and let `i : H ⟶ G` be a closed immersion with normal all-test range.
For any supplied representatives `r : U ⟶ G` and `s : V ⟶ H` of their
ground-field unipotent radicals, the target asserts

```text
(SubgroupFunctor.range r).comap i = SubgroupFunctor.range s.
```

This is an equality of subgroup functors on every scheme over `k`. The
left-hand side is the full scheme-theoretic intersection viewed inside `H`,
and the right-hand side is the full represented radical range. Neither side
is replaced by reduced points. The predicate `IsUnipotentRadical` includes
closedness, smoothness, connectedness, unipotence, normality, and greatest
all-test image containment among such subgroups. The target neither chooses
these representatives nor asserts their existence.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), Proposition A.4.8, printed pp.498–499 (PDF pages 524–525, zero-based
indices 523–524), source identifier
`conrad-gabber-prasad-2015-pseudo-reductive`. The source treats a field over
which the ambient ground-field radical agrees with the geometric radical,
and either a normal smooth connected subgroup or a torus centralizer.
Our target specializes the normal-subgroup case to an algebraically closed
field, where the geometric compatibility condition is automatic. It does
not state the torus-centralizer case or the source's further assertion
about semisimple quotients.

For the normal case the source first passes to the subgroup radical
quotient. It then shows that the commutator with the ambient unipotent
radical is both reductive and unipotent, hence trivial. The remaining
intersection is central and unipotent in the reductive subgroup, so its
multiplicative-type property makes it trivial. These structural arguments
are not proved in this module.

Two grouped conditional consequences use the target on supplied quotient
maps `q : G ⟶ Q` and `p : H ⟶ R`. They require exact all-test equalities
between the kernel ranges of these maps and the supplied radical ranges.
`kernel_comap_eq_of_normalUnipotentRadicalIntersectionStatement` substitutes
those equalities into the target to identify the inverse image of the
ambient full kernel with the subgroup full kernel.

`exists_normal_quotientSubgroupHom_of_normalUnipotentRadicalIntersectionStatement`
additionally assumes both quotient maps are flat, scheme-surjective and
quasi-compact, `R` is smooth connected affine, and `Q` is affine and locally
of finite type over `k`. It constructs a homomorphism `j : R ⟶ Q`
completing `i ≫ q = p ≫ j`, and proves that `j` is a closed subgroup
embedding with normal all-test range. The proof descends `i ≫ q` using
the published `quotientSubgroupHom`; the exact kernel inverse image gives
monicity. The published smooth-connected image theorem turns this
monomorphism into a closed immersion, and normality descends through the
fpqc square. These are internal consequences of the stated target and the
existing quotient interfaces.

The conditional consequence imposes the displayed quotient geometry; it
does not derive it from the kernel equalities. This module does not prove
`NormalUnipotentRadicalIntersectionStatement`, construct radical quotients
or compatible torus actions, prove their reductivity, or prove semigroup
intersection comparison.
