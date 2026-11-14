# Conditional construction and base change of maximal central relative tori

Worker 673.

`MaximalCentralRelativeTorusReductionStatement` states an internal implication:
the relative reductive-centre theorem and the largest-subtorus theorem for
relative multiplicative-type groups imply existence and arbitrary base-change
stability of every maximal central relative torus of a reductive group. The two
structural statements remain explicit premises. This module does not prove
either premise or either central-isogeny conclusion of the host target.

The conclusion quantifies over every scheme `S`, reductive group `G`, every
maximal central relative torus `z : Z ⟶ G`, and every morphism `b : S' ⟶ S`
in universe `u`. Maximality means the greatest range among all closed central
relative tori, using the predicate of `MaximalCentralTorus`. After base change
the comparison includes all closed central relative tori over `S'`, including
ones that do not descend to `S`.

`maximalCentralRelativeTorusReduction` implements the implication. It applies
the centre premise to obtain a full scheme-theoretic centre `c : C ⟶ G` of
relative multiplicative type, then the largest-subtorus premise to obtain
`t : T ⟶ C`. The published factorization interfaces, via
`isMaximalCentralRelativeTorus_comp_center`, show that `t ≫ c` is maximal
central. The base-change clauses of the same two premises show that the
pullback of `t ≫ c` is maximal central over every `S'`.

For an arbitrary maximal central `z`, the range uniqueness lemma identifies
its range with that of `t ≫ c`. `SubgroupFunctor.range_baseChangeHom`
transports this equality after base change. Closedness, centrality and the
relative-torus property of the pullback of `z` follow from their independent
base-change lemmas. Its greatest-range property then follows from the
canonical pulled-back torus and the transported range equality.

The provenance is internal: this is a formal deduction from the named
prerequisite propositions and existing subgroup and base-change interfaces.
It makes no independent external literature assertion and introduces no
additional hypothesis on the base.
