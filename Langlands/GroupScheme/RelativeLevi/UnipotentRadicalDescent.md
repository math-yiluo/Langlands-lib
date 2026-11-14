# Cover transport for relative unipotent radicals

This internal supporting module derives cover transport from the published
relative radical predicate, field-radical transport, and fpqc reflection.
The base schemes and universe are arbitrary. The ambient group is affine over
the base.

`IsRelativeUnipotentRadical.baseChange_etale` preserves a supplied relative
radical under an etale morphism. Closedness, smoothness and all-test normality
are preserved by pullback. At each point of the new base, etaleness makes the
residue extension separable algebraic. The two chosen algebraic closures are
therefore isomorphic over the old residue field. The proof transports the
field radical along this field isomorphism and the natural pullback comparison.

`IsRelativeUnipotentRadical.of_baseChange` reflects the predicate under an
fpqc morphism, assuming the original inclusion is closed. Smoothness and
all-test normality reflect by the existing fpqc lemmas. For each base point,
surjectivity supplies a point above it. An embedding of the chosen old
algebraic closure into the new one compares the two actual geometric fibre
inclusions. The published field-radical reflection lemma then supplies the
old fibre's complete radical predicate.

`RelativeLevi.etaleBaseChangeRadical` returns the actual pullback group scheme,
its pullback inclusion into the ambient group and the full relative radical
certificate supplied by `baseChange_etale`.

These are internal consequences of existing interfaces; they do not assert
existence or uniqueness of a relative radical and do not require the dynamic
relative Levi theorem.
