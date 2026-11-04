# Actual uniformizer charts modulo the full rational-point center

`RationalPointFamily.RationalFiniteChamberCartanCoverStatement` is an internal
adapter at general connected-reductive scope over every nonarchimedean local
field, in either characteristic. It uses the literal `SimpleRoot i ν` labels,
actual uniformizer evaluation `uniformizerPowers i` and the canonical rational
point topology. The displayed finite-type structure on the simple-root labels
may be any choice; such a structure exists for the stated maximal split torus.
The chosen cocharacter `ν` is assumed generic, through
`hν : IsGenericCocharacter i ν`. A proof
`hStandard : StandardCocharacterStatement.{u}` is also supplied. This is a
global structural proposition providing standard-cocharacter existence and
the dynamic-subgroup comparisons; it is a separate premise from the actual
geometric witness described below.

Fix the actual apartment data `D`, its point `x`, a group scheme `Z`, maps
`j : Z → G` and `s : S → Z`, and bijectivity `h` of actual character-restriction
evaluation, with `s ≫ j = i`. Assume the same compact subgroup `D.specialCompactSubgroup x`
satisfies `SpecialCompactProperties`, and assume the actual
`SpecialCompactStandardLeviCompatibility D x ν s h j`. For every supplied
finite lattice transversal `F₀`, the conclusion constructs diagonal
cocharacters `gen α` with positive own simple-root pairing and all other
pairings zero, and one finite set `T` of actual group points. Every group
point has the form

`g = k₁ * uniformizerPowers i (∑ α, n α • gen α) * t * k₂ * z`,

with natural coordinates, both compact factors in the specified subgroup,
`t ∈ T` and `z` in the **full abstract center** of the actual group `G(F)`.
If the simple-root type is empty, the conclusion also gives compactness of
that actual full central quotient with its canonical quotient topology.
No splitness or quasi-splitness of `G` is imposed.

This is a derived adapter. The full-index Levi is the whole group by
`RationalPointFamily.levi_univ_eq_top`, using both `hStandard` and `hν`.
The standard-cocharacter premise also supplies the standard vectors used
to obtain diagonal generators and the common-kernel comparison.
The actual Cartan cover
comes from the supplied same-compact Levi compatibility. Character-normalized
valuation on a uniformizer cocharacter is `1 ⊗ c`, so finite lattice
translates give a common lower bound on simple-root pairings. The published
commutation lemma makes the common pairing kernel central in the whole
group. Finite orthant decomposition then gives the displayed charts; when
the labels are empty the generator sum is zero and compact representatives
surject onto the full central quotient.

Genericity of `ν`, the supplied global standard-cocharacter proposition,
the apartment, special-compact properties, restriction comparison,
same-compact Levi compatibility and finite transversal remain explicit
geometric inputs. This statement does not construct the joint geometric
witness, prove it for arbitrary weak apartment data, or discharge that
existence obligation in the host strict Jacquet criterion. It states no
Haar-volume or coefficient estimate and no square-integrability conclusion.
