# Product-Levi tempered sufficiency from Jacquet exponents

Author: Worker 544, with Worker 23, whose task supplied the Lean formulations.

This module defines two closed propositions, each with independent field and
representation universes `uF` and `uV`:

- `Langlands.GLProductLeviTemperedExponentSufficiencyStatement` is the upper
  generalized-exponent core statement.
- `Langlands.GLProductLeviDualOppositeTemperedSufficiencyStatement` is the
  opposite-Jacquet dual-eigenfunctional statement used by consumers.

These are `Prop`-valued definitions. Neither proposition is proved here.

## Common hypotheses and analytic conclusion

Both statements quantify every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, every compatible realization `T : F.TopologicalData`,
every positive rank `n`, and every ordered block shape `C : BlockShape n`.
The topology is `T.topology`. The group is the actual product Levi
`M_C = C.Levi F.Carrier`, whose factors are `GL_(C.size j)(F)`.

The bundled complex representation `S : Rep.{uV} ℂ M_C` must be irreducible
and admissible. Admissibility includes smoothness. A prescribed character
`ω : (Fin C.length → F.Carrierˣ) →* ℂˣ` satisfies
`Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) ω`,
meaning that each tuple of scalar matrices acts by `ω`. Its norm is one at
every tuple. The statement does not separately assume openness of `ω.ker`:
its openness follows from smoothness and a nonzero vector. The identification
of all central elements of a positive-size GL factor with scalars is part of
the mathematical translation, rather than an additional hypothesis.

Under the relevant exponent hypothesis, the conclusion is
`IsTemperedModCenter S.ρ μ` for every Borel measurable structure on
`Q = M_C ⧸ Subgroup.center M_C` and every Haar measure `μ` on `Q`.
`T.leviTopologicalGroup C` supplies the product group topology. The published
predicate requires admissibility, a unitary central character with open
kernel, and that every descended absolute smooth matrix coefficient belong
to `L^(2+ε)(Q, μ)` for every real `ε > 0`. Thus the conclusion concerns the
whole product Levi and the actual full centre. It retains every choice of
Borel Haar measure.

## The upper core hypothesis

A refinement `D : BlockRefinement C` selects an ordered block shape `D j`
inside each outer block `j`. All refinements are quantified, including the
identity refinement. Write `B = C.flatten D` and
`e(j,k) = C.flattenBlockEquiv D ⟨j,k⟩`. The constructed equivalence
`flattenedLeviEquiv F.Carrier C D` identifies `B.Levi F.Carrier` with the
actual refined Levi subgroup of `M_C`. Restrict
`T.normalizedRefinedJacquet C D S.ρ` along that map and then along
`B.blockScalarLevi F.Carrier`.

For every character `ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with open kernel
that is a generalized eigencharacter of this restriction, require
`‖ψ(a)‖ ≤ 1` whenever

```text
|a_(e(j,0))| ≤ |a_(e(j,1))| ≤ ...
```

holds separately for each `j`. Here `|·| = T.normalizedAbs`, and the Lean
condition uses `Monotone` on `Fin (D j).length`. There is no comparison between
different outer blocks. `IsGeneralizedEigencharacter` means that some nonzero
vector is killed by a single power of every character-defect operator; the
power is uniform in the scalar tuple and may depend on the vector and `ψ`.
This is precisely the exponent convention of the published
[`GLTemperedExponentCriterionStatement`](TemperedExponentStatement.md),
now inside each outer block.

The upper action uses inverse upper half-modulus. On fine block scalars its
explicit full modulus is

```text
δ_D(a) = product_j product_(k<l)
           |a_(e(j,k)) / a_(e(j,l))|^((D j).size k * (D j).size l).
```

If `r` is the real part in block-scalar coordinates, the chamber bound is
equivalent to nonnegative prefixes within each outer block and zero total
there. These are scalar exponents: determinant exponents `t_(j,k)` give
`r_(e(j,k)) = (D j).size k * t_(j,k)`. Unweighted sums of determinant exponents
would describe a different condition.

## The dual-opposite hypothesis

For every refinement `D`, every open-kernel character `ψ`, every real vector
`s`, and every nonzero functional

```text
φ : Module.Dual ℂ (Geometric.RefinedOppositeJacquetModule C D S.ρ),
```

assume the eigen-equation

```text
φ(Jbar_D(m(a)) q(v)) = ψ(a) φ(q(v))
```

for all fine scalar tuples `a` and source vectors `v`. Here `q` is
`refinedOppositeJacquetMk C D S.ρ`, `m(a)` is the image of the flattened block
scalar through `flattenedLeviEquiv`, and `Jbar_D` is
`T.normalizedRefinedOppositeJacquet C D S.ρ`. The quotient map is surjective,
so this is the eigenfunctional condition on the entire quotient. The dual is
the full algebraic dual. The displayed action is transposition, without
inverting or conjugating the character, as in the published
[`Exponents.DualJacquet`](../Exponents/DualJacquet.md).

`T.IsRealPartOf ψ s` means exactly
`‖ψ(a)‖ = product_b |a_b|^(s_b)` for every `a`. The conclusion required by the
hypothesis is

```text
sum_(k≤i) s_(e(j,k)) ≤ 0
```

for every outer block `j` and every inner index `i`. This includes the full
prefix. Zero totals are not extra hypotheses. On scalars constant within one
outer block the refined modulus is trivial and the quotient action is that
of `ω`. The eigen-equation and `φ ≠ 0` therefore imply that the norm of `ψ`
on those scalars is one. Testing a uniformizer gives
`sum_k s_(e(j,k)) = 0`. The same central argument applies to upper generalized
exponents.

## Relation between the two forms (derived, not proved here)

Conjugation by the long Weyl element within each factor of `M_C` takes the
inner opposite parabolic of `D` to the standard upper parabolic with its
inner blocks in reverse order. The opposite action uses positive upper
half-modulus, exactly as proved by `normalizedRefinedOppositeJacquet_mk`;
after conjugation this is the inverse half-modulus for the reversed upper
parabolic. The representation conjugated by this element is equivalent to
`S`, through its actual group action.

Admissible Jacquet modules have finite-dimensional compact-open invariant
spaces. Restriction of a nonzero eigenfunctional to a suitable such space
detects its character among the generalized eigencharacters. Conversely,
a generalized eigencharacter is visible on a finite-dimensional invariant
space; a dual eigenvector there extends by compact-open averaging, which
commutes with the central scalar action. This explains why exponent-one
functionals in the consumer form test the generalized spectrum of the core
form. Existence of real parts for all open-kernel characters of `(Fˣ)^r`
uses the compact unit group and the uniformizer decomposition. These
representation-theoretic and character facts remain proof obligations.

Reversing a zero-total vector `s` turns its nonpositive prefixes into
nonnegative prefixes. Equivalently, summation by parts shows that nonpositive
prefixes with zero total imply `sum_k s_k log|a_k| ≤ 0` on decreasing absolute
values, the opposite chamber. Reversal transports this to the core's
increasing chamber. There is no extra negation of the character caused by
the algebraic dual. A future consumer proof may therefore import the core
proof together with this adapter. No equivalence of the two conditions is
asserted as a Lean theorem in this file.

## GL₂ sign check

This is an explanatory calculation using the published upper convention and
the task's opposite convention, not an implemented Lean theorem about these
representations. Set `C = (2)` and refine to `D = (1,1)`.

| Representation | Upper scalar real part | Opposite scalar real part | Opposite prefixes |
| --- | --- | --- | --- |
| Steinberg `St₂` | `(1/2, -1/2)` | `(-1/2, 1/2)` | `-1/2, 0` |
| Trivial representation | `(-1/2, 1/2)` | `(1/2, -1/2)` | `1/2, 0` |

For `St₂` the upper exponent has norm `|a₁/a₂|^(1/2)`, at most one on
`|a₁| ≤ |a₂|`, and both opposite prefixes are nonpositive. For the trivial
representation the upper norm is `|a₁/a₂|^(-1/2)`. Taking `a₁ = ϖ`, `a₂ = 1`,
with `|ϖ| = q⁻¹ < 1`, gives `q^(1/2) > 1`. Its first opposite prefix is also
positive. Thus the non-tempered trivial representation violates both
hypotheses. The other refinement is `(2)`, where both representations have
unitary central character and the single real exponent is zero. These are
all refinements of `(2)`, so the tempered `St₂` satisfies both hypotheses.

## Original sources and the product-Levi translation

- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
  d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.
  Literature ID `waldspurger-2003-plancherel`, SHA256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
  Proposition III.2.2, printed pp.265–266 (PDF31–32), is the tempered
  exponent criterion for admissible representations of connected reductive
  groups. Section I.3, p.243 (PDF9), defines generalized exponents and
  inverse-half normalized Jacquet modules. Sections I.1, pp.239–241
  (PDF5–7), define the cones, the sign of `H`, and the Cartan volume estimate.
- A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
  groups*, Princeton University Press and University of Tokyo Press, 1979.
  Literature ID `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  Section 4.5, p.184 (PDF190), defines tempered representations through
  their coefficients; Lemma 4.5.3, pp.185–186 (PDF191–192), gives the weak
  exponent bound for functions and their constant terms.

The cited passages were read directly; the formula-bearing criterion pages
were also checked as images. No source-specific errata files were found in
the project/public notes. Casselman 1995 Theorem 4.4.6 is not used as a source
for this tempered statement: it is the square-integrability criterion.

Apply Waldspurger's criterion to the reductive group `M_C`. Its standard
parabolics are products of the standard parabolics in the factors, hence
are exactly the refinements `D`. Its centre is the product of the scalar
centres, and its roots and chambers compare fine coordinates only inside
each outer block. This product-Levi specialization, the flattened coordinate
maps, and the dual-opposite adapter are derived translations, not literal
statements in those sources.

Waldspurger and Silberger define temperedness through a bound by
`Ξ(g)(1+σ(g))^r`. The Library uses `L^(2+ε)` modulo the centre. For the
sufficiency direction needed here, Waldspurger's I.1(5), p.241, and Lemma
II.1.1, p.251 (PDF17), bound the Cartan-cell integral of a coefficient's
`(2+ε)`-power by a polynomial times exponentially decreasing lattice terms
on the chamber modulo the centre. The resulting series converges for every
`ε > 0`; this adapts the series argument of Lemma II.1.5, p.252 (PDF18).
The coefficient norms descend by unitarity and are locally constant.
Scaling Haar measure does not change integrability. This is a derived
analytic bridge, not a proof supplied by this statement module; the exact
all-Haar-measure conclusion must be proved by its proof successors.

## Dependencies and remaining scope

The imports provide `IsTemperedModCenter`, `HasScalarCharacter`, generalized
eigencharacters and real parts, the actual upper and opposite refined
Jacquet quotients, and the constructed flattened Levi and index
equivalences. No tensor presentation, cuspidal support, finite set of
refinements, or square-integrability assumption is added to either target.
The file does not prove the exponent criterion, the analytic bridge, the
spectral adapter, or their identification with the explicit Library moduli.
A factorization-based core proof may use the published Levi factorization,
the GL exponent criterion proof and a tensor-temperedness proof; those are
separate obligations. Both statement declarations are intended for exact
inspection in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
