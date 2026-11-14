# Full ordinary derivatives of actual quasi-split apartments

`Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsStatement`
is an unproved proposition. For every universe `u`, it quantifies over a
field `k : Type u`, a surjective valuation
`v : Valuation k (WithZero (Multiplicative ℤ))`, and henselianity of
`v.valuationSubring`. For each actual quasi-split affine group `G/k` and
prescribed actual maximal split torus `i : S → G`, it quantifies over
every `D : KPApartmentData i (IntegerValuation.order v)` and actual
centralizer datum `C : CentralizerDatum i` satisfying full
`IntegerValuation.IsOmegaCompatible v D C`.

The conclusion is the equality
`AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i)`.
Here `D.affineRoots` is the set of ordinary affine roots defined by
nontrivial jumps modulo the doubled-root subgroup. Its derivative set
consists of their linear parts. The right side consists of the real
linear forms of all actual relative roots of `(G,S)`, namely the
nonzero weights in the adjoint Lie representation, on the actual reduced
translation space. The equality includes multipliable and doubled
relative roots. It is not an assertion about only the extended affine
roots or about a reduced subset of the relative roots.

`IsQuasiSplit G` includes connected reductivity and a field-defined
geometric Borel. The monomorphism instance for `i` is deduced from its
maximal split torus hypothesis. `D` is an actual normalizer-stable
equipollence class of valuations on the rational root groups, and
`IsOmegaCompatible` is the full V6 identity for the actual centralizer.
There is no hypothesis of local compactness, completeness, perfect
residue field, residue cardinality, characteristic, reducedness, an
affine-root-system axiom package, or absolute maximality of `i`.
In particular, the target applies before proving splitting over the
henselian maximal unramified field.

This file proves no derivative equality. The assertion is separate from
`QuasiSplitIndivisibleDerivativeLiftsStatement`, which asks for lifts of
derivatives already present and therefore does not ensure that every
relative root occurs. It also differs from the full derivative equality
for extended affine roots and the local-field V7 theorem for ordinary
affine roots. It does not prove `LocalAnisotropicAffineDiagramStatement`.

## Derived source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Chapter 6. Its opening paragraphs (printed pp.195–196,
PDF pp.226–227) assume a henselian discretely valued field normalized
to have value group `ℤ` and permit imperfect residue fields.
Surjectivity of `v` expresses this normalization in multiplicative
notation. Definition 6.3.4 (printed p.218, PDF p.249) gives the ordinary
affine roots used in the conclusion.

Section 6.4 (printed pp.223–226, PDF pp.254–257) concerns the canonical
apartment of a quasi-split reductive group. Definition 6.4.3 introduces
the jumps `J_{a/2a}` of the root filtration modulo the doubled-root
group. The displayed identity following that definition identifies
the ordinary affine roots of derivative `a` with `a + J_{a/2a}` at an
adjusted Chevalley origin. Fact 6.4.5 makes each such jump set nonempty,
including the multipliable cases. Proposition 6.4.8 explicitly concludes
that both the ordinary and the auxiliary affine roots have derivative
root system `Φ`. Its proof passes to the adjoint group, takes simple
factors, and uses restriction of scalars; these reductions must preserve
the identification with the actual relative-root forms. Only the
ordinary-root conclusion is requested here.

The target quantifies over every compatible `D`, whereas §6.4 computes
the canonical class. Proposition 6.2.6 (printed p.216, PDF p.247)
identifies the compatible class. The Library theorem
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus`
in `IntegerOmegaApartmentUniqueness` proves the integer-valued
uniqueness implication for two full-V6 classes with the same torus and
centralizer datum. A proof of this target must construct the canonical
class, establish full compatibility, compare any centralizer
representations, and transport the derivative equality to the arbitrary
`D`. These are proof obligations, not extra premises. Translation of the
chosen origin preserves the linear parts.

The authors' *Corrections and additions* (2024), PDF p.32, replace the
derived-group construction of §6.1(c) and Definition 6.1.27 with the
adjoint-group construction. They also correct the type notation in
Remark 6.4.7. They do not alter Fact 6.4.5 or Proposition 6.4.8 there.
The corrected adjoint reduction is required for the reductive scope
of this target.

This formulation is derived from the canonical source result and its
uniqueness comparison, rather than transcribed verbatim. The registered
sources are `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
and `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
