# The rational classification of standard parabolics from its structural inputs

This unit assembles `StandardParabolicClassificationStatement.{u}` (Milne 2017,
25.23; Borel–Tits §5.14) from six published structural statements, which are
still unproved. They are taken as explicit premises:

- `SmoothMaximalSplitTorusConjugacyStatement.{u}`: maximal split tori of a
  smooth connected affine group are conjugate by a rational point.
- `DynamicConnectedStatement.{u}`: representatives of dynamic unipotent
  subgroups are connected, and for connected `G` so are representatives of
  dynamic parabolics and centralizers.
- `RelativeRootSystemStatement.{u}`: `HasRelativeRootSystem i`, i.e. the
  relative roots form a finite crystallographic root system on the rational
  root span whose Weyl group is the image of the injective relative Weyl
  action.
- `RelativeRootSignInclusionsStatement.{u}`: the root-sign criterion for
  inclusions of dynamic parabolics (and unipotent subgroups) of cocharacters
  of `T`.
- `RelativeTitsSystemStatement.{u}`: `HasRelativeTitsSystem i ν` for generic
  `ν`.
- `StandardParabolicOrderStatement.{u}`: inclusion of standard parabolics
  matches inclusion of subsets of `Δ` (with the corresponding Levi and
  unipotent inclusions), and `J ↦ P_J` is injective.

Smoothness of dynamic subgroups is not a premise. It is the published theorem
`dynamicSmooth`. Negation stability of the relative roots is derived from the
root-system premise through the published
`relativeRootNegationStatement_of_relativeRootSystemStatement`.

The unit does not prove `StandardParabolicClassificationStatement`
unconditionally. It shows that the six statements above suffice. Once each is
proved, applying the final theorem to those proofs gives the target.
Minimal-parabolic conjugacy (`MinimalParabolicConjugacyStatement`), the generic
minimal-parabolic statement and `ParabolicDynamicStatement` are not used.

## Setting

`k : Type u` is an arbitrary field. `G` is a group scheme over `Spec k` with
`IsConnectedReductive G`, and its affine instance is `hG.isAffineHom`, as in
the target. `i : T.toGrp ⟶ G` is a maximal split torus (`IsMaximalSplitTorus i`)
and `ν` is a generic cocharacter of `T`. Cocharacters `zeta` of `G` are
homomorphisms `Gm ⟶ G`. Inclusions and equalities of subgroup functors hold on
every test scheme.

## Declarations

- `exists_conjugate_parabolic_containing_generic_of_chamber` (premises: torus
  conjugacy, root system, root-sign criterion). For every cocharacter `zeta`
  there is a rational point `g` with
  `P(groupHom ν ≫ i) ≤ P(zeta ≫ (G.innerIso g).hom)`.
  - First, the published `exists_innerIso_comp_eq_cocharacter`
    (`Rational/ParabolicCocharacterConjugacy`) gives `g` and a cocharacter `ξ`
    of `T` with `zeta ≫ Int(g) = groupHom ξ ≫ i`.
  - Next, `exists_normalizerPoint_parabolic_le_of_statements`
    (`Rational/DominantChamberMove`) gives a normalizing point `n` with
    `P(groupHom ν ≫ i) ≤ P((groupHom ξ ≫ i) ≫ Int(n))`.
  - The witness is `n * g`, because
    `Int(n * g) = Int(g) ≫ Int(n)` (`innerIso_mul_hom`).
- `conjugatingPointToGenericOvergroup` (definition): that point, chosen by
  `Classical.indefiniteDescription` and bundled with its containment.
- `exists_standardParabolic_eq_of_parabolic_le_of_structural_statements`
  (premises: torus conjugacy, dynamic connectedness, root-sign criterion,
  root negation). If `P(groupHom ν ≫ i) ≤ P(zeta)`, then
  `P(zeta) = standardParabolic i ν J` for some `J ⊆ simpleRelativeRoots i ν`.
  - The published `exists_parabolic_eq_cocharacter_of_parabolic_le`, with
    `dynamicSmooth`, replaces `zeta` by a cocharacter `ξ` of `T` with the same
    dynamic parabolic.
  - The published `exists_standardParabolic_eq_of_parabolic_le_of_statements`
    (`Rational/CocharacterStandardFace`) then identifies `P(groupHom ξ ≫ i)`
    with the standard parabolic of its simple-root face.
- `standardParabolicClassificationStatement_of_structural_statements`: the
  exact proposition `StandardParabolicClassificationStatement.{u}` from the six
  premises. It applies the published `standardParabolicClassification_of_local_inputs`
  (`Rational/StandardParabolicClassificationReduction`) to four inputs:
  - the standardness theorem above;
  - the conjugation theorem above;
  - injectivity of `J ↦ standardParabolic i ν J`, the second component of
    `StandardParabolicOrderStatement`;
  - rigidity under rational conjugacy, the published
    `standardParabolic_eq_of_isRationallyConjugate_of_statements`
    (`Rational/ParabolicConjugacyRigidity`), from the Tits-system and order
    statements.

## Provenance

The unit is derived. It is a pure assembly of Library results and introduces
no mathematical content of its own. The route follows the dependency structure
recorded in the Markdown of the imported units:

- standardness comes from torus conjugacy and the root-sign criterion;
- conjugation into an overgroup of `P(ν)` comes from torus conjugacy and the
  relative Weyl group move into the closed dominant chamber;
- uniqueness comes from the Tits system and the order of standard parabolics.

The classical statement is Milne, *Algebraic Groups* (2017), 25.23 (printed
p. 550; one-based PDF p. 566). For a minimal parabolic `P` and a maximal split
torus `S` in `P`, the `P_I` for subsets `I` of the base defined by `P` "are the
standard parabolic subgroups of G containing P. Every parabolic subgroup is
conjugate by an element of G(k) to a unique P_I." The preceding 25.22 (same
page) gives the relative Weyl group action on the minimal parabolics
containing `S`, which motivates the chamber move. The target's own Markdown
cites Borel–Tits (1965), §5.14 (printed pp. 99–100) for the same result over
an arbitrary field.

The official errata (snapshot of 2026-11-02) have no entry for 25.22 or 25.23.
Two nearby entries concern this material:

- '*p.545 et seq.' says that in 25.6(b), in the final sentence of 25.24 and in
  25.27 the parabolic subgroup should be minimal. 25.23 applies 25.6 only to a
  minimal `P`, and this unit uses neither 25.24 nor 25.27.
- 'p.549' says that the classical proofs that the relative root system of 25.16
  is a root system are incomplete, and refers to CGP C.2.15. Here that
  assertion is the explicit premise `RelativeRootSystemStatement.{u}`.
