# Simultaneous dynamic realization of extension from a Levi

Authors: Worker 1291 and Worker 717.

Worker 717 supplied the explicit simultaneous P/Z/U realization interface
needed by its consumer; Worker 1291 wrote the proposition and documentation.

`DynamicLeviCocharacterRealizationStatement` is a proposition target.
For every connected reductive group scheme `G` over any field `k : Type u`,
any cocharacter `χ` of `G`, any closed representative `j : L → G` of
`Dynamic.centralizer χ`, and any cocharacter `ν` of `L`, it asserts the
existence of a cocharacter `ψ` of `G` such that, as actual subgroup functors,

- `P_G(ψ) = j(P_L(ν)) U_G(χ)`;
- `Z_G(ψ) = j(Z_L(ν))`;
- `U_G(ψ) = j(U_L(ν)) U_G(χ)`.

Here `P`, `Z`, and `U` are exactly `Dynamic.parabolic`,
`Dynamic.centralizer`, and `Dynamic.unipotent`. Each product is the
already defined `Dynamic.extendFromCentralizer`, whose carrier is the
literal two-factor product on each original test scheme. The image in the
middle equality is the existing actual `SubgroupFunctor.map`. The
equalities quantify implicitly over all test schemes, including nonreduced
ones, and do not mean merely equality on points over a field.

The hypotheses require no splitness of `G`, maximal split torus, root-system
classification, additional reductivity premise on `L`, or displayed
product formula. None of the three conclusions is assumed. The statement
also does not assume the parabolic correspondence. A proof may construct
`ψ` by combining the commuting ambient cocharacters `χ` and `ν ≫ j`
with a sufficiently dominant positive multiple of `χ`; the target does
not prescribe that construction.

On the identity test `Over.mk (𝟙 (Spec k))`, the same equalities give
the corresponding exact rational-point products and centralizer image.
`hj.rationalPointsEquiv` identifies the rational points of the represented
Levi with the actual centralizer subgroup. The elementary P/Z/U
image-intersection identities in `Dynamic.LeviParabolicDefinitions`
remain available for this same embedding and test. No topological claim
is part of this target.

This interface is a derived strengthening of the correspondence needed
to expose a compatible ambient dynamic triple to consumers of Renard
V.3.10–V.3.11, printed p.112/PDF p.118, and VI.1.4, printed
pp.136–137/PDF pp.142–143, in the edition dated 9 July 2026. Those passages
use chosen Levi and unipotent factors, and do not state this cocharacter
formula verbatim. Borel–Tits, *Groupes réductifs* (1965), Proposition
4.4(c), printed pp.86–87/PDF pp.33–34, supplies the full
parabolic-in-Levi semidirect correspondence motivating the first product.

Milne, *Algebraic Groups* (2017), §13.28–13.30, printed
p.264/PDF p.280, defines the dynamic parabolic, unipotent
functor and centralizer. Theorem 13.33, printed pp.265–266/PDF
pp.281–282, describes their smoothness, semidirect decomposition and
weight-space behavior; §25.1 and §25.6, printed pp.544–545/PDF
pp.560–561, places these factors in connected reductive groups over an
arbitrary field. The official errata snapshot of 2026-11-02 restricts
§25.6(b) to minimal parabolics. This statement uses the actual centralizer
of `χ`, not the centralizer of a maximal split torus for an arbitrary
parabolic, and uses no relative-root-system assertion affected by the
printed-p.549 warning.

The provenance is derived: simultaneous realization of all three exact
functors, together with arbitrary-universe and all-test quantification,
is an explicit Library target motivated by those structural and weight
descriptions. It is not claimed as a literal quotation, an implemented
construction, or a proved consequence of the correspondence. Its proof,
including simultaneous equality on every test scheme, is separate.
