# A torus norm presentation for the connected integral-point bound

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationStatement`
is an unproved prerequisite for the connected-model bound in
`UnramifiedTorusConnectedBoundStatement`. It isolates the norm-sequence
construction used in Kaletha–Prasad's proof of Corollary B.8.7.

## Source and provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Corollaries
B.8.6–B.8.7, printed pp. 682–683 / PDF pp. 713–714, is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
For a torus over the maximal unramified field `K`, the proof takes
`S = Res_{L/K}(T_L)` for a finite Galois splitting field `L/K` and uses the
norm `S → T`. Its full kernel is a torus, so B.8.6 applies. Since `T_L`
is split, `S` is induced; its bounded points correspond to the bounded
points of `T_L`, and their norm image is the Iwahori subgroup of
Definition 2.5.13.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, contain no amendment to B.8.6 or B.8.7; the Appendix B
corrections there concern B.10.

This is a **derived** existential formulation of that construction.
It specializes the base to `K = inertiaFixedField F` and retains precisely
the source-torus, surjectivity, full-kernel and bounded-image properties
needed to combine neutral integral-point lifting with the connected-model
bound. It does not identify the witness with a particular Weil-restriction
implementation or assert equality of the bounded-point image with the
Iwahori subgroup.

## Lean statement

At arbitrary universe `u`, take a nonarchimedean local field `F`, an actual
affine commutative group scheme `T` over `K = inertiaFixedField F`, and a
finite Galois intermediate field `L` of `SeparableClosure F / K` splitting
`T`. The proposition asserts the existence of:

1. An actual affine commutative group scheme `S` over `K` which is a torus.
2. An actual group-scheme homomorphism `q : S.toGrp ⟶ T.toGrp` whose
   underlying scheme morphism is surjective.
3. A torus certificate for the entire scheme-theoretic kernel `kernel q`,
   defined by the pullback along the unit of `T`.
4. The inclusion
   `map (S(K)^b) (q(K)) ≤ torusNormIwahori K L vL T`, where
   `S(K)^b = characterValuationKernel (fixedFieldValuation F) S.toGrp`
   and `vL = intermediateValuation F L`.

The character-valuation kernel imposes valuation one on the evaluation of
every rational character; it uses the actual rational-point group. The
right-hand subgroup is the image under `rationalNorm K L T` of the
character-valuation kernel of `T_L`. Thus the last assertion supplies an
actual bounded `L`-point whose norm is each indicated `q(K)`-image.

## Scope of the remaining proof

No geometric certificate or image inclusion is assumed about `S` or `q`;
all are conclusions. The intended construction uses the existing affine
Weil restriction of `T_L` and its algebraic Galois norm. Over `L` this
restriction is a product of copies of `T_L`, and the norm is their
multiplication, giving surjectivity and a torus full kernel. The canonical
rational-point comparison identifies the norm with `rationalNorm`.
Compatibility of character-valuation kernels with finite Galois scalar
extension and the counit of restriction then provides the required
bounded-image inclusion.

The statement supplies no smooth integral model and no lifting of neutral
integral points. Those are separate inputs to the connected-model proof.
