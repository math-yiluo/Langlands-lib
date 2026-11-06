# Actual cocenter characters from compatible derived tori

Author: Worker 1293.

This internal adapter composes published geometric and lattice results. It
does not prove the existence of a Levi root model or the structural inputs
retained below.

`cocenter_cocharacter_surjective_of_product_of_intersection` concerns an actual
derived inclusion `d : D → M`, torus map `t : T → M`, and supplied commutative
fppf quotient `q : M → Q` by the full range of `d`, over an arbitrary field.
The source and quotient tori are split. The explicit geometric premises are
scheme surjectivity of the ordered product `D × T → M` and the torus property
of the entire scheme-theoretic intersection `T ×_M D`. No maximality is
required in this first result.

The derived subgroup maps trivially into the commutative quotient. Product
surjectivity and quotient surjectivity therefore make the actual restriction
`T → Q` scheme-surjective. The published torus epimorphism theorem makes it
an epimorphism of group schemes. Its full kernel is the supplied intersection,
which is a smooth connected torus. The published split-torus theorem with
smooth connected full kernel now gives surjectivity on integral cocharacters.

`characterLattice.cocenterCorootAnnihilatorEquiv` additionally takes a compatible
split maximal torus `a : S → D` and its actual map `φ : S → T`, with the exact
commuting square. Here `t` is a closed inclusion, and `D` is explicitly
semisimple. A supplied actual root datum `R` for `a` has finite root index by
the published semisimple necessity theorem. Its root index set is finite by
actual weight-support finiteness, and perfect pairing converts finite root
index into finite coroot index.

A root datum `P` on the actual lattices of `T` has the actual character and
cocharacter pairing. A subset `s` of its root indices is supplied, together
with the explicit equality between the image of the integral `R` coroot span
under `φ` and the span of the `s`-indexed coroots of `P`. The full-intersection
comparison identifies the actual integral cocharacter kernel of `T → Q`
with the image of `S`. The first result supplies cocharacter surjectivity, and
the published finite-index coroot comparison constructs

`X*(Q) ≃ₗ[ℤ] {χ ∈ X*(T) | χ annihilates the s-indexed coroots of P}`.

The underlying map is actual precomposition along `t ≫ q`. Finite coroot
index supplies saturation through nonzero integral multiples; it does not
assert that coroots generate the full integral cocharacter kernel.

The field universe and the two root-index universes are independent. This
adapter does not require algebraic closedness, perfectness, simple
connectedness or a characteristic restriction. It does retain splitness of
the three tori, semisimplicity of the supplied derived subgroup, the full
intersection torus premise, actual product surjectivity and the actual
coroot-span comparison. It constructs no root datum, compatible torus, base,
simple subset, splitting extension or Galois correction. Those remain
obligations of `SplitTorusCentralizerCocenterRootModelStatement`.
