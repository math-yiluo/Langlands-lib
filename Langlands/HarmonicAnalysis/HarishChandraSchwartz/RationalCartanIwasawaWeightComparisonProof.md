# The actual Cartan-to-Iwasawa weight comparison

`Langlands.HarishChandraSchwartz.rationalCartanIwasawaWeightComparison` proves
`RationalCartanIwasawaWeightComparisonStatement.{u}` at arbitrary universe
`u`. Let `P₀` be the minimal standard parabolic, `U₀` its unipotent radical,
and `δ₀` the Haar modulus for forward conjugation on `U₀(F)`. For each
dominant uniformizer power `a = ϖʸ` and each `g` in its Cartan cell, the
theorem compares the actual square-root Iwasawa weights at `a` and `g`.

The proof represents `P₀` and `U₀` by the dynamic subgroups of the generic
cocharacter. The Haar determinant formula identifies the modulus on the
centralizer with the residue-normalized absolute value of its determinant
on `Lie U₀`. The scalar identification follows by comparing the Haar
scaling of the compact open valuation ring under multiplication with the
scalar Haar scaling formula. On the parabolic, the limit map gives the
centralizer component. The Haar modulus is trivial on the remaining
unipotent factor, and the determinant character is the pullback of its
restriction to the centralizer.

Choose homogeneous coordinates for the action of `S` on `Lie G`, and let
`d = dim Lie U₀`. The multiplicity of each weight of `Lie U₀` equals its
multiplicity in `Lie G` when its pairing with the generic cocharacter is
positive, and is zero otherwise. Thus the torus determinant on `Lie U₀`
is the product of the characters of the positive basis weights. Dominance
and relative-root negation give absolute values at least one for those
weights on `a⁻¹`, and at most one for the other weights. Each diagonal
coefficient of `∧ᵈ Ad(a⁻¹)` is a product indexed by a subset of the basis.
Its absolute value is bounded by the product over the positive weights,
which is `δ₀(a⁻¹)`. The actual exterior coordinates of `Lie U₀` give a
nonzero vector of this representation on which `P₀(F)` acts by the same
determinant character.

Write `g = k₁ a f k₂ = p k` with `p` the chosen Iwasawa factor. Since `f`
centralizes `a`, one has `p⁻¹ = (k k₂⁻¹) a⁻¹ (k₁ f)⁻¹`. Both outer factors
range in compact sets, using the finiteness of the family of centralizer
points. A common bound `C ≥ 1` for their exterior matrix entry norms and
ultrametric submultiplicativity bound the norm at `p⁻¹` by
`C² δ₀(a⁻¹)`. Applying the operator to the nonzero determinant vector and
cancelling its norm gives `δ₀(p⁻¹) ≤ C² δ₀(a⁻¹)`. Multiplicativity and square
roots then give `φ_K(a) ≤ C φ_K(g)`. The proof identifies `φ_K(a)` by the
factorization `a = a · 1` and triviality of the modulus on `P₀(F) ∩ K`.

The argument follows the determinant-line and compact-factor proof in
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), II.2 and Lemma II.3.2, printed pp. 253–255.
The Lean proof uses homogeneous adjoint coordinates, the residue-normalized
maximum entry norm, and a common bound on the two compact sets that arise
from the statement's independent compact factors and finite centralizer
family. The registered source `waldspurger-2003-plancherel` has SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
