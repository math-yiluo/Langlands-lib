# Integer valuation of character evaluations

Author: Worker 200.

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.3, printed p.105 (PDF p.111), defines `H_G` by applying the normalized
integer valuation to rational-character evaluations. He defines `Λ(G)` as its
image, gives the resulting exact sequence, and identifies the kernel with the
intersection of the norm kernels. At the beginning of V.2.4, printed p.106
(PDF p.112), the unramified characters factor through that image. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This file constructs the composite, image and algebraic quotient in a generic
form derived from that passage. Its inputs are a group `G`, an additive
commutative group `L`, a commutative value group `K`, and maps

`ε : L →+ Additive (G →* K)`, `v : K →* Multiplicative ℤ`.

Thus evaluation is additive in the character index and multiplicative in the
group argument. The three universes are independent. The intended specialization
is `L = Rat(G)`, `K = Fˣ`, `ε` the actual rational-character evaluation from the
shared group-scheme construction, and `v` the normalized integer valuation of
field units. No actual field, reductivity, finite-rank hypothesis or topology is
assumed or constructed by this generic file. A trivial character group is allowed.

- `characterValuationPairing ε v g : L →+ ℤ` sends a character `χ` to the
  integer coordinate of `v (ε χ g)`. Additivity follows from the given
  evaluation and valuation laws.
- `characterValuation ε v : G →* Multiplicative (L →+ ℤ)` bundles the same
  formula into a homomorphism in `g`. The multiplicative type tag represents
  addition of integer-valued additive functionals. `characterValuation_apply`
  gives the coordinate formula, and `mem_characterValuation_ker` gives the
  simultaneous zero-valuation criterion, written as value `1` in
  `Multiplicative ℤ`.
- For a given positive norm `n : K →* ℝ≥0ˣ`, `evaluationNormCharacters ε n`
  constructs `L →+ Additive (G →* ℝ≥0ˣ)` by composing the same evaluations
  with `n`. `evaluationNormCharacters_apply` identifies its values. This
  does not choose an unrelated norm-character family.
- `characterValuation_ker` assumes exactly
  `∀ a, v a = 1 ↔ n a = 1`. Under that displayed compatibility of the two
  given value maps, it proves that the valuation composite’s actual kernel
  equals `commonNormKernel` of `evaluationNormCharacters ε n`. It neither
  supplies the local-field instance of this compatibility nor proves a
  numerical normalization formula for `n`.
- `characterValuationImage ε v` is the actual range subgroup in the integer
  additive dual, written multiplicatively. `characterValuationQuotientEquiv`
  constructs the canonical multiplicative equivalence from the quotient of
  `G` by the composite’s kernel to this image. Its `_mk` lemma proves that
  the class of `g` maps to the actual valuation of `g`.
- Under the same value-kernel compatibility as above,
  `normKernelValuationQuotientEquiv` identifies the quotient already used
  for unramified characters with this actual image. Its `_mk` lemma gives
  the same representative formula. These are algebraic equivalences only;
  no topology on the image or continuity of either direction is asserted.
- `commutator_le_characterValuation_ker` proves containment of the abstract
  commutator subgroup of `G` in the valuation kernel. This follows from the
  commutative target, through Mathlib’s abelianization lemma. It makes no
  assertion identifying rational points of an algebraic derived subgroup
  with the abstract commutator subgroup.

The proofs check the coordinate laws using the two supplied homomorphisms.
The kernel calculation uses extensionality of additive homomorphisms and the
value-kernel compatibility at each evaluation. The quotient constructions use
Mathlib’s `QuotientGroup.quotientKerEquivRange` and transport along the proved
kernel equality; their representative formulas are checked directly. These
are intrinsic laws of the constructed maps, rather than a proof of the
remaining reductive lattice assertions in the source.

This contribution implements the generic valuation composite and its exact
algebraic quotient. It does not supply the actual rational-character group,
its point evaluation, or the normalized valuation and absolute value of an
arbitrary nonarchimedean local field. It does not assert that the image is
finitely generated or has full rank in the integer dual, prove a split-torus
section, prove finite index of the split-center image, or construct the
complex or unitary character torus. Openness and closedness of the kernel,
compact-subgroup containment, the comparison with algebraic derived-group
points, unimodularity, and all rational-point topology realizations remain
separate obligations. In particular no completion of Renard V.2.3–V.2.6 or
Waldspurger’s actual `H_M` construction is claimed.
