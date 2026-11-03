# Pseudo-completeness of pseudo-parabolic quotients

Author: Worker 1369.

`Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteStatement` is a
Prop-valued statement of CGP Proposition C.1.6 for actual group schemes and a
supplied actual homogeneous quotient. This module defines the proposition;
it provides no proof of it.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition C.1.6 and its proof, printed pp.586–588 (one-based PDF
pp.612–614). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Definition C.1.1, printed p.581 (PDF p.607), gives pseudo-completeness.
Definition 2.2.1 and its following warning, printed p.62 (PDF p.88), give
pseudo-parabolicity and distinguish the conclusion from properness.

## Inputs and quotient interface

For every universe `u` and every field `k : Type u`, put
`B := Spec (CommRingCat.of k)`. The statement quantifies over actual group
schemes `G P : GroupScheme B` and a homomorphism `i : P ⟶ G` satisfying
the published `IsPseudoParabolicSubgroup i`. That predicate includes
`Smooth G.X.hom`, `ConnectedSpace G.X.left`, and `IsAffineHom G.X.hom`;
these hypotheses need no additional binders in this statement.
It also requires a represented fppf-local product presentation
`P_G(χ) R_{u,k}(G)`, using an actual ground-field cocharacter and the
published ground-field unipotent radical. No reductivity or
pseudo-reductivity is required of `G`, and there is no perfectness,
infinitude or characteristic restriction on `k`.

For each actual relative scheme `Q : Over B` and morphism `q : G.X ⟶ Q`,
the remaining premises are exactly the quotient conditions used in
`SmoothSubgroupQuotientExistenceStatement`, imported from
`Langlands.GroupScheme.HomogeneousQuotientStatement`:

- `IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and
  `QuasiCompact Q.hom`, expressing separatedness and finite type over `k`;
- `Smooth q.left`, `Surjective q.left` and `QuasiCompact q.left`;
- for every relative scheme `T : Over B` and actual points
  `g h : T ⟶ G.X`, the equivalence
  `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T`.

The last condition has the right-coset orientation `gP = hP`. The range
predicate says that the actual point `g⁻¹ * h` factors through `i` over
the same test scheme. The tests include nonreduced and nonaffine schemes;
the condition is not restricted to field-valued points or affine tests.
The statement adds no smoothness or connectedness hypothesis on `P`
beyond the supplied pseudo-parabolic predicate and quotient data.

Smoothness and surjectivity make `q` an fppf cover: smoothness supplies
flatness and local finite presentation. The exact all-test fibers identify
its equivalence relation with right translation by `P`, so these premises
express the given fppf homogeneous quotient `G/P`. Thus the conclusion
concerns every supplied scheme model with this interface. This is the
derived translation of the source's coset space into the existing
homogeneous quotient interface; the module neither constructs a new
quotient nor assumes the quotient-existence statement is proved.
In particular, an fppf cover does not require surjectivity of
`G(k) → Q(k)`, and that rational lifting property is no premise here.

## Conclusion and the DVR condition

The conclusion is exactly `Langlands.GroupScheme.IsPseudoComplete Q`,
imported unchanged from `Langlands.GroupScheme.PseudoComplete`. Its
separatedness and finite-type fields agree with the first three quotient
premises. Its remaining field is the restricted valuative extension
condition of Definition C.1.1.

For every `k`-algebra `R : Type u` with `CommRing R`, `IsDomain R` and
`IsDiscreteValuationRing R`, assume
`Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R)`.
Every actual relative point
`x : PseudoComplete.algebraSpec k (FractionRing R) ⟶ Q` must then extend
to `xR : PseudoComplete.algebraSpec k R ⟶ Q` with
`PseudoComplete.genericPoint R ≫ xR = x`.
The fraction and residue fields have the induced `k`-algebra structures.
All DVR tests are in the same universe `u`; no larger-universe tests are
claimed.

For field extensions, geometric reducedness expresses general separability
and allows transcendental residue extensions. The imported predicate does
not replace this condition by `Algebra.IsSeparable`, which would impose
algebraicity, or reduce the tests to algebraic residue extensions.
The existence condition together with separatedness corresponds to the
source's equality `Q(R) = Q(Frac R)`; this module proves no separate
uniqueness lemma.

## Comparison with the source proof

Proposition C.1.6 asserts pseudo-completeness for every pseudo-parabolic
quotient of a smooth connected affine group over an arbitrary field.
Its proof first uses Proposition 2.2.10 to reduce to the pseudo-reductive
case and makes a separable field extension to work over a separably closed
field. It compares with a proper reductive homogeneous space over the
algebraic closure. Translation and the opposite open cells reduce DVR
extension to an integrality assertion on the unipotent open cell.
Root-group decompositions and equivariant linear structures then reduce
this assertion to a valuation argument for a sum of characteristic-power
monomials. A failure of integrality gives a nontrivial zero over the
separable residue extension; specialization through a smooth finitely
generated algebra contradicts the absence of such a zero over the
separably closed ground field.

Those reductions explain the conclusion and its generally separable
residue-field condition. They are source proof ingredients, not extra
theorem-valued hypotheses of this Lean statement and not results proved
by this module. The reductions to pseudo-reductive and separably closed
cases do not restrict its input quantifiers.

Pseudo-completeness must be distinguished from properness. The warning
following Definition 2.2.1 says that `G/P` can fail to be proper, even for
pseudo-reductive `G` over an imperfect field. The proper reductive quotient
used inside the proof does not make the original quotient proper.
Accordingly the conclusion uses the restricted DVR predicate, with no
`IsProper Q.hom` assertion.

The imported radical, fppf-product, pseudo-parabolic and pseudo-completeness
Lean/Markdown pairs are reused unchanged. Quotient construction,
rational-point lifting and the structural proof of Proposition C.1.6
remain separate obligations.
