# Uniform Whittaker vanishing on a coordinate Jacquet kernel

Worker 635 defines the single closed proposition
`Langlands.Whittaker.CoordinateJacquetKernelStatement.{uF,uV}` in
`Langlands.Representation.Whittaker.CoordinateJacquetKernelStatement`.
This module states the vanishing assertion and supplies no proof of it.
The formulation follows Worker 186's task specification and the direct
relation-generator argument identified there by Workers 186 and 48.

This is an internal derived prerequisite for the Jacquet-kernel step in
JPS (1979), Proposition (2.2), rather than a verbatim theorem from that
paper. In particular, the conclusion concerns the entire diagonal torus
and arbitrary algebraic equivariant functionals. The mathematical audit
below explains why those stronger quantifiers are appropriate; it is not
a Lean proof or an assertion of independent mathematical acceptance.

## Exact data and quantifier order

The proposition quantifies over every natural number `p`, a certificate
`Fact p.Prime`, every `F : PadicField.{uF} p`, and every supplied
`T : F.TopologicalData`. It installs `T.topology`, so all subsequent
topological hypotheses use this supplied topology. The absolute value is
`T.normalizedAbs`, from the same data. It is the residue-cardinality
normalization, zero at zero and `q ^ (-T.ord x)` at nonzero `x`, where
`q = T.residueCardinality`.

Next it quantifies over every `n : ℕ`, every `V : Type uV` with
`AddCommGroup V` and `Module ℂ V`, every representation

```lean
ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V
```

and every raw additive character `ψ : AddChar F.Carrier ℂ`. The hypotheses
are exactly `Continuous ψ`, `∀ x, ‖ψ x‖ = 1`, and `IsSmooth ρ`. Thus `ρ`
may be reducible, infinitely generated, or nonadmissible. There is no
central-character hypothesis. The character may be trivial. The field
universe `uF` and carrier universe `uV` are independent; no topology on
`V` or continuity of a dual functional is assumed.

The local predicates reproduce the parent's entrywise Whittaker convention:

```lean
unipotent g :=
  (∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1
θ g := ∏ j : Fin n, ψ (g.val j.castSucc j.succ)
```

For every algebraic functional `ℓ : Module.Dual ℂ V` satisfying

```lean
∀ g, unipotent g → ∀ w, ℓ (ρ g w) = θ g * ℓ w
```

the conclusion holds for every `i : Fin n` and every vector in the
specified Jacquet kernel. This is the exact covariance used in
`Langlands.WhittakerLastEntryOneAsymptoticStatement`, without its
nontrivial-character, admissibility, finite-generation, or
one-dimensional-functional-space hypotheses. The zero functional is
included, as are multiple independent equivariant functionals.

The torus homomorphism is exactly the parent's expression:

```lean
(Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F.Carrier).toMonoidHom).comp
  MulEquiv.piUnits.symm.toMonoidHom
```

It sends `a : Fin (n + 1) → F.Carrierˣ` to the diagonal matrix with entries
`a j`. No alternate torus parametrization is introduced.

## The actual quotient and conclusion

For `i : Fin n`, the local block shape is precisely

```lean
B := CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val (by omega)
```

Its ordered block sizes are `i.val + 1` and `n - i.val`; both are positive.
The map `B.jacquetMk ρ` is the Library's actual linear quotient map onto
`B.JacquetModule ρ`, the coinvariants of the unipotent radical of `B`'s
standard parabolic. No abstract substitute for this quotient is used.
Normalization of the Levi action does not change this underlying quotient.
The published `B.jacquetModuleEquiv ρ` identifies it with the coinvariants
of the ambient matrix subgroup `B.unipotentSubgroup F.Carrier`, and
`jacquetModuleEquiv_mk` identifies their quotient maps.

For each `v : V` such that `B.jacquetMk ρ v = 0`, the conclusion is

```lean
∃ ε : ℝ, 0 < ε ∧
  ∀ a : Fin (n + 1) → F.Carrierˣ,
    T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) < ε →
    ℓ (ρ (torus a) v) = 0
```

The threshold can depend on all earlier data, including `ℓ`, `i`, and `v`.
It is chosen before `a`. Consequently the vanishing is uniform over all
other diagonal entries, all other simple-root coordinates, and the common
central scalar. There is no last-entry-one condition, upper-support bound,
antitonicity assumption, fixed contraction sequence, or compact averaging.

For `ℓ = 0`, the coefficient vanishes identically, so any positive threshold
has the required effect. For `ψ = 1`, equivariance makes each radical
relation's coefficient zero at every diagonal. For `n = 0`, the subsequent
quantifier `i : Fin 0` is empty, so the conclusion is vacuous and no
impossible two-block shape is demanded in rank one.

## Audit of the stronger derived formulation

Write `N = B.unipotentSubgroup F.Carrier` and `t = torus a`. The Library
lemma `splitUnipotent_of_mem_twoBlock` says that `u ∈ N` agrees with the
identity outside the upper-right block across the selected split. Diagonal
conjugation preserves that pattern. Its entries satisfy

`(t u t⁻¹)_(j,k) = (a_j/a_k) u_(j,k)`.

Among entries immediately above the diagonal, only the entry across the
split, indexed in Lean by `(i.castSucc, i.succ)`, can be nonzero. Therefore

`θ(t u t⁻¹) = ψ((a_i/a_(i+1)) u_(i,i+1))`.

For the actual generating relation `ρ(u)w - w`, linearity, the
representation law, and equivariance give the scalar identity

`ℓ(ρ(t)(ρ(u)w - w)) = (ψ((a_i/a_(i+1)) u_(i,i+1)) - 1) ℓ(ρ(t)w)`.

A continuous unit-norm additive character on the p-adic field is trivial
on an open additive subgroup: one may take an additive valuation lattice
mapped into a sufficiently small arc in the unit circle, which contains
no nontrivial subgroup. If `ψ = 1` this is immediate. Otherwise the raw
character can be bundled using the published `UnitaryAdditiveCharacter.ofComplex`,
and `T.exists_additiveTrivialAt` supplies such a lattice. The Library's
`T.normalizedAbs_balls_basis` and the topology of these valuation lattices
allow a positive normalized-absolute-value threshold for the argument
`(a_i/a_(i+1)) u_(i,i+1)`. The fixed matrix entry is harmless; if it is zero,
the scalar factor already vanishes everywhere.

The published `Jacquet.mk_eq_zero` and `Jacquet.relations_eq_span`, together
with the quotient equivalence above, identify each kernel vector with an
element of the algebraic span of these relations. Zero vectors and scalar
multiples preserve a positive threshold; sums use the minimum of two
positive thresholds. Thus finite span induction is the anticipated route
to one threshold for a kernel vector. This audit controls only the single
character factor and does not require the full conjugated matrix to tend
to the identity. Arbitrary sizes in the other entries and an arbitrary
central scalar do not affect that factor. Smoothness is retained as
requested, although the displayed algebraic cancellation itself does not
use it. Formalizing this argument is the separate proof obligation.

## Relation to JPS and source record

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Annals of Mathematics (2) 109 (1979), no. 1, 169–212, registered
source `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Proposition (2.2), its proof, Lemma (2.2.1), and Remark (2.2.5), printed
pages 181–183 (one-based PDF pages 14–16), were read in the text layer and
visually checked. The retained PDF fingerprint was verified. No
source-specific erratum was found at the checked project and workspace
`notes/errata/jps-1979-gl3-i.md` paths.

The source uses the simple-root torus represented by matrices
`diag(x₁⋯xₙ, x₂⋯xₙ, …, xₙ, 1)`. Its proof takes the space spanned by
`π(u)W - W` for the radical of a parabolic of type `(i,r-i)`, then observes
that its restrictions vanish when the corresponding root coordinate is
sufficiently small. Lemma (2.2.1) requires a threshold uniform in all other
coordinates. The present statement isolates and strengthens this kernel
step to the full diagonal torus and arbitrary algebraic functionals; the
explicit conjugation audit gives its provenance. The source's finite-type
and admissibility hypotheses serve the later finite-dimensional quotient
and expansion arguments, which are outside this statement.

The imported Library constructions are reused without modification:
`CuspidalSupport.LeviSplitContraction` supplies `twoBlock`,
`Jacquet.Parabolic` supplies the actual quotient, the local-field
normalization definitions supply `T.normalizedAbs`, and the smooth
representation definitions supply `IsSmooth`. The conductor, normalization
proof, and prerequisite-interface lemmas named in the audit are existing
Library results documenting a future proof route; the proposition does
not assume their conclusions as additional hypotheses. The parent
asymptotic proposition is a comparison of conventions and is not assumed.
