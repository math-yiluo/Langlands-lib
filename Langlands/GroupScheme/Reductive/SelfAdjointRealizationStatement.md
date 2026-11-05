# Actual adjoint-stable realization of a connected reductive group

Authors: Worker 1359 and Worker 1571.

`Langlands.GroupScheme.ConnectedReductiveSelfAdjointRealizationStatement`
is a proposition to be proved. It asserts that, for every `RCLike k : Type u`
and every actual group scheme `G` over `Spec k` satisfying the published
`IsConnectedReductive G`, there are a natural number `d` and a group-scheme
homomorphism `ρ : G ⟶ GL_d` such that:

- the underlying scheme morphism of `ρ` is a closed immersion;
- the literal range of `ρ.affineMatrix (CommAlgCat.of k k)` on all actual
  `k`-valued affine points is stable under conjugate transpose.

The matrix range is a subgroup of `GL (Fin d) k`. Here `star` is the adjoint
on that invertible matrix group, induced by the given `RCLike` conjugation on
`k`. Since this range is a subgroup, stability under adjoint is equivalent
to stability under the Cartan involution `q ↦ star (q⁻¹)`. One inclusion
suffices: adjoint is involutive.

The representation, its rank and its closedness are conclusions. There is no
supplied representation, positive definite form, Cartan involution, compact
subgroup, polar decomposition, complete-reducibility certificate, or
comparison with another point group among the hypotheses. The statement
uses the complete rational-point range, including all real point components.
It has no splitness or anisotropy restriction and permits rank zero.
The universe `u` is arbitrary.

This is a derived interface for the realization step of the actual
archimedean parabolic Iwasawa proof. It is distinct from ordinary affine
linear embedding, which provides a closed representation but does not prove
adjoint stability. It states no parabolic classification or Iwasawa covering
and makes no assertion about a specified Levi subgroup. No topology is
chosen or changed in this statement; the consumers use the existing
regular-function evaluation topology on these same affine points.

## Original sources and the derived formulation

The retained sources are:

1. A. Borel and Harish-Chandra, *Arithmetic Subgroups of Algebraic Groups*,
   Annals of Mathematics (2) 75 (1962), 485–535,
   source `borel-harish-chandra-arithmetic-subgroups-1962`.
   The retained PDF has a cover sheet: printed pp.488–492 are PDF pp.5–9.
   Section 1.1 describes Cartan involutions of `GL_n(ℝ)` using adjoints for
   positive definite quadratic forms. Section 1.2 relates complete
   reducibility of a closed group with finitely many components to its Lie
   algebra, and §1.3 defines a reductive real algebraic matrix group using
   complete reducibility. Lemmas 1.5–1.6 construct compatible Lie-algebra
   Cartan involutions. Lemma 1.7 treats the whole real group, and Lemma 1.8,
   including its proof across printed pp.491–492, constructs a compatible
   group Cartan involution. Theorem 1.9 gives simultaneous conjugation of
   a chain of real reductive algebraic matrix groups to self-adjoint
   groups. Its one-group case is the real matrix-group source for the
   existence asserted here.
2. A. Borel, *Lie Groups and Linear Algebraic Groups, I. Complex and Real
   Groups*, Hong Kong lecture notes, 2000–2001 repository copy,
   source `borel-lie-groups-linear-algebraic-groups-2000`.
   Section 5.6, printed pp.39–40 (the same PDF pages), records compact
   real-form existence for a connected complex reductive group.
   Sections 5.8 and 6.2, printed pp.40–42, discuss restriction of scalars
   and the real reductivity of complex reductive groups and their real
   forms. Section 6.3, printed pp.42–43, defines self-adjointness in
   `GL_n(ℝ)`; its converse remark on p.43 cites Mostow and
   Borel–Harish-Chandra Lemma 1.8.

The Lean proposition is not a literal restatement of Borel–Harish-Chandra's
real matrix-group theorem. Its scheme presentation and arbitrary `RCLike`
field are an internal derived formulation. A proof must supply all bridges:
ordinary closed linear embedding of `G`; comparison of the published
geometric-unipotent-radical reductivity predicate with the classical
reductive algebraic group used in the sources; adjoint-stable realization
for both the real and complex cases; normalization of a positive quadratic
or Hermitian form if one is used; and transport to the actual field `k`
at arbitrary universe `u`.

In particular, the real transpose theorem by itself does not establish the
complex conjugate-transpose case. A proof using real restriction of scalars
must recover a representation over the original complex field and its
Hermitian adjoint, while a compact-real-form proof must establish the
required group and representation comparisons. The Lie-algebra statements
alone also do not establish stability of the entire real point group.
These are proof obligations, not extra assumptions or results proved by
this statement module.
