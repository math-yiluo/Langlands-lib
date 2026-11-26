# The support-sign adjustment of an exact GL operator

`Langlands.Aubert.LocalFieldGraded.supportSign` assigns
\((-1)^{n-k}\) to an irreducible smooth complex class of rank \(n\),
where \(k\) is the number of supercuspidal factors in its support,
counted with multiplicity. The field is any nonarchimedean local field
in the supplied topology. The existing all-field embedding supplies a
support in positive rank. The all-field support uniqueness theorem and
transport of the subquotient relation make the count independent of the
presentation and of the representative of the irreducible class. At
rank zero the count is zero and the sign is one.

`LocalFieldGraded.adjustOperator` applies this sign to the image of each
irreducible generator of a homogeneous additive operator. It extends
these values using the proved Jordan–Hölder isomorphism for the actual
exact Grothendieck group. `adjustOperator_irreducible` gives the
resulting formula on actual classes. Applying the construction to the
alternating induction–Jacquet operator gives the normalization in
Aubert's Definition 2.1.

In Notation 1.6 Aubert indexes support by the type of a standard Levi.
For the upper-block Levi of a partition \((n_1,\ldots,n_k)\), its
simple-root subset has cardinality
\(\sum_i(n_i-1)=n-k\). This converts the sign in Definition 2.1 to the
displayed formula. Zelevinsky §1.10 identifies the multiset of actual
cuspidal factors and its uniqueness.

- `aubert-1995-duality`, SHA-256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  Notation 1.6, printed p. 2181, and Definition 2.1, printed p. 2184.
- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.10, printed p. 174.
