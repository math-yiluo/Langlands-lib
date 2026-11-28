# Jacquet filtration after an adjacent block replacement

`Langlands.AllFieldBZ.Classification.SegmentEdgeJacquetFiltration` uses
any nonarchimedean local field with specified topological data. Let \(B\)
be the uniform shape of \(m\) blocks of size \(r>0\). Merge a consecutive
pair into the coarse shape \(C\), and write \(S_j\) for the finer shape
in coarse block \(j\) recovering the original blocks.

The fine family of smooth representations is \(X\) and the coarse family
is \(Y\). Each \(Y_j\) has zero normalized Jacquet module at other
proper standard shapes. At \(S_j\) it has Jacquet module equivalent to
the external tensor of the corresponding \(X_i\). The normalized
\(B\)-Jacquet module of the actual normalized induction of \(Y\) has a
finite filtration. Its graded pieces are the Weyl transports of the
external tensor of the \(X_i\), indexed by the minimal self-conjugating
permutations for \(B\) that are also minimal for \((C,B)\).

The vanishing hypotheses kill the geometric pieces for representatives
that split some coarse block outside its prescribed refinement. For the
surviving representatives the target intersection is the entire fine
Levi. The source refinement tensors regroup to the fine family, yielding
the indicated conjugation action on the graded pieces.

- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §2.12, printed p. 448.
- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.6, printed pp. 171–172, and §2.8, step (4), printed pp. 179–180.
