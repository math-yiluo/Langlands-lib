# Subsegment Jacquet factors at blocks divisible by the cuspidal rank

`Langlands.AllFieldBZ.Classification.DivisibleBlockSegmentJacquetStatement`
uses the actual normalized upper Jacquet functor over any nonarchimedean
local field with specified topological data. Let the segment have length
\(m\) and cuspidal rank \(r\), and let the standard parabolic have ordered
blocks of sizes \(N_i\) divisible by \(r\). Write \(q_i=N_i/r\) and
\(p_i=\sum_{j<i}q_j\), using zero-based indices for the segment members.

For the segment socle, the normalized Jacquet module is the external
tensor of the socles of the subsegments of length \(q_i\) beginning
at member \(p_i\). For the special head, it is the external tensor of
the heads of the subsegments of length \(q_i\) beginning at member
\(m-p_i-q_i\). The subsegments for the head are therefore assigned to
the Levi blocks in descending order along the original segment.
In both cases the statement supplies the subsegments, their degree
equalities with the Levi blocks, actual block representations, and the
equivariant linear equivalence with their external tensor.

The two-block formulas iterate by normalized Jacquet transitivity along
ordered refinements. Their subsingleton cases at nondivisible blocks are
covered by the separate uniform vanishing formula.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  Propositions 3.4 and 9.5, printed pp. 181–182 and 198.
- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §2.3(c), printed p. 446.
