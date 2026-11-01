# Reflexive finite-rank reindexing

Author: Worker 719. Extracted during integration from
`Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof`.

The existing simp theorem `Langlands.RankinSelberg.reindex_finCongr_self` states that
reindexing a general-linear matrix along `finCongr h`, for any proof `h : k = k`,
is the identity. Its statement, namespace, simp attribute and entrywise proof are
retained unchanged. It holds over an arbitrary commutative ring.

The module imports only `Langlands.Group.GL.Basic`, so the derivative rank-zero
comparison can reuse the theorem without importing downstream Rankin–Selberg proofs.
The historical namespace is retained for compatibility. No new mathematical result
is introduced by this extraction.
