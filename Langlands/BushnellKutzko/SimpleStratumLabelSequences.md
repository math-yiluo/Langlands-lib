# Extending and truncating labels

Operations on the labels `Label q` of `Labels`, the finite sequences
`((φ_i, n_i, d_i, e_i))_{0 ≤ i ≤ r}` of Bushnell–Kutzko 1994,
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, (1.13), printed
pp. 115–116.

- `Label.single x`: the label with the single quadruple `x` (`r = 0`).
- `Label.snoc p x`: the label `p` followed by the quadruple `x`; its
  entries are `p.entry i` for `i ≤ r` and `x` at index `r + 1`
  (`snoc_entry_castSucc`, `snoc_entry_last`, `snoc_entry_of_lt`,
  `snoc_entry_of_eq`).
- `snoc_d`, `snoc_e`, `single_d`, `single_e`: `d(p x) = d(p) d_x`,
  `e(p x) = e_x`; partial degree products of `p x` up to index `r + 1`
  are those of `p` (`snoc_degreeProd_of_le`, `snoc_degreeProd_succ_succ`).
- `snoc_injective`: `p x = p' x'` implies `p = p'` and `x = x'`.
- `LabelEntry.PolyOK x`: the polynomial of `x` lies in `𝔍(d_x, q^D)` for
  the exponent `D` it is recorded with.

Membership in `labelSet m n a b q = P^m_n(a, b; q)`:

- `lt_level_of_mem_labelSet`: every level of a label in `P^m_n` exceeds
  `m`;
- `labelSet_succ_subset`: `P^{m+1}_n ⊆ P^m_n` (the inclusion used for the
  restriction map in the proof of (1.14), printed p. 117);
- `single_mem_labelSet`: the conditions (1.13)(i)–(ii) for a one-entry
  label;
- `snoc_mem_labelSet`: appending to a label of `P^{m+1}_n` a quadruple of
  level `m + 1`, positive degree, ramification `gcd(m + 1, e(p))`,
  polynomial over `𝔽_{q^{d(p)}}` and `d(p) d_x ∣ b` gives a label of
  `P^m_n` ((1.13)(iii) for the new index);
- `snoc_ne_of_mem_labelSet`: such an extension is never a label of
  `P^{m+1}_n`, whose levels all exceed `m + 1`.
