# Levi and split components of a characteristic truncation shell

Delorme, *On the spectral theorem of Langlands* (2023), §7, (7.2) and (7.23),
decomposes a parabolic characteristic chamber and its shell into a Levi factor
and a split factor. Write `J` for the simple roots of the Levi and use the
relative level projection `π` onto their common kernel. The two components of
`X` are `X − π X` in the Levi coroot subspace and `π X` in the split subspace.

The Levi inequalities use the projections `T₀ − π T₀` and `T − π T` of the
lower and upper parameters. For a simple root outside `J`, every Levi coroot
has nonpositive evaluation. The inequalities on the Levi weights therefore
give a nonnegative contribution at that root, and the strictly positive split
inequality and `α(T − T₀) ≥ 0` imply the lower cutoff for `X`. The remaining
inequalities follow by projection. This proves (7.2).

For (7.23), the full weights outside `J` vanish on the Levi coroot subspace,
so the additional upper cutoff there is an inequality on the split factor
alone. For a root in `J`, the inverse Cartan block has nonnegative entries.
If the corresponding roots are nonnegative on `S`, each Levi weight of `S`
is nonnegative. The Levi upper bound thus continues to hold at the increased
parameter. The comparison of weights from nested Cartan blocks says that once
the full weights outside `J` are nonpositive, a full weight indexed by `J` is
at most its Levi counterpart. This proves the remaining full upper bounds.
`truncationShellProduct` gives the resulting Minkowski sum for the characteristic
shell with strict split inequalities.
