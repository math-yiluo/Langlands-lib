# Points of the Chevalley group: root elements and torus

Author: Worker 1398.

For `D : ChevalleyData P b` and a field `K`:
* `rootHom j` and `x j s = exp_j(s) ∈ GL_n(K)`, with `x_add`, `x_zero`, `x_neg`;
* `diagUnit f` the diagonal unit with entries `f c`, and `torusHom : (Multiplicative X →* Kˣ)
  →* GL_n(K)`, `χ ↦ diag(χ(wt c))`, the `K`-points of the split torus with character group `X`;
* `torusHom_conj_x`: `t x_j(s) t⁻¹ = x_j(χ(root j) s)`, proved entrywise from the weight
  condition on `e j k`.
Internal lemmas.
