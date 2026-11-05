# `N` permutes the root groups and normalizes the torus

Author: Worker 1398.

`IsRootPerm g`: there is an additive map `w : X → X` such that for every root `j` there is a root
`j'` with `root j' = w (root j)` and `g U_j g⁻¹ ⊆ U_{j'}`. By closure induction every element of
`N` has this property (torus elements fix each root group; `n_i^{±1}` act through `s_i` by
`wn_conj_x`). `NormalizesTorus g`: `g T g⁻¹ ⊆ T`, also true on `N` (`n_i t(χ) n_i⁻¹ =
t(χ ∘ s_i)`). Internal lemmas following Steinberg, *Lectures on Chevalley groups*, §3.
