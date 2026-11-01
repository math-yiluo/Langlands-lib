# Alternating Čech section complexes of a family of opens

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.OneDirection`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

## Setting

Let `𝒰 : X.OrderedAffineCover`. Only its ordered finite index type `𝒰.ι` and the
tuples `𝒰.Idx p` (strictly increasing maps `Fin (p + 1) → 𝒰.ι`) are used. Fix a
scheme `Z` and a module sheaf `F` on `Z`.

- `rs F h` is the restriction `F(U) → F(U')` for `h : U' ≤ U`. The lemmas `rs_rs` and
  `rs_self` state that restrictions compose and that the identity restriction is trivial.
- `Fam 𝒰 Z` is a family of opens `O p s` of `Z`, one for each tuple `s : 𝒰.Idx p`, with
  `O (p + 1) t ≤ O p (𝒰.face t j)` for every face.
- `FSec F G p` is the type of families `s ↦ c s ∈ F(O p s)`.
- `δ` is the alternating Čech differential
  `(δ c) t = ∑ j, (-1)^j • c (𝒰.face t j)|_{O t}`. It is additive (`δ_add`, `δ_zsmul`,
  `δ_zero`, `δ_neg`, `δ_sub`) and squares to zero (`δ_δ`). The proof uses the
  same pairing of terms as the Library's `CechResolution.cechD_comp_cechD`.

## Contraction

`InsStable G k` says that `O p s ≤ O (p + 1) (insIdx 𝒰 s k _)` whenever `k ∉ s`.
For such a family:

- `contr hG c` is defined by `(contr c) s = (-1)^{pos s k} • c (s ∪ {k})|` if `k ∉ s` and
  `0` otherwise. This is the operator `CechResolution.contr` of the Library, for a general
  family of opens.
- `proj hG c` restricts the `(k)`-component, `(proj c) s = c (single k)|_{O s}`. It
  uses `le_single : O 0 s ≤ O 0 (single k)`.
- `δ_contr_add_contr_δ`: `δ (contr c) + contr (δ c) = c` in positive degrees.
- `contr_δ_zero`: `contr (δ c) = c - proj c` in degree zero.
- `δ_contr_of_δ_eq_zero` and `eq_proj_of_δ_eq_zero` are the cocycle consequences.

The Library proves only the cocycle form (`CechResolution.dSec_contr`). The full identity
has the same proof: split the sum over the faces of `s ∪ {k}` at the inserted position
(`Fin.sum_univ_succAbove`), and identify the remaining faces using `face_insIdx_succAbove`
and the sign rule `sign_face`. These combinatorial lemmas come from
`CechResolution.Exact`.

Provenance: internal. This is the standard contracting homotopy of an alternating Čech
complex over an open contained in one member of the cover. Here it is written for
arbitrary face-antitone families of opens, so that the rows and columns of the bi-Čech
complex of `BiCech.Sections` are instances.
