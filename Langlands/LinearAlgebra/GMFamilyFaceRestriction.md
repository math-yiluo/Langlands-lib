# Restricting `(G, M)`-families to the Levi subgroup of a face

Module `Langlands.LinearAlgebra.GMFamilyFaceRestriction` treats a face
`Q = posSet R w` with `w ∈ a`, the abstract form of a parabolic subgroup
`Q ⊇ P ∈ 𝓟(M)`. The roots of its Levi subgroup `M_Q` are
`leviRoots R Q`.

## Results

- `isLeviSpace_leviRoots`: `a` is a Levi space of `leviRoots R Q`. For a
  regular point `h₀` of `a`, the roots of `leviRoots R Q` vanishing at `h₀`
  are those of `R`, since a root vanishing at `h₀` vanishes on `a`, hence
  at `w`, and is neither in `Q` nor in `−Q`.
- `simpleRoots_face_eq_filter`, `simpleRoots_face_subset`: for a chamber `S`
  of `leviRoots R Q`, the simple roots of `S` are the simple roots of the
  chamber `Q ∪ S` of `R` that vanish at `w` (from the lemmas
  `union_parabolic_of_local` and `simpleRoots_inter_leviRoots` of
  `GMFamilyRootGeometry`).
- `exists_simpleRoot_not_mem_face`: if `Q ≠ ∅`, some simple root of `Q ∪ S`
  is not a simple root of `S`. Otherwise all simple roots of `Q ∪ S` vanish
  at `w`, so by `nonneg_posSet_of_nonneg_simpleRoots` applied to `w` and
  `−w` every root of `Q ∪ S` vanishes at `w`, contradicting `⟪α, w⟫ > 0` for
  `α ∈ Q`.
- `isAdjacentAlong_face_union`: chambers `S`, `S'` of `leviRoots R Q`
  adjacent along `v` give chambers `Q ∪ S`, `Q ∪ S'` of `R` adjacent along
  `v`.
- `isFamily_face`: if `c` is a `(G, M)`-family for `R`, then
  `S ↦ c (Q ∪ S)` is a `(M_Q, M)`-family for `leviRoots R Q`. This is the
  family whose `c_M` is Arthur's `c_M^Q`.
- `leviRoots_empty`: `leviRoots R ∅ = R`.
- `cQM_parabolic`: for a chamber `P` (a minimal face), `cQM R a c P = c P`:
  the only chamber above `P` is `P`, the Levi root set of `P` meets `P`
  trivially and the empty theta factor is `1`.

## Provenance

These are the standard compatibilities of `(G, M)`-families with parabolic
subgroups (J. Arthur, *An introduction to the trace formula*, §17, printed
p. 97 (PDF p. 109): the first restriction operation after Lemma 17.3,
`c_R^Q(λ) = c_{Q(R)}(λ)` for `R ∈ 𝒫^{M_Q}(M)`, which gives the
`(M_Q, M)`-family whose `c_M` is `c_M^Q`; in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`),
derived here from the Library's definitions in `GMFamilies` and the face
lemmas of `GMFamilyRootGeometry` and `GMFamiliesFaces`.
