# The radical of `Q` meets `w⁻¹ P w` inside `w⁻¹ U w`

This module proves the group-theoretic fact behind the injectivity step in the convergence proof
of intertwining integrals (Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*,
II.1.6, Remark and proof of (i)). For every `v ∈ V(F)` and `w ∈ W(P, Q)`, if `w⁻¹ v w ∈ P`,
then `w⁻¹ v w ∈ U`. Hence `V ∩ w P w⁻¹ = V ∩ w U w⁻¹`. So the map `δ ↦ P(F) w⁻¹ δ` from
`(V(F) ∩ wU(𝔸)w⁻¹) \ V(F)` to `P(F) \ G(F)` is injective.

Provenance: this is an internal lemma. MW use the inclusion implicitly when they bound the
intertwining integral by an integral of the Eisenstein series over `U'(k) \ U'(𝔸)` (printed p. 88).
The proof below uses the dynamic description of parabolic subgroups that is already in the
Library. It is not a transcription of a literature proof.

## `Langlands.GroupScheme.range_conj_radical_inf_parabolic_le`

Setting:

- `G` is a connected reductive group over a field `k`, with `IsAffineHom G.X.hom`.
- `p : P → G` is a parabolic with geometric unipotent radical `iU : U → P`, a Levi `l : M → P`,
  a split component `a`, and a root presentation `r : ParabolicRootPresentation p l a`.
- `q : Q → G` is a parabolic subgroup with geometric unipotent radical `iV : V → Q`, with
  `iV ≫ q` a closed immersion.
- `l' : M' → Q` has `subgroupMultiplication l' iV : M' × V → Q` an isomorphism.
- `w : Spec k → G` is a point and `c : M' → M` is an isomorphism with
  `c ≫ l ≫ p = l' ≫ q ≫ (innerIso w)⁻¹`, i.e. `l(c(m')) = w⁻¹ l'(m') w`.

Conclusion: as subgroup functors,
`range (iV ≫ q ≫ (innerIso w)⁻¹) ⊓ range p ≤ range (iU ≫ p)`. In words, on every test scheme
`T`, every `T`-point of `w⁻¹ V w` that lies in `P` lies in `U`.

Proof:

1. The compatibility field of `r` supplies a cocharacter `χ` of the split component. Its
   attracting subgroup is `P = P_G(χ)`, and its centralizer is `M = Z_G(χ)`. The Library lemma
   `radical_range_eq_dynamic_unipotent` identifies `U` with `U_G(χ)`.
2. Conjugation by `(innerIso w)⁻¹` is an automorphism of `G`. So `w⁻¹ V w` is a closed subgroup,
   represented by `iV ≫ q ≫ (innerIso w)⁻¹`. The hypothesis on `c` gives
   `range (l ≫ p) = range (l' ≫ q ≫ (innerIso w)⁻¹)`, that is, `M = w⁻¹ M' w`.
3. `w⁻¹ V w` is stable under conjugation by `χ`. A point `χ(t)` lies in `Z_G(χ) = M = w⁻¹ M' w`,
   and `V` is normal in `Q` (`IsUnipotentRadical.isNormal`).
4. `w⁻¹ V w` meets `Z_G(χ) = w⁻¹ M' w` trivially. A common point gives `l'(m') = iV(v)`, and
   `M' × V ≅ Q` forces `v = 1`.
5. The Library result `Dynamic.inf_parabolic_isPointwiseProduct_of_isStable` applies to the
   `χ`-stable closed subgroup `w⁻¹ V w`. It writes each point of `w⁻¹ V w ∩ P_G(χ)` as `z n`,
   with `z ∈ w⁻¹ V w ∩ Z_G(χ)` and `n ∈ U_G(χ)`. Step 4 gives `z = 1`, so the point lies in
   `U_G(χ) = U`.

## `Langlands.Global.comp_innerIso_inv_adelic`

For a number field `F`, a point `w` of `G` and an adelic point `v ∈ G(𝔸)`, the inverse inner
automorphism acts on adelic points by conjugation. That is,
`v ≫ (innerIso w)⁻¹ = W⁻¹ v W`, where `W = innerAdelicPoint F G w`. The proof applies the
Library lemma `GroupScheme.comp_innerIso_hom` to the point `v ≫ (innerIso w)⁻¹` and uses
`(innerIso w)⁻¹ ≫ innerIso w = 𝟙`.

## `Langlands.Global.conj_mem_parabolicUnipotentImage`

Setting: that of the first lemma over a number field `F`, with the Weyl-conjugation hypothesis
`hw : IsWeylConjugation p l q l' w c`. Let `v ∈ G(𝔸)` lie in the adelic points of
`range (iV ≫ q)`, and suppose `W⁻¹ v W` is in the image of `P(𝔸)`.

Conclusion: `W⁻¹ v W ∈ parabolicUnipotentImage F p iU`, the image of `U(𝔸)` in `G(𝔸)`.

Proof: by the previous lemma, `W⁻¹ v W` is the adelic point `v ≫ (innerIso w)⁻¹` of
`w⁻¹ V w`. Apply the first lemma at the test scheme `Spec 𝔸_F`, with the fields `isIso` and
`comp_eq` of `hw`.
