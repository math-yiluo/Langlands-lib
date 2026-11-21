# Proof of the apartment cocharacter root-support statement

`Langlands.Geometry.Building.lieRootSupportOfApartmentCocharacter` proves
the Library proposition
`Langlands.Geometry.Building.LieRootSupportOfApartmentCocharacterStatement`
(module `Langlands.Geometry.Building.KPLieCocharacterRootSupportStatement`)
at arbitrary universe `u`. The theorem's type is exactly that proposition.

## Setting

`P : ParahoricBuildingData G` is supplied building data over a
nonarchimedean local field `F`, with actual maximal split torus `S → G`, and
`L : P.LieFiltrationData` gives supplied centralizer and relative affine-root
Lie lattices. Given `X ∈ 𝔤_{x,r}` (`lieFiltrationReal`) contracted by the
composite `Gₘ → S → G` of an actual cocharacter `ν`, let `v` be the image of
`1 ⊗ ν` in the reduced translation space, `n = ⌈−r⌉₊` and `t = r + n`.
The claim is that every `a • X` with `a ∈ 𝔪ⁿ` lies in the sum `Q` of the
root lattices `L.affineRootLie ψ` with `ψ(x) ≥ t` and `ψ̇(v) > 0`.

## The proof

1. **Weight splitting.** `S` is a split torus (`isMaximalSplitTorus`), so
   the generic Lie algebra is the internal direct sum of its `S`-weight
   spaces (`isInternal_weightSpace_of_isSplitTorus`). Let `Pos` be the sum
   of the weight spaces of characters `χ` with `⟨χ, ν⟩ > 0`, and `Neg` the
   sum over `⟨χ, ν⟩ ≤ 0`. They are disjoint by independence of the weight
   spaces. Their preimages `PosO`, `NegO` under `GenericLie.equiv` are
   disjoint `𝒪[F]`-submodules.
2. **The contracted vector is positive.** A private lemma rewrites
   `cocharacterPositiveLie` as the sum of the weight spaces of `ν` for
   `t ↦ tⁿ⁺¹`. The published `iSup_nat_succ_weightSpace_cocharacter`
   identifies that sum with `Pos`. Hence `X`, and every scalar multiple
   `a • X`, lies in `PosO`.
3. **Root lattices have a sign.** For `ψ` with gradient the relative root
   `α`, `ψ̇(v) = ⟨α, ν⟩`. The field `affineRootLie_le` of the supplied
   `L : P.LieFiltrationData` puts `L.affineRootLie ψ` in `P.rootLieSpace α`,
   the preimage of `RelativeRoot.positiveWeightSpan P.i α`, the sum of
   the weight spaces of the positive multiples `kα`. Since
   `⟨kα, ν⟩ = k⟨α, ν⟩`, this lattice is in `PosO` if `ψ̇(v) > 0` and in
   `NegO` if `ψ̇(v) ≤ 0`.
4. **The centralizer term is in weight zero.** The centralizer image is
   in the weight-zero space by
   `Lie.mem_weightSpace_zero_of_mem_torusCentralizer`, using that
   `P.centralizer` represents the torus centralizer. Weight zero is part
   of `Neg`.
5. **Conclusion.** By the definition of `lieFiltrationReal`,
   `a • X ∈ 𝔤_{x,t}`: the centralizer image plus the root lattices with
   `ψ(x) ≥ t`. Steps 3–4 give `𝔤_{x,t} ≤ Q ⊔ NegO`, so `a • X = Y + Z` with
   `Y ∈ Q ⊆ PosO` and `Z ∈ NegO`. Then `Z = a • X − Y ∈ PosO`, hence
   `Z = 0` by disjointness and `a • X = Y ∈ Q`.

No periodicity, apartment axiom or finite generation is used. The theorem
uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Relation to the source

This is the weight-space argument in the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 13.6.7, printed
p. 481 / PDF p. 512, written on the Library's relative root spans. The proof
does not obtain `ν` by parahoric conjugacy and does not move the coset.
