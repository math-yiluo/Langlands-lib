# Descent of the character-valuation kernel from `K` to `F`

Authors: Worker 1532 and Worker 389. The Lean statement and initial exposition
reuse Worker 1532's draft; Worker 389 checked the original passages and authors'
corrections and clarified the valuation conventions.

`Langlands.Geometry.Building.CharacterValuationKernelDescentStatement.{u}`
is a proposition definition. It states the derived identity
`G(F)^1 = G(K)^1 ∩ G(F)` for an affine group scheme `G` over a
nonarchimedean local field `F`, where `K` is its maximal unramified extension
inside `SeparableClosure F`. This file supplies no proof of that proposition.

## The proposition

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, write `K := UnramifiedClosure F`. For every
`G : GroupScheme (Spec (CommRingCat.of F))` with `[IsAffine G.X.left]`,

```text
(characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
    (GaloisPointComparison.baseChanged F K G)).comap
  (GaloisPointComparison.rationalExtend F K G) =
Plancherel.rationalCommonNormKernel G
```

as subgroups of `rationalPoints G`, the group `G(F)`.

These are all the quantified objects and hypotheses. The universe `u` is
arbitrary, and `F` may have either characteristic. No reductive, smooth,
connected, finite-type or splitting hypothesis is imposed on `G`.
The only direct import is `Langlands.Geometry.Building.KPZeroNormKernel`.

## Exact objects and valuation conventions

`UnramifiedClosure F` is the actual inertia fixed field in
`SeparableClosure F`. The valuation
`v_K := LocalGalois.Separable.fixedFieldValuation F : Valuation K ℝ≥0`
is the restriction of `LocalGalois.Separable.sepClosureValuation F`,
the spectral valuation associated to `LocalGalois.localNormedField F`.
It extends the prescribed canonical valuation
`v_F := ValuativeRel.valuation F` in the sense of `Valuation.HasExtension`.
Their value groups need not be definitionally identical; extension preserves
the condition that a nonzero element has value one.

The absolute value `|·|_F` on the right is the residue-normalized one,
`LocalField.residueNormalizedAbsoluteValue F`: for a uniformizer `π`,
`|π|_F = q_F⁻¹`, where `q_F` is the residue-field cardinality.
Its unit kernel agrees with that of `v_F`. No numerical identification of
this normalization with the chosen spectral normalization on `K` is required.
The multiplicative condition `v(x) = 1` corresponds to the additive
valuation condition `ω(x) = 0` used by KP.

`GaloisPointComparison.baseChanged F K G` is the actual base change `G_K`,
and `GaloisPointComparison.rationalExtend F K G` is extension of rational
points along `F → K`. The left subgroup is the inverse image under this map
of `characterValuationKernel v_K G_K`. Its members are precisely those
`g ∈ G(F)` such that
`v_K(ψ(rationalExtend F K G g)) = 1` for every `K`-rational algebraic
character `ψ : G_K → 𝔾_m`.

`Plancherel.rationalCommonNormKernel G` consists of those `g ∈ G(F)` with
`|χ(g)|_F = 1` for every `F`-rational algebraic character `χ : G → 𝔾_m`.
The Library theorem `characterValuationKernel_eq_rationalCommonNormKernel`
identifies it with `characterValuationKernel v_F G`.

The inclusion from the left subgroup to the right is already proved:
`comap_characterValuationKernel_le` tests the base changes of `F`-rational
characters and uses extension of valuations; the displayed Library
identification then gives the claimed inclusion. Both theorems are in
`Langlands.Geometry.Building.KPZeroNormKernel`. The reverse inclusion is the
remaining content of this proposition.

## Source and derived provenance

The source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New
Approach*, Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. In the retained book PDF,
printed page = PDF page − 31.

- Notation 2.6.15, printed p. 102 / PDF p. 133, defines `G(k)^1` as the
  kernel of the character-valuation homomorphism on `G(k)`.
  The authors' *Corrections and additions*, version of 1 November 2024,
  registered as `kaletha-prasad-2024-corrections`, PDF p. 25, Section 2.6,
  correct its coordinate to `χ ↦ ω(χ(g))`, removing the printed minus sign.
  The correction leaves the kernel unchanged.
- Lemma 2.6.16(4), printed p. 103 / PDF p. 134, identifies this kernel by
  vanishing on all `k`-rational characters, equivalently on all geometric
  characters evaluated with the extended valuation.
- Lemma 2.6.17, on the same page, compares the valuation homomorphisms under
  a Galois extension of finite ramification degree with the uniquely
  extending valuation.
- Lemma 2.6.27, printed p. 105 / PDF p. 136, passes from
  `M₀(K)^0 = M₀(K)^1` to `M₀(k)^0 = M₀(k)^1` for a minimal Levi subgroup
  of a simply connected group. Corollary 2.6.28, printed pp. 105–106 /
  PDF pp. 136–137, explicitly uses
  `M₀(k)^1 = M₀(K)^1 ∩ M₀(k)` and the analogous defining identity for
  `M₀(k)^0`.

KP introduce Notation 2.6.15 and Lemmas 2.6.16–17 for connected reductive
groups over a discretely valued Henselian field with perfect residue field.
The corrections also broaden the subsequent discussion from just before
Definition 2.6.20 to Henselian valued fields with perfect residue field.
The present proposition specializes the fields to a nonarchimedean local
`F` and its maximal unramified extension `K`, which is Galois of ramification
degree one, and extends the group scope to every affine `G`. It is therefore
a derived formulation, rather than a literal transcription of a KP lemma.

The reason affineness suffices is recorded here as provenance, not as a
proved result in Lean. A `K`-character of an affine `G` is defined over a
finite Galois extension `F'/F` inside `K`. Indeed, its coordinate map is
specified by a unit and its inverse in the scalar-extended coordinate ring;
these involve only finitely many coefficients from `K`. This uses no
finite-type assumption on `G`.
The product of the `Gal(F'/F)`-conjugates of that character descends to an
`F`-character `χ`. At `g ∈ G(F)` its value is the field norm of the original
character value. The valuation on `K` is Galois invariant, so, computing
both sides in `K`,

```text
v_K(χ(g)) = v_K(ψ(g))^[F' : F].
```

The embeddings of `F` and `F'` into `K` are implicit in this formula.
Since `[F' : F]` is positive and `v_K` takes values in `ℝ≥0`, a unit value
for `χ(g)` forces a unit value for `ψ(g)`. This explains the proposed
reverse inclusion without imposing reductivity, smoothness or connectedness.
The character descent, conjugate product and valuation argument remain
obligations for a separate proof of the exact proposition.
