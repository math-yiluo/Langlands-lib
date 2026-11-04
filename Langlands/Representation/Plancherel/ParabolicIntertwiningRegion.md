# Supplied parabolic radicals in canonical unramified-character regions

## Provenance and purpose

This is a derived adapter between the actual radical comparisons in
`ParabolicRootRadicals` and `ParabolicOppositeRootModel` and the complete
threshold-region and character-realization constructions in `IntertwiningCone`,
`CharacterIntertwiningCone` and `SubtorusIntertwiningCone`. It introduces no new
literature assertion. The identities below are intrinsic laws of the defined
regions, intended for subsequent analytic intertwining-operator work.

The entry definition is
`Langlands.Plancherel.parabolicUnramifiedIntertwiningRegion`.
All declarations below are in `Langlands.Plancherel`.

## Actual data and retained hypotheses

For the real-parameter results, let `k : Type u` be any field, `G` a smooth
affine group scheme over `k`, and `A` a commutative group scheme. There are
actual maps

- `p : P ⟶ G`, `l : M ⟶ P`;
- `p' : P' ⟶ G`, `l' : M ⟶ P'`;
- `a : A.toGrp ⟶ M`.

The existing compatible presentations `r : ParabolicRootPresentation p l a`
and `r' : ParabolicRootPresentation p' l' a` are inputs. Their full compatibility
and realization fields remain in force. In particular, `a` is the specified split
component of the connected reductive Levi `M`; no existence of compatible
presentations is proved here. Assume the literal common-Levi equality
`hM : l ≫ p = l' ≫ p'`.

Write `nu = r.splitComponentCocharacter`,
`eta = r'.splitComponentCocharacter` and `i = a ≫ l ≫ p`.
The supplied maps are `n : U ⟶ P`, `q : Q ⟶ G`, `v : V ⟶ Q`.
The hypotheses `hn` and `hv` say that `n` and `v` satisfy
`LeviSubgroup.IsGeometricUnipotentRadical`, which includes greatestness over
the ground field and its algebraic closure. The hypothesis `hQ` says that `q`
represents the full dynamic parabolic of `(-eta) ≫ a ≫ l' ≫ p'`, where a
cocharacter is converted to a group-scheme homomorphism by
`CommGroupScheme.groupHom`. This is an equality of subgroup functors on all
test schemes, together with monicity of the representing map. It is not merely
a statement about rational points. Algebraic parabolicity of `Q` is not asserted
by this adapter.

No restriction on characteristic, splitness or quasisplitness of `G`, or positive
split rank is imposed.

## Real threshold regions

Let `B` be any real bilinear form on the full real character space
`RealTorusSpace.Vstar A = ℝ ⊗[ℤ] characterLattice A`, and let `R : ℝ`.
The actual region is

```
intertwiningRegion i B (range (n ≫ p)) (range (v ≫ q)) R.
```

`intertwiningRegion_eq_dynamic_commonLevi` identifies this region exactly
with the dynamic region for `nu` and `-eta`, both using the single embedding
`i`. Its proof rewrites the full ambient-image equalities
`r.range_comp_radical_eq hn` and `r'.range_comp_oppositeRadical_eq hQ hv`,
then rewrites the common-Levi equality. Thus arbitrary supplied radicals are
allowed; no choice of a canonical representative is imposed on `n` or `v`.

`mem_intertwiningRegion_commonLevi` gives the precise membership criterion:
for every `alpha` in the actual `relativeRoots i`,

```
0 < latticePairing A alpha nu →
latticePairing A alpha eta < 0 →
R < B x ((1 : ℝ) ⊗ₜ[ℤ] alpha).
```

This is the full intersection of the two actual radical supports. There is no
restriction to simple, reduced or indivisible roots, so multipliable roots are
retained. The proof uses the preceding equality and
`mem_intertwiningRegion_dynamic`.

`intertwiningRegion_commonLevi_nonempty` adds `B.Nondegenerate` and proves
nonemptiness for every real `R`. After the same region equality it applies
`intertwiningRegion_dynamic_nonempty`. That imported result represents pairing
with the integral positive direction `nu` by a real vector using the
nondegenerate form and scales the vector. Every relevant positive integral
pairing is at least one. Empty root intersections, including rank zero, are
covered without a separate nonemptiness premise.

## Canonical continuous characters

Now `F : Type u` is a nonarchimedean local field with its valuation and topology,
including possible positive characteristic. The character section explicitly
carries `[IsAffine M.X.left]` and `[LocallyOfFiniteType M.X.hom]` to form the
canonical rational-point topology and the continuous-character equivalence.
These are properties of the specified Levi: they follow from
`r.isCompatible.levi.isConnectedReductive.isAffineHom` and its `smooth` field.
They impose no assertion about all centralizers or all reductive groups. The
membership theorem and ambient-region equality do not need the
`LocallyOfFiniteType` instance, and explicitly omit it.

The local rational-point topology is exactly `rationalPointTopology F M.X`.
`parabolicUnramifiedIntertwiningRegion r B n q v R` is a subset of the existing
continuous unramified-character space

```
unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul).
```

It is defined by `canonicalUnramifiedIntertwiningRegion`, using the ambient
images of the actual supplied radical maps. The definition itself only needs
the first compatible presentation and the supplied maps, not `r'`, `hM`,
`hn`, `hQ` or `hv`.

For such a character `chi`, set

```
x = SplitTorus.normalizedRealPart
      r.isCompatible.splitComponent.1.isSplitSubtorus.1
      (chi.val.toMonoidHom.comp (rationalPoints.map a)).
```

`mem_parabolicUnramifiedIntertwiningRegion` states that membership is
exactly the full strict-root criterion above with this `x`. It is the
real-parameter membership theorem applied to the normalized real part of the
restriction of the same continuous character.

`exists_positiveImageCharacter_mem_parabolicUnramifiedIntertwiningRegion`
assumes `B.Nondegenerate` and constructs a witness of the specific form

```
rationalCanonicalImageUnramifiedContinuousEquiv M
  (rationalImagePositiveCharacter M psi)
```

for some `psi : rationalImageRealFunctionals M`. The proof first obtains
nonemptiness of the actual real region. The split-component property and the
connected reductivity of this `M` give injectivity of the actual valuation-image
map by `rationalValuationImageMap_injective`. The existing extension theorem
`exists_positiveImageCharacter_mem_intertwiningRegion_of_injective` then gives
a positive character of that actual image. The canonical continuous-character
equivalence transports it to the displayed witness; its underlying pullback
makes the required membership definitionally the same predicate. No selected
free lattice or assumed extension of characters replaces the actual image.
`parabolicUnramifiedIntertwiningRegion_nonempty` records the resulting set
nonemptiness.

## One ambient Weyl form and exact comparison

Let `r.data.f : A ⟶ r.data.T` and `r.data.i : r.data.T.toGrp ⟶ G` be the
first presentation's actual factorization, with

```
CommGroupScheme.groupHom r.data.f ≫ r.data.i = a ≫ l ≫ p.
```

The ambient embedding is monic by the maximal split-subtorus field of the
presentation. The factor map is monic because `a`, `l` and `p` are monic and
the displayed composite is monic. These local instances are proved in the
file. The ambient section also explicitly assumes
`[Fintype (relativeWeylGroup r.data.i)]`.

`parabolicWeylUnramifiedIntertwiningRegion r n q v R` specializes the entry
region to `weylInducedCharacterForm`, constructed by pulling the one ambient
relative Weyl-invariant positive form back along the orthogonal lift of the
actual character-restriction map. It does not independently choose another
local form.

`parabolicWeylUnramifiedIntertwiningRegion_eq_ambient` proves equality of
sets of the same canonical continuous characters:

```
parabolicWeylUnramifiedIntertwiningRegion r n q v R =
  weylAmbientUnramifiedIntertwiningRegion hA hT r.data.f r.data.i a nu eta R.
```

Here `hA` and `hT` are the split-torus proofs supplied by the split component
and maximal split subtorus. The ambient set tests the orthogonal lift of the
character's normalized real part on every ambient root in the dynamic support
intersection of the pushed-forward cocharacters. The proof first applies
`weylAmbientUnramifiedIntertwiningRegion_eq`, which already compares all
ambient and local roots under restriction, including merged restrictions.
It then applies the actual supplied-radical region equality and the exact
factorization identity. No extra root-correspondence or form-compatibility
premise is inserted.

`exists_positiveImageCharacter_mem_parabolicWeylUnramifiedIntertwiningRegion`
uses the general witness theorem with
`weylInducedCharacterForm_nondegenerate`. Consequently
`parabolicWeylUnramifiedIntertwiningRegion_nonempty` holds for every real
threshold, under the same supplied-radical hypotheses.

## Scope

These definitions and their intrinsic laws provide exact parameter-region
adapters. They retain the two compatible presentations, the equality of actual
Levi embeddings, the negative dynamic representative and both supplied-radical
predicates. They do not prove presentation existence or independence, algebraic
parabolicity of the negative representative, finite length of representations,
convergence or continuation of intertwiners, or any Plancherel conclusion.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
