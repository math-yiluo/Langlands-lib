# Relative-root restriction fibers are single Galois orbits

This file proves that, for a torus `T ⊆ G` with largest split subtorus
`f : S ⟶ T`, every nonempty restriction fiber of the actual roots of `T_L` in
`G_L` is one ordinary Galois orbit. Here `L/k` is a finite Galois extension
splitting `T`. It then turns such a fiber into the set of `k`-embeddings of
the stabilizer field of one of its roots.

Notation: `b = algebraBaseMap k L`; `T_L`, `S_L`, `G_L`, `f_L` and `j_L` are
base changes along `b`. `roots j_L` is the actual root set of `T_L` in `G_L`
and carries the ordinary Galois action `rootsGaloisAction` (from
`Rational/RootGaloisOrbits`). `rootRestrictionFiber k L j f a` is the set of
roots `β` with `f_L ≫ β = a_L` for a character `a` of `S`.
`CharacterAveraging.galoisOrbitSum k L T χ` is `∑ σ, σ • χ` for a character
`χ` of `T_L`.

## Character lemmas

- `IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq`: assume `T` is a
  torus, affine and locally of finite type over `k`, that `f` is its largest
  split subtorus, and that `L/k` is finite Galois. Then two characters `χ, ψ`
  of `T_L` with `f_L ≫ χ = f_L ≫ ψ` have equal Galois orbit sums. The proof
  applies the Library lemma
  `IsLargestSplitSubtorus.galoisOrbitSum_character_eq_zero` to `χ - ψ` and
  uses additivity of the orbit sum.
- `galoisOrbitSum_ne_zero_of_restrict_ne_zero`: if `S` is split and
  `f_L ≫ χ ≠ 0`, the orbit sum of `χ` is nonzero. Write `f_L ≫ χ = c_L` by
  surjectivity of character base change for the split torus `S`. Galois
  transport commutes with restriction and fixes base-changed characters, so
  `f_L ≫ (orbit sum of χ) = (|Gal| • c)_L`. Base change is injective and the
  character lattice of a split torus is torsion-free, so a vanishing orbit
  sum would force `c = 0`, i.e. `f_L ≫ χ = 0`.

## Fiber transitivity

`rootOrbit_eq_restrictionFiber` assumes:

- `L/k` finite Galois, `G` affine and locally of finite type, `T` affine and
  locally of finite type;
- `S` split and `f` the largest split subtorus of `T`;
- `T_L` split and `j_L` a closed immersion;
- a finite root datum `P` with `IsRootDatumOf j_L P`;
- `hzero`: no actual root `β` of `j_L` satisfies `f_L ≫ β = 0`.

Then for every `β` in `rootRestrictionFiber k L j f a`,
`MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a`.

Proof. The Library inclusion `rootOrbit_subset_restrictionFiber` gives one
direction. For the other, let `γ` be in the fiber. The Library action
`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus` makes the Galois
group act on `P` by root-datum automorphisms. Its index action is
`galoisRootIndexEquiv`, which is compatible with the character Galois action
(`galoisRootIndexEquiv_root`). So the combinatorial orbit sum
`P.rootOrbitSum ρ m` equals the character orbit sum of `P.root m`. The roots
`β` and `γ` have the same restriction, hence equal orbit sums by the first
character lemma. By `hzero` and the second character lemma, every root has a
nonzero orbit sum. `RootPairing.exists_smul_eq_of_rootOrbitSum_eq` (from
`Reductive/RootDatumOrbitSums`) then gives `σ` with `σ • β = γ`.

### Deriving `hzero`

`root_restrict_ne_zero_of_torusCentralizer` assumes `S` split, `T_L` split,
`G` and `T` affine and locally of finite type, and that `j : T ⟶ G`
represents the full centralizer `torusCentralizer (f ≫ j)`. It shows
`f_L ≫ β ≠ 0` for every actual root `β` of `j_L`. Proof:

1. Let `ζ = centralizingCocharacter hS (f ≫ j) ≫ f`. By
   `centralizingCocharacter_spec`, the dynamic centralizer of `ζ ≫ j` is
   `torusCentralizer (f ≫ j)`.
2. Base change (`cocharacterLattice.groupHom_baseChange_dynamic`,
   `Dynamic.baseChangeCocharacter_comp`, `Dynamic.centralizer_baseChange`)
   and `IsRepresentedBy.baseChange` show that `j_L` represents the dynamic
   centralizer of `ζ_L ≫ j_L`.
3. `relativeRoots_centralizer_factor dynamicLie`, applied with centralizer
   torus inclusion `𝟙 T_L`, identifies the roots of `𝟙 T_L` with the roots of
   `j_L` that pair to zero with `ζ_L`.
4. If `f_L ≫ β = 0`, then `⟨β, ζ_L⟩ = 0`, because `ζ_L` factors through
   `f_L`. So `β` would be a root of `𝟙 T_L`. The identity of the commutative
   group `T_L` is central (`isCentral_to_commGroupScheme`), so
   `root_restrict_eq_zero_of_isCentral` forces `β = 0`. Roots are nonzero, a
   contradiction.

`rootOrbit_eq_restrictionFiber_of_torusCentralizer` is the ambient form. Its
hypotheses are: `f ≫ j` is a maximal split torus of `G`; `j` is a closed
subgroup; `j` represents `torusCentralizer (f ≫ j)`; `T_L` is split; and
`IsRootDatumOf j_L P`. Under these, every nonempty restriction fiber is one
Galois orbit. It combines the two results above. `f` is maximal split in `T`
by `IsMaximalSplitTorus.of_comp`, and hence `f` is the largest split subtorus
by `IsMaximalSplitTorus.isLargestSplitSubtorus`. The base change of a closed
subgroup is closed (`IsClosedSubgroup.baseChange`).

## Fibers as field embeddings

For `L/k` finite Galois, a character `a` of `S`, a root `β` and a proof
`horbit` that the orbit of `β` equals the fiber of `a`,
`rootRestrictionFiberEmbeddingEquiv k L f j a β horbit` is the equivalence
from the fiber to `rootOrbitField k L j β →ₐ[k] L`. Here `rootOrbitField`
is the fixed field of the stabilizer of `β`. It composes the subtype
equivalence induced by `horbit` with the Library's `rootOrbitEmbeddingEquiv`.

- `rootRestrictionFiberEmbeddingEquiv_symm_comp`: postcomposing an embedding
  with `σ` corresponds to the Galois action of `σ` on the root.
- `rootRestrictionFiberEmbeddingEquiv_symm_val`: the inverse has the same
  underlying roots as the inverse of `rootOrbitEmbeddingEquiv`.

## Provenance

Internal. Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
§2.6(b), printed page 96, state without proof that, in a quasi-split group,
the fibers of restriction from absolute roots to relative roots are Galois
orbits. In the quasi-split case the centralizer of a maximal split torus is a
maximal torus. Here that centralizer condition is the hypothesis `hcent`, and
the existence of the root datum `P` is the hypothesis `hP`. The argument
avoids the classification of root systems by using the orbit-sum criterion
from `Reductive/RootDatumOrbitSums`.
