# Split-torus homomorphisms as Hopf points

Module `Langlands.GroupScheme.HomScheme.SplitTorusHopfPoint`, namespace
`Langlands.GroupScheme.HomScheme`.

The module turns actual group-scheme homomorphisms from the split torus `𝔾_m^I` to an affine
group scheme `G` over `Spec R`, after base change to `Spec C`, into Hopf points
`O(G) → C ⊗[R] R[ℤ^I]`. It also reads closed immersions, base change and inclusions of ranges
on these Hopf points. It is infrastructure for the task "Prove smooth moduli of actual closed
torus subgroups" (SGA 3, Exp. XI, 4.1, torus case), where the chart construction works with Hopf
points.

Notation: `RelativeHom H G T` is a homomorphism `H_T ⟶ G_T` of group schemes over `T`
(`HomScheme.Universal`). `evaluate a i` is its base change along `a : T' ⟶ T`
(`HomScheme.Universal`). `transport eH eG i` composes with isomorphisms of source and target, and
`pointEquiv A P C` identifies `RelativeHom (hopfGroup R P) (hopfGroup R A) (specOver R C)` with
Hopf points `A →ₐ[R] C ⊗[R] P` (`HomScheme.AffineTest`, `HomScheme.FiniteSourceHom`).
`IsClosedSubgroup j` says that the underlying scheme map of `j` is a closed immersion.

## Closed immersions under transport (`section ClosedImmersion`)

`isClosedSubgroup_transport_iff eH eG i`: for isomorphisms `eH : H' ≅ H` and `eG : G ≅ G'`,
`transport eH eG i` is a closed subgroup exactly when `i` is. The underlying scheme map of the
transport is `i` composed on both sides with isomorphisms, and closed immersions are stable under
composition with isomorphisms on either side.

## Ranges (`section Range`)

- `range_le_range_iff j j'`: for homomorphisms `j : K ⟶ G` and `j' : K' ⟶ G` over a scheme `B`,
  `SubgroupFunctor.range j ≤ SubgroupFunctor.range j'` holds exactly when the underlying scheme
  map of `j` factors through that of `j'`. The forward direction applies the inclusion to the
  identity point of `K`. The converse composes points with the factorization.
- `range_transport_le_iff eH eG i i'`: transport along fixed isomorphisms preserves and reflects
  inclusions of ranges. A factorization `z` for the transported maps gives `a⁻¹ ≫ z ≫ a` for the
  original maps, where `a` is the source isomorphism, and conversely.
- `familyHom_eq i a`: the Library subgroup family `TorusSubgroupModuli.familyHom i a` equals the
  source pullback comparison isomorphism followed by `evaluate a i`. Both are built from the same
  base change and comparison maps.
- `evaluate_eq_range i a`: the Library evaluation `TorusSubgroupModuli.evaluate i a` of `i` as a
  family of subgroups equals `SubgroupFunctor.range (evaluate a i)`. This follows from
  `familyHom_eq`, since precomposing with an isomorphism does not change a range
  (`SubgroupFunctor.range_iso_comp`).

## Hopf spectra (`namespace FiniteSource`)

Here `A` and `P` are commutative Hopf algebras over `R`, `C` is an `R`-algebra, and `f`, `f'` are
Hopf points `A →ₐ[R] C ⊗[R] P`. For such a point, `AlgHom.liftEquiv R C A (C ⊗[R] P) f` is its
`C`-linear extension `C ⊗[R] A → C ⊗[R] P`. The underlying scheme map of
`(pointEquiv A P C).symm f` is, by definition, `Spec` of this extension, conjugated by the
isomorphisms `tensorIso` between the base changes and the spectra of `C ⊗[R] P` and `C ⊗[R] A`.

- `isClosedSubgroup_pointEquiv_symm_iff f`: the homomorphism attached to `f` is a closed subgroup
  exactly when the `C`-linear extension of `f` is surjective. The forward direction is the
  Library `CentralExtensionHopfSpec.surjective_of_isClosedImmersion`. The converse is Mathlib's
  `IsClosedImmersion.spec_of_surjective`.
- `range_pointEquiv_symm_le_iff f f'`: the range attached to `f'` lies in the range attached to
  `f` exactly when some ring endomorphism `ψ` of `C ⊗[R] P` satisfies `ψ ∘ φ = φ'`. Here `φ` and
  `φ'` are the `C`-linear extensions of `f` and `f'`. A factorization of scheme maps between
  affine schemes is `Spec` of a ring map, because `Spec` is fully faithful (`Spec.preimage`,
  `Spec.map_injective`).
- `range_pointEquiv_symm_le_iff_ker f f' hf`: if `φ` is surjective, the condition above is
  `ker φ ≤ ker φ'`. Given the kernel inclusion, `ψ` is the map `C ⊗[R] P ≅ (C ⊗[R] A)/ker φ → C ⊗[R] P`
  induced by `φ'`.
- `range_pointEquiv_symm_eq_iff_ker f f' hf hf'`: if both extensions are surjective, the two
  ranges are equal exactly when the two kernels are equal.
- `range_pointEquiv_symm_le_of_comp τ f f' h`: if `f' = τ ∘ f` for a `C`-algebra endomorphism `τ`
  of `C ⊗[R] P`, then the range attached to `f'` lies in the range attached to `f`. The
  extension of `f'` is `τ` composed with the extension of `f`.

## The split torus (`namespace SplitTorusPoint`)

Here `I` is a finite type with decidable equality and `G` is a group scheme over `Spec R` with
`IsAffine G.X.left`. `AffineCoordinates.hopfAlgebra G` is the Library coordinate Hopf algebra
`O(G)`.

- `splitTorusHopfIso R I : hopfGroup R (AddMonoidAlgebra R (I → ℤ)) ≅ splitTorus (Spec R) I`
  composes the Library isomorphisms `Diagonalizable.hopfSpecIso` (the Hopf spectrum of `R[Λ]` is
  the diagonalizable group `D(Λ)`) and `Diagonalizable.splitIso` with the identity of `ℤ^I`
  (`D(ℤ^I)` is the split torus, the finite product of copies of `𝔾_m`).
- `splitPointEquiv G C` is the equivalence between
  `RelativeHom (splitTorus (Spec R) I) G (specOver R C)` and Hopf points
  `O(G) →ₐ[R] C ⊗[R] R[ℤ^I]`. It is the inverse of `transportEquiv` along `splitTorusHopfIso`
  and `coordinateIso G` (from `HomScheme.FiniteDiagonalizableHom`), followed by `pointEquiv`.
  `splitPointEquiv_symm_apply` records the inverse as a `transport`. No finiteness of the Hopf
  algebra `R[ℤ^I]` is needed: `pointEquiv` is defined for arbitrary Hopf algebras.
- `evaluate_splitPointEquiv_symm g f`, naturality: for an `R`-algebra map `g : C → D`, base change
  along `specMap g : Spec D ⟶ Spec C` sends the homomorphism of `f` to the homomorphism of the
  pushed-forward point `pushPoint R g f` (the map `g ⊗ id` after `f`, from
  `Langlands.Algebra.FiniteBialgebraHom`). It follows from `evaluate_transport` and
  `evaluate_specMap`. `splitPointEquiv_evaluate` states the same on Hopf points.
- `isClosedSubgroup_splitPointEquiv_symm_iff f`: the homomorphism of `f` is a closed subgroup
  exactly when the `C`-linear extension `C ⊗[R] O(G) → C ⊗[R] R[ℤ^I]` of `f` is surjective.
- `evaluate_splitPointEquiv_symm_eq_range g f`: the Library evaluation
  `TorusSubgroupModuli.evaluate` of the homomorphism of `f` along `specMap g` is the range of
  the homomorphism of `pushPoint R g f`.
- `range_splitPointEquiv_symm_le_iff`, `range_splitPointEquiv_symm_le_iff_ker` and
  `range_splitPointEquiv_symm_eq_iff_ker` are the three range criteria of `FiniteSource` for
  split-torus homomorphisms. They are transported by `range_transport_le_iff`. In particular, two
  closed split-torus homomorphisms over `Spec C` have the same range exactly when the kernels of
  the `C`-linear extensions of their Hopf points are equal.
- `range_splitPointEquiv_symm_twist_le t f h`: let `t : ℤ^I →+ ℤ^I` be an additive endomorphism
  of the character lattice. Let `f_t` be `f` followed by
  `Algebra.TensorProduct.map (AlgHom.id R C) (AddMonoidAlgebra.mapDomainAlgHom R R t)`, and let
  `h` be a proof that `f_t` is a Hopf point. Then the range attached to `f_t` lies in the range
  attached to `f`. This is `range_pointEquiv_symm_le_of_comp` with `τ = id_C ⊗ R[t]`.
- `range_splitPointEquiv_symm_twist_eq t f h`: for an additive automorphism `t : ℤ^I ≃+ ℤ^I`, the
  range attached to `f_t` equals the range attached to `f`. The reverse inclusion uses
  `τ = id_C ⊗ R[t⁻¹]`, since `R[t⁻¹] ∘ R[t]` is the identity (`mapDomainAlgHom_comp`), checked on
  pure tensors.

The twist lemmas take the Hopf-point property of `f_t` as the hypothesis `h`. The module does
not prove that twisting preserves Hopf points.

## Provenance

The module is internal infrastructure; it formalizes no single cited result. Its content is the
standard description of homomorphisms from a split torus to an affine group scheme by
coordinate rings: a homomorphism `𝔾_m^I → G` over `Spec C` is a map of Hopf algebras
`C ⊗ O(G) → C[ℤ^I]`, and such a homomorphism is a closed immersion exactly when this map is
surjective. The range and twist criteria are elementary consequences, written for the chart
construction of the task named above.
