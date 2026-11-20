# Splitting off the multiplicative part over a perfect field

This internal derived unit proves the existence clause of Milne 2017,
Theorem 16.13(b). Let `k` be a perfect field and `G` a commutative group
scheme over `Spec k` that is affine and locally of finite type. Then there are
a unipotent closed subgroup `u : U ⟶ G` and a closed subgroup `s : S ⟶ G` of
multiplicative type such that the multiplication map
`subgroupMultiplication u s : U × S ⟶ G` is an isomorphism
(`exists_multiplicativeUnipotentDecomposition`).

The main intermediate result is `exists_retraction_of_perfectField`. Suppose
`G` is commutative and affine over a perfect field, `s : S ⟶ G` is a closed
subgroup of multiplicative type, and `q : G ⟶ Q` is an fppf quotient map with
kernel the range of `s` and with `Q` affine and unipotent. Then `s` has a
retraction homomorphism `r : G ⟶ S` with `s ≫ r = 𝟙 S`.

## Route

1. **Group-like elements in a graded Hopf algebra** (section `Hopf`). Let
   `A` and `B` be commutative Hopf algebras over a field `K`, and let
   `π : A → K[N]` be a bialgebra map to the group algebra of an abelian group
   `N`. The map `π` grades `A` by `N`
   (`GroupAlgebraCoaction.grade`). Let `φ : B → A` be an injective bialgebra
   map whose image contains the degree-zero part.
   - `eq_one_of_isGroupLikeElem`: if `B` has the property
     `Unipotent.OneMemStable` (the Hopf form of unipotence), then the only
     group-like element of `B` is `1`. The line spanned by a group-like `b`
     is stable under right translation, so it contains `1`, and the counit
     fixes the scalar.
   - `eq_one_of_mem_grade_zero` and `degree_injective`: a group-like element of
     degree zero comes from `B`, and its preimage is group-like because `φ` is
     injective and tensor products over a field are flat. So it equals `1`,
     which means the degree map on group-like elements
     (`CentralDiagonalizableExtensionHopf.degree π`) is injective.
   - `degree_surjective`: if `K` is algebraically closed, `A` is
     cocommutative and `π` is surjective, then every degree is reached. The
     Library's `GroupAlgebraCoaction.exists_isGroupLikeElem_mem_grade`
     provides a group-like element in each nonzero graded piece.
   - `sectionHom`, `sectionHom_single` and `comp_sectionHom`: an additive map
     `e : N → GroupLike A` that inverts the degree gives the bialgebra map
     `K[N] → A`, `Xⁿ ↦ e n`, through `MonoidAlgebra.liftGroupLikeBialgHom`.
     It is a section of `π`.
   - `eq_of_comp_eq_id`: when the degree map is injective, `π` has at most
     one bialgebra section. A section sends `Xⁿ` to a group-like element of
     degree `n`.
2. **Unique retraction over an algebraically closed field**
   (`exists_unique_retraction_of_isAlgClosed`). Let `E` be commutative and
   affine over an algebraically closed field `K`, `z : Z ⟶ E` a closed
   subgroup with `Z ≅ D(N)` diagonalizable, and `p : E ⟶ T` an fppf
   quotient map with kernel the range of `z` and with `T` affine and
   unipotent. The proof passes to coordinate Hopf algebras with the Library's
   `AffineCoordinates.hopfSpecIso` and the full faithfulness of `hopfSpec`.
   The subgroup `z` becomes a surjection `π : O(E) → K[N]`
   (`CentralExtensionHopfSpec.surjective_of_isClosedSubgroup`). The quotient
   `p` becomes a faithfully flat, hence injective, map `φ : O(T) → O(E)`. The
   degree-zero part of the grading lies in the image of `φ`
   (`exists_eq_of_mem_grade_zero`). That lemma repeats the proof of the
   `invariants` field of `CentralExtensionHopfSpec.isExtension_diagonalizable`
   with `O(T)` in place of the specific quotient algebra, using
   `CentralExtensionHopfSpec.exists_eq_of_lTensor_comul_eq`. `O(T)` has the
   property `OneMemStable` because `T` is unipotent
   (`oneMemStable_hopfAlgebra`, from
   `Unipotent.oneMemStable_of_isUnipotent_cogroup`). `O(E)` is cocommutative
   because `E` is commutative. Step 1 then gives exactly one section of `π`.
   Under `hopfSpec` the sections of `π` correspond to the retractions of `z`.
3. **Descent to a perfect field** (`exists_retraction_of_perfectField`). Let
   `L` be an algebraic closure of `k`. Since `k` is perfect, `L/k` is Galois.
   After base change to `L`, `S_L` is of multiplicative type and hence
   diagonalizable (`MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`).
   Base change also preserves closed subgroups, fppf quotients with their
   kernels, and unipotence. Step 2 gives a unique retraction `r` of `s_L`.
   For each `σ ∈ Gal(L/k)`, the Galois conjugate of `r`, transported by the
   Library's `descentBaseChangeIso`, is again a retraction of `s_L`, so it
   equals `r`. The Library's `Descent.GaloisHom.hom` then descends `r` to a
   homomorphism `G ⟶ S` whose base change is `r`. The identity `s ≫ r = 𝟙`
   holds after base change, and base change along the fpqc morphism
   `Spec L → Spec k` is faithful, so it holds over `k`.
4. **Split extensions** (section `Split`). Let `r : G ⟶ S` be a retraction
   of `s`.
   - `isIso_subgroupMultiplication_kernelι`: multiplication
     `ker r × S → G` is the Library's product isomorphism
     `CommutativeSplitProduct.iso r s`, so it is an isomorphism.
   - `isUnipotent_kernel_of_retraction`: `ker r` is unipotent. The projection
     `p = commutingFactorRetraction (kernelι r) s : G ⟶ ker r` kills the range
     of `s`, so it vanishes on the kernel of `q`. Fppf descent of
     homomorphisms (`FppfHomDescent.hom`) factors it as `q ≫ p'` with
     `p' : Q ⟶ ker r`. Since `p` restricted to `ker r` is the identity
     (`comp_commutingFactorRetraction`), `p'` is a split epimorphism on
     underlying schemes. Unipotence passes to its target
     (`IsUnipotent.of_epi`).
5. **Existence** (`exists_multiplicativeUnipotentDecomposition`). The
   companion unit `MultiplicativePartExistence` provides
   `exists_multiplicativePart`: a closed subgroup `s : S ⟶ G` of
   multiplicative type with an fppf quotient `q : G ⟶ Q` whose kernel is the
   range of `s` and whose target `Q` is affine and unipotent. Step 3 gives a
   retraction `r`, and step 4 shows that `U = ker r` with `u = kernelι r`
   gives the decomposition. `kernelι r` is a closed subgroup by
   `isClosedSubgroup_kernelι`.

## Provenance

The statement of `exists_multiplicativeUnipotentDecomposition` is the
existence part of Milne, *Algebraic Groups* (2017), Theorem 16.13(b)
(printed p. 328). Milne uses uniqueness and the Galois extension `k^a/k` to
reduce to an algebraically closed field. There, the extension
`e → G_s → G → G/G_s → e` splits by his Theorem 15.37. The route here is
internal and does not use 15.37. Over the
algebraic closure, the coordinate Hopf algebra is graded by the characters
of `S`. Each graded piece has exactly one group-like element, so the
retraction exists and is unique. Uniqueness makes the retraction Galois
invariant, and it descends with the Library's `Descent.GaloisHom`. The
Galois-descent step follows Milne's outline. The Library lemmas reused are
`GroupAlgebraCoaction.exists_isGroupLikeElem_mem_grade`, the
`CentralDiagonalizableExtensionHopf` degree map, `CentralExtensionHopfSpec`,
`CommutativeSplitProduct`, `CommutingFactorRetraction` and
`FppfHomDescent`.
