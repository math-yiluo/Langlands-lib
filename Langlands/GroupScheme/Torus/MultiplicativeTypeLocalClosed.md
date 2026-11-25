# Closed immersions from isotrivial groups of multiplicative type over local bases

This internal helper module proves the closed-immersion clause (3) of
[`MultiplicativeTypeCompleteLocalLiftStatement`](MultiplicativeTypeCompleteLocalLiftStatement.md)
(Conrad, *Reductive group schemes*, Corollary B.3.5, p.292). It proves the clause in more
generality than the statement needs. The base is `Spec A` for any local ring `A`;
completeness and noetherianity are not used. `H` is any group over `Spec A` that becomes
diagonalizable after a finite étale surjective base change. `G` is any group over `Spec A`
with `IsAffineHom G.X.hom`; smoothness is not used. The proof route differs from Conrad's,
which goes through `ker f = 1` (Lemma B.1.3), Nakayama on fibres and a separate argument
at non-closed points. Here the clause is reduced to the surjectivity of a map of Hopf
algebras.

## Algebra

Throughout, `R` is a commutative ring, `B` is an `R`-bialgebra and `M` is an additive
commutative monoid. `DiagonalCoalgebraLocus.scalarExtension φ K : K ⊗[R] B → K[M]` is the
scalar extension of `φ : B → R[M]` (`R[M]` = `AddMonoidAlgebra R M`).

- `exists_coefficient_ne_zero`: if `K` is a nontrivial `R`-algebra and the scalar
  extension of the algebra map `φ : B → R[M]` to `K` is surjective, then for each `m : M`
  some `b : B` has `(φ b).coeff m` with nonzero image in `K`. Proof: otherwise the
  degree-`m` coefficient of every element of the scalar extension's image vanishes
  (induction on `K ⊗[R] B`), contradicting that `single m 1` is in the image.
- `single_one_mem_range_of_forall_maximal`: let `φ : B → R[M]` be a bialgebra map. If
  the scalar extension of `φ` to `R ⧸ n` is surjective for every maximal ideal `n` of `R`,
  then `single m 1` lies in the range of `φ` for every `m`. Proof: the set
  `P = {r | single m r ∈ range φ}` is an ideal of `R`. For every `b`,
  `single m ((φ b).coeff m)` lies in the range of `φ`; this is the Library's
  `DiagonalCoalgebraImage.single_coefficient_mem_range`, which uses the bialgebra
  property. So `P` contains all degree-`m` coefficients. If `P ≠ ⊤`, it lies in a maximal
  ideal `n`. Then all these coefficients vanish in `R ⧸ n`, contradicting
  `exists_coefficient_ne_zero`. Hence `1 ∈ P`.
- `surjective_of_forall_maximal`: under the same hypothesis `φ` is surjective. All
  monomials are in the range, so `DiagonalCoalgebraLocus.surjective_of_generators_mem`
  applies with generating set `M`.

## Transport

- `isClosedSubgroup_iff_of_comm`: given isomorphisms `a : H ≅ H'` and `b : G ≅ G'` with
  `i ≫ b.hom = a.hom ≫ j`, `IsClosedSubgroup i ↔ IsClosedSubgroup j`. Closed immersions
  are stable under composition with isomorphisms on either side.
- `isClosedSubgroup_baseChange_comp_iff`: for `a : S' ⟶ S`, `b : S'' ⟶ S'` and
  `i : H ⟶ G`, base change of `i` along `b ≫ a` is a closed subgroup inclusion if and
  only if the iterated base change along `a` and then `b` is one. It uses
  `baseChangeCompIso` and the naturality of the composite pullback isomorphism.

## Local residue maps

Let `A` be a local ring and `R` an integral `A`-algebra.

- `residueLift R n`: for a maximal ideal `n` of `R`, the ring map from the residue field
  of `A` to `R ⧸ n`. It is well defined because `n` lies over a maximal ideal of `A`
  (integrality), which is the maximal ideal of the local ring `A`.
- `specMap_residueLift`: `Spec (R ⧸ n) → Spec R → Spec A` equals
  `Spec (R ⧸ n) → Spec k → Spec A`, where the second map is `Spec.map` of `residueLift`.

## Main theorems

`isClosedSubgroup_of_finite_split`. Let `A` be a local ring and `R` a finite `A`-algebra
with `Spec R → Spec A` étale and surjective. Let `H, G` be groups over `Spec A` with
`IsAffineHom G.X.hom`, and suppose `H_R` is diagonalizable. If the special fibre
`(GroupScheme.baseChange (Spec.algebraMap A k)).map f` of a homomorphism `f : H ⟶ G` is
a closed immersion, then `f` is one. Proof:

1. By `IsClosedSubgroup.of_baseChange_of_etale` (Library, étale descent of closed
   immersions) it suffices to show that `f_R` is a closed immersion.
2. Diagonalizability gives `H_R ≅ D_R(Λ)`. The Library's `Diagonalizable.hopfSpecIso` and
   `Diagonalizable.relativeModelIso` identify `D_R(Λ)` with the standard diagonal source,
   so it suffices that `i : diagonalSource R Λ ⟶ G_R` is a closed immersion, where `i` is
   the composite of this identification with `f_R` (`isClosedSubgroup_iff_of_comm`).
3. `G_R` is affine. Let `φ = diagonalCoordinateMap i`, the bialgebra map from the Hopf
   algebra of `G_R` to `R[Λ]`. For each maximal ideal `n` of `R`, `diagonal_closed_iff`
   turns the scalar extension of `φ` to `R ⧸ n` being surjective into the base change of
   `i` along `Spec (R ⧸ n) → Spec R` being a closed immersion. By
   `closed_baseChange_precomp_iso_iff`, `isClosedSubgroup_baseChange_comp_iff` and
   `specMap_residueLift`, this base change is the base change of the special fibre
   `f_k` along `Spec (R ⧸ n) → Spec k`. It is a closed immersion because `f_k` is one and
   `IsClosedSubgroup.baseChange` applies.
4. `surjective_of_forall_maximal` shows that `φ` is surjective, so `Spec φ` is a closed
   immersion (`IsClosedImmersion.spec_of_surjective`). By `diagonalCoordinateMap_map`,
   `Spec φ` is `i` followed by the isomorphism `(AffineCoordinates.hopfSpecIso G_R).inv`,
   so `i` is a closed immersion.

`isClosedSubgroup_of_isotrivial`. This is the same conclusion when the splitting is given
as in [`MultiplicativeTypeQuasiIsotrivialStatement`](MultiplicativeTypeQuasiIsotrivialStatement.md)
clause (2): some `p : S' ⟶ Spec A` with `IsFinite p`, `Etale p`, `Surjective p` and the
base change of `H` along `p` diagonalizable. `S'` is affine because `p` is affine. With
`R = Γ(S', ⊤)` and `q = S'.isoSpec.inv ≫ p = Spec.algebraMap A R`, `R` is a finite
`A`-algebra (`IsFinite.SpecMap_iff`), and `q` is étale and surjective. The base change of
`H` along `q` is diagonalizable via `baseChangeCompIso` and
`RelativeMultiplicativeType.IsDiagonalizable.baseChange`. Then
`isClosedSubgroup_of_finite_split` applies.
