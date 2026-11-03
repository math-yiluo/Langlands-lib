# Fixed vectors for the relative spectrum of a Hopf algebra

Author: Worker 1419 designed and implemented this module and wrote this note, as part of
task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the absence of zero Lie
weights). Over a field `k`, it turns the Library predicate `IsUnipotent` for the affine
group scheme `Spec A = (hopfSpec (CommRingCat.of k)).obj (op A)` of a commutative Hopf
algebra `A` into a statement about matrices of elements of `A`. Every square matrix
`a = (aᵢⱼ)` of elements of `A` with

- `Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` (comultiplication is matrix multiplication), and
- `ε(aᵢⱼ) = δᵢⱼ` (the counit is the identity matrix)

has a nonzero vector `v : n → k` with `∑ⱼ vⱼ aᵢⱼ = vᵢ · 1` for all `i`.

Everything is in namespace `Langlands.GroupScheme.UnipotentMatrixCriterion`.

## Provenance

This is internal infrastructure for the proof of
`RelativeRoot.TorusActionSplitUnipotenceStatement`. Mathematically it is the standard
dictionary between finite-dimensional representations of an affine group scheme and
square matrices of coefficients in its Hopf algebra (a matrix as above is the coefficient
matrix of the representation `g ↦ (g(aᵢⱼ))` on `kⁿ`). No source states it in this form,
so none is cited. The proof is assembled from the Library's
`Corepresented` machinery and `UnipotentMatrixCriterion.Coordinates`.

## Spec A as a corepresented group functor

Let `R : CommRingCat.{u}` and `A : CommHopfAlgCat.{u} R`.

- `hopfCogroup A : Grp (CommAlgCat.{u} R)ᵒᵖ` is the cogroup object of commutative
  `R`-algebras given by `A`, the image of `A` under Mathlib's equivalence
  `commHopfAlgCatEquivCogrpCommAlgCat R`.
- `hopfPointsFunctor A : CommAlgCat.{u} R ⥤ GrpCat.{u}` sends an algebra `B` to the group of
  algebra maps `A → B`, with the convolution product. It is `opOp` followed by the Yoneda
  functor of the group object `hopfCogroup A`.
- `hopfCorepresentableBy A` says that `hopfPointsFunctor A` (as a functor to types) is
  corepresented by `A`. The bijection sends `f : A ⟶ B` to `f.op`; all fields hold by `rfl`.
- `hopfCogroupIso A` identifies the Library cogroup `Corepresented.cogroup` built from
  this corepresentation with `hopfCogroup A`. It is the preimage under the fully faithful
  Yoneda functor `yonedaGrpFullyFaithful` of the Library isomorphism
  `Corepresented.pointsIso`, composed with an isomorphism whose components are identities.
- `hopfGroupSchemeIso A` is the induced isomorphism of group schemes from
  `Corepresented.groupScheme (hopfPointsFunctor A) (hopfCorepresentableBy A)` to
  `(hopfSpec R).obj (op A)`. It is the image of `hopfCogroupIso A` under
  `(algSpec R).mapGrp`.
- `comulL_hopf A a` and `counitL_hopf A a`: the comultiplication
  `Corepresented.LinearEmbedding.comulL` and counit `Corepresented.LinearEmbedding.counitL`
  of this corepresentation are the comultiplication and counit of the Hopf algebra `A`.
  The counit statement holds by `rfl`. For the comultiplication, the Library map is the
  algebra comultiplication followed by the lift of the two tensor inclusions, which is the
  identity (`Algebra.TensorProduct.lift_includeLeft_includeRight`).

## The fixed-vector theorem

`exists_fixedVector_of_isUnipotent` takes a field `k : Type u`,
`A : CommHopfAlgCat.{u} (CommRingCat.of k)`, the hypothesis
`hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A))`, a finite nonempty index type
`n : Type` with decidable equality, and a matrix `a : Matrix n n A` with

- `hmul : ∀ i j, Coalgebra.comul (a i j) = ∑ l, a i l ⊗ₜ[k] a l j`;
- `hone : ∀ i j, Coalgebra.counit (a i j) = (1 : Matrix n n k) i j`.

It concludes `∃ v : n → k, v ≠ 0 ∧ ∀ i, ∑ j, v j • a i j = v i • (1 : A)`.

Proof. Unipotence passes to the corepresented group scheme along `hopfGroupSchemeIso A`
(Library `IsUnipotent.of_iso`). By `comulL_hopf` and `counitL_hopf`, `hmul` and `hone`
are the hypotheses of the Library's `Corepresented.LinearEmbedding.toGL`, which gives a
homomorphism of group functors to `GL_n`. The Library's `Corepresented.groupSchemeMap` turns
it into an actual representation, i.e. a homomorphism of group schemes to the general
linear group scheme. Unipotence gives a nonzero fixed vector `v` of this representation.
The Library's `isFixedVector_iff` turns fixedness into the coordinate equation for the
coefficient matrix of the representation, and `coefficientMatrix_toGL` shows that this
coefficient matrix is `a`.
