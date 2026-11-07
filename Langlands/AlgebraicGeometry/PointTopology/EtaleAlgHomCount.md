# Field-valued points of an étale algebra are uniformly bounded in number

Author: Worker 105.

Internal infrastructure for the proof of the quasi-compactness assertion of Conrad's
Corollary 5.7 (`HenselianIntegralPointsCompactStatement`). This standard fact of commutative
algebra is stated here in the form the proof needs. It is not taken from a specific statement
in the literature. All names are in the namespace
`Langlands.AlgebraicGeometry.PointTopology.EtaleAlgHomCount`.

## Statements

- `card_algHom_le_of_presentation (P : StandardEtalePresentation R S) (L)`: for a commutative
  ring `R`, an `R`-algebra `S` with a Mathlib standard étale presentation `P`, and a field `L`
  with an `R`-algebra structure, the type `S →ₐ[R] L` is finite. Its cardinality
  (`Nat.card`) is at most `P.f.natDegree`.
- `exists_card_algHom_le (A) [Algebra.Etale R A]`: for an étale `R`-algebra `A` there is
  `D : ℕ` such that for every field `L` (in any universe) with an `R`-algebra structure, the
  type `A →ₐ[R] L` is finite and has at most `D` elements.

## Proofs

`card_algHom_le_of_presentation`: an `R`-algebra map `φ : S → L` is determined by
`φ P.x` (`StandardEtalePresentation.hom_ext`). That value is a root in `L` of the image of
the monic polynomial `P.f` (`P.hasMap.1`). So `φ ↦ φ P.x` injects the maps into the
finite set of roots of `P.f.map (algebraMap R L)`, which has at most
`natDegree (P.f.map _) ≤ P.f.natDegree` elements (`Polynomial.card_roots'`).

`exists_card_algHom_le`: `EtaleBoundedCluster.exists_finset_isStandardEtale` (Library
module `AffineEtaleBoundedCluster`) gives a finite set `s ⊆ A` spanning the unit ideal with
every localization `A_f` (`f ∈ s`) standard étale. Choose a presentation `P f` of each and set
`D = ∑_{f ∈ s} (P f).f.natDegree`. Every `φ : A →ₐ[R] L` is nonzero on some `f ∈ s`, since
otherwise the unit ideal would lie in its kernel. Choosing such an `f`, `φ` extends to
`A_f` (`IsLocalization.liftAlgHom`). This gives a map
`(A →ₐ[R] L) → Σ f : s, (A_f →ₐ[R] L)` with a left inverse (composition with
`A → A_f`), hence an injection. By `Nat.card_sigma` and the first statement, the cardinality
is at most `D`.
