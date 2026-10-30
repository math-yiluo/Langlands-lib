# Proof of the source presentation of abelian group schemes over fields

This module proves the published statement
`Langlands.GroupScheme.FieldAbelianVarietyPresentationStatement` from
`Langlands.AbelianScheme.FieldAbelianVarietyPresentationStatement`. The
statement module is imported unchanged.

For every universe `u`, every field `K : Type u`, every group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, the
statement says that

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  LocallyOfFiniteType G.X.hom ∧
  QuasiCompact G.X.hom ∧
  IsSeparated G.X.hom ∧
  Nonempty G.X.left ∧
  GeometricallyIntegral G.X.hom.
```

## Declarations

- `Langlands.GroupScheme.fieldAbelianVarietyPresentation_of_smoothGeometricIntegrality`
  derives the statement from an explicit argument of type
  `Langlands.AbelianScheme.SmoothGeometricIntegrality.{u}`. It is an
  intermediate step only.
- `Langlands.GroupScheme.fieldAbelianVarietyPresentation` has exactly the type
  `FieldAbelianVarietyPresentationStatement.{u}`. It applies the step above to
  the published proof of `SmoothGeometricIntegrality`, so it has no extra
  hypotheses.

## Implemented proof

Fix `K`, `G`, the commutativity instance and the three hypotheses. Each clause
is proved directly.

1. **Local finite type.** Mathlib's `IsProper` extends `LocallyOfFiniteType`,
   so instance search gives `LocallyOfFiniteType G.X.hom` from the properness
   hypothesis.
2. **Quasi-compactness.** `IsProper` also extends `UniversallyClosed`, and
   Mathlib's instance `UniversallyClosed f → QuasiCompact f` gives
   `QuasiCompact G.X.hom`.
3. **Separatedness.** `IsProper` extends `IsSeparated`, so instance search
   gives `IsSeparated G.X.hom`.
4. **Nonemptiness.** The spectrum of a field is nonempty: Mathlib has an
   instance for it, since a field is a nontrivial ring. The group unit
   `η[G.X] : 𝟙_ _ ⟶ G.X` is a morphism in the over category. The monoidal unit
   there is `Spec K` over itself, so its underlying scheme morphism
   `η[G.X].left` goes from `Spec K` to `G.X.left`. Applying it to a point of
   `Spec K` gives a point of `G.X.left`.
5. **Geometric integrality.** `SmoothGeometricIntegrality` says that every
   smooth, geometrically connected morphism `p : X ⟶ Spec K` is geometrically
   integral. It is applied with `X = G.X.left`, `p = G.X.hom`, and the
   smoothness and geometric-connectedness hypotheses.

The proof does not use the commutativity instance. It also uses neither the
group multiplication nor the inverse. Smoothness is used only in clause 5,
and properness only in clauses 1–3.

## Dependencies and scope

The only non-Mathlib inputs are the target statement module and the published
proof of `Langlands.AbelianScheme.SmoothGeometricIntegrality`. That proof was
supplied by its own proof task. Its theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality` is imported by Lean name
from module `Langlands.AbelianScheme.SmoothGeometricIntegralityProof`. This
module does not reprove it, and it uses no statement or draft as a proof.
No ample line bundle, projective embedding, twisting sheaf or ample-existence
result is used. The universe, field, characteristic and dimension stay
arbitrary, and imperfect fields and dimension zero are included.

The source correspondence with J. S. Milne, *Abelian Varieties* (1986, author
revision 2022), pp.2–3 and Section 20, p.42, is explained in the statement
companion `FieldAbelianVarietyPresentationStatement.md`. The Lean proof follows
the route given there: properness consequences, the actual unit section, and
geometric integrality.
