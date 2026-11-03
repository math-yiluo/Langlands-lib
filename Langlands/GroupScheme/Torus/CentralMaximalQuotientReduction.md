# The quotient by a central maximal torus contains no torus, from extensions and images of tori

Worker 1395 wrote this module. It reduces
[`CentralMaximalTorusQuotientStatement`](CentralMaximalQuotientStatement.md)
(Worker 1379; the "only if" direction of Milne's Lemma 16.43 as used in the
proof of Theorem 17.82) to two premises:

- [`CentralTorusExtensionStatement`](CentralExtensionStatement.md): a
  central extension of a torus by a torus is a torus (Milne 12.41, 12.22);
- [`TorusImageClosedTorusStatement`](ImageStatement.md): a homomorphism
  from a torus to a smooth affine group factors through a closed torus
  (Milne 5.39 and §12.e).

Both premises stay hypotheses.

## Statements (namespace `Langlands.GroupScheme`)

- `CentralMaximalTorusQuotientReductionStatement.{u}` is the proposition
  `CentralTorusExtensionStatement.{u} → TorusImageClosedTorusStatement.{u} →
  CentralMaximalTorusQuotientStatement.{u}`.
- `centralMaximalTorusQuotientReduction :
  CentralMaximalTorusQuotientReductionStatement.{u}` proves it.

The reduction statement is an internal assembly, not a numbered result of
Milne. It records the derivation given in the source section of
`CentralMaximalTorusQuotientStatement`, with the inverse image of the torus
formed as a fibre product, and with centrality of `Z` in that fibre product
used in place of the identity component.

## Proof

Let `k`, a smooth affine `H`, a commutative `Z` with `j : Z.toGrp ⟶ H`,
`IsCentral j` and `IsMaximalTorus j`, an fppf quotient `q : H ⟶ Q` with
kernel `range j`, a torus `T` and `g : T.toGrp ⟶ Q` be given.

1. `j ≫ q = 0`. The identity of `Z.X`, as a point of `Z` over the test
   scheme `Z.X`, maps to the point `j.hom.hom` of `range j`, which is the
   range of `kernelι q`. By `mem_range_kernelι_iff`
   (module `CentralIsogeny.Basic`), `j.hom.hom ≫ q.hom.hom = 1`; since
   `Grp.forget` is faithful, `j ≫ q = 0`.
2. The fibre product. `E = pullback g q` in `Grp (Over (Spec k))`, with
   projections `p : E ⟶ T.toGrp` and `e : E ⟶ H`. Mathlib's
   `Grp.forget` creates limits, and `Over.forget` preserves pullbacks, so
   the square `p, e, g, q` is a pullback square of objects over `Spec k`
   and of schemes.
3. The lift `zE = pullback.lift 0 j : Z.toGrp ⟶ E`, defined by step 1, with
   `zE ≫ p = 0` and `zE ≫ e = j`.
   - `zE` is central. For points `y = a ≫ x` of `Z` and `h` of `E`, the
     two products `(y ≫ zE) * h` and `h * (y ≫ zE)` agree after `p`
     (where `y ≫ zE` becomes `1`) and after `e` (where `y ≫ j` commutes
     with `h ≫ e` since `j` is central). Pullback morphisms are equal when
     both projections agree.
   - `zE` is a closed subgroup. `T` is separated over `Spec k`
     (`fieldSeparated`, module `FieldSeparatedProof`), so `g` is
     separated, and so is its base change `e`. Since `zE ≫ e = j` is a
     closed immersion and `e` is separated, `zE` is a closed immersion
     (`IsClosedImmersion.of_comp`).
   - `p` is an fppf quotient with kernel `range zE`. Flatness, surjectivity
     and local finite presentation of `p` come from those of `q` by base
     change. A point `x` of `E` with `x ≫ p = 1` has `x ≫ e ≫ q = x ≫ p ≫ g
     = 1`, so `x ≫ e` lies in `range (kernelι q) = range j`, say
     `x ≫ e = y ≫ j`; then `x = y ≫ zE`, comparing both projections.
     Conversely `y ≫ zE ≫ p = 1`.
   - `p` is affine. `Q` is separated over `Spec k` (`fieldSeparated`) and
     `q` followed by the structure morphism of `Q` is the structure
     morphism of `H`, which is affine. So `q` is affine
     (`IsAffineHom.of_comp`), and so is its base change `p`.
4. `CentralTorusExtensionStatement` applied to `zE` and `p` gives
   `IsTorus E`.
5. `TorusImageClosedTorusStatement` applied to `e : E ⟶ H` gives a closed
   torus `j' : Z'.toGrp ⟶ H` and `f : E ⟶ Z'.toGrp` with `f ≫ j' = e`.
   Then `(zE ≫ f) ≫ j' = zE ≫ e = j`, so maximality of `j` makes
   `zE ≫ f` an isomorphism and `j' = inv (zE ≫ f) ≫ j`.
6. Hence `p ≫ g = e ≫ q = f ≫ inv (zE ≫ f) ≫ j ≫ q = 0` by step 1. The
   scheme morphism underlying `p` is flat and surjective, hence an
   epimorphism (`Flat.epi_of_flat_of_surjective`), so the morphism
   underlying `g` is the identity point `1`. Every point of `T` then maps
   to `1` under `g`, which is `SubgroupFunctor.range g = ⊥`.

The proof adds no hypothesis on `k`, `H`, `Q` or `T`, and uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
