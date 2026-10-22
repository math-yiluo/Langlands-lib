# Finite etale torsion of abelian schemes

Author: Worker 140.

`Langlands.AbelianScheme.TorsionFiniteEtaleStatement` is a proposition target.
For every scheme `S`, every published `Langlands.AbelianScheme S`, and every
natural number `n > 0` whose image in the global sections ring `Γ(S, ⊤)` is a
unit, it asserts that the structure morphism of `A[n]` to `S` is both finite
and etale, using Mathlib's `IsFinite` and `Etale` predicates.

Here `A[n]` is exactly the imported
`Langlands.GroupScheme.torsion A.toGrp (n : ℤ)`. It is the group-scheme kernel
of actual integer multiplication, constructed as the pullback with the unit
section. The conclusion concerns its structure map `.X.hom`, rather than its
inclusion into `A` or the multiplication map on `A`. No new torsion object or
geometric property is included as data. The abelian-scheme bundle supplies
smoothness, properness, geometrically connected fibres, and explicit
commutativity; its source-definition equivalence remains a separate obligation.

## Source and scope

The original source is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article in the author's corrected version dated
January 2, 2022. It is registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Printed page numbers equal the one-based PDF page numbers in this copy.
The cited pages were read directly.

- Section 20, opening definition, p.42, defines an abelian scheme over an
  arbitrary scheme by smoothness, properness and connected geometric fibres.
  Corollary 20.2(c), p.43, asserts commutativity. These agree with the explicit
  conditions in the imported bundle; this statement does not prove commutativity.
- Proposition 20.7 and its proof, p.44, give finite flat multiplication and its
  finite flat kernel, with etaleness when the integer is prime to every residue
  characteristic. The forward etaleness implication is the one used here.
- The proof invokes Theorem 8.2, p.13, whose integer hypothesis is explicitly
  `n > 0`. That hypothesis is retained, despite its omission in the sentence
  stating Proposition 20.7. The torsion construction itself remains defined
  for every integer; this theorem target is restricted to positive indices.

The provenance is **derived** because Proposition 20.7 is phrased for a fixed
relative dimension `g`, while this target makes no globally constant dimension
assumption and omits the order formula. Its finite and etale conclusions apply
locally on the base where the relative dimension is constant and descend by
locality on the target. Alternatively, its proof obtains finiteness from
properness and finite fibres and obtains etaleness from the corresponding
fibrewise multiplication result; neither argument needs a uniform fibre
dimension. This explains the mathematical scope, not a Lean proof provided here.

The hypothesis `IsUnit (n : Γ(S, ⊤))` expresses invertibility on the whole base,
including a nonaffine base. A global section is invertible precisely when all
its germs are units; in a local ring this is equivalent to its image in the
residue field being nonzero. Applied to the integer section, this is the
prime-to-residue-characteristics hypothesis of Proposition 20.7. This
interpretation does not add a further equivalence theorem to the Lean module.

There is no field, affineness, noetherian, connectedness, or constant-dimension
assumption on `S`. The target asserts neither an etaleness converse nor a rank
formula. In particular, it makes no finiteness claim for zero multiplication.

## Formal status

The declaration is a `Prop`-valued `def`, not a theorem, an axiom, or an added
field of the abelian-scheme or torsion definitions. A proof of this exact
statement is a separate obligation after independent acceptance and publication.
