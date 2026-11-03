# Central maximal tori under field extension: reduction to quotients and absence of tori

Worker 1379.

## Statements

`IsCentral.range_isNormal` proves, over any base scheme, that the range
`SubgroupFunctor.range i` of a central homomorphism `i : H ⟶ G` of group
schemes is normal (`IsNormal`): conjugating a point `i ∘ y` by any point
`g` of `G` gives `i ∘ y` back.

`CentralMaximalTorusBaseChangeReductionStatement.{u}` says that three
statements at universe `u` together imply
`CentralMaximalTorusBaseChangeStatement.{u}`, the forward implication of
Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Theorem 17.82, printed p.379 (one-based PDF p.395), for a central torus:

- `NormalSubgroupQuotientStatement.{u}`: a normal closed subgroup of a
  smooth affine group over a field is the kernel of an fppf quotient map
  onto a smooth affine group (Milne 5.14, 5.18, 5.26).
- `CentralMaximalTorusQuotientStatement.{u}`: if `j : Z ⟶ H` is a central
  maximal torus and `q : H ⟶ Q` an fppf quotient with kernel `Z`, every
  homomorphism from a torus over `k` to `Q` is trivial (Milne 16.43, as
  used in the proof of 17.82).
- `NoTorusBaseChangeStatement.{u}`: if every homomorphism from a torus over
  `k` to a smooth affine `Q` is trivial, the same holds for tori over `K`
  and `Q_K` (Milne 17.81, 14.9, 14.18).

None of the three is proved here; they remain explicit hypotheses. The
reduction statement is an internal assembly of them. It follows the
proof of Milne 17.82: `T` is maximal in `C = C_G(T)` iff `C/T` contains no
nontrivial torus, and that property is invariant under field extension.

## Proof

`centralMaximalTorusBaseChangeReduction` proves the reduction statement.
Let `K/k`, `H` smooth affine over `k`, and `j : Z ⟶ H` central with
`IsMaximalTorus j` be given, and write `b` for `Spec K ⟶ Spec k`.

1. `j` is a closed subgroup (part of `IsMaximalTorus`) with normal range
   (`IsCentral.range_isNormal`), so the quotient premise gives a smooth
   affine `Q` and `q : H ⟶ Q` with `IsFppfQuotient (range j) q`.
2. The premise `CentralMaximalTorusQuotientStatement` makes every
   homomorphism from a torus over `k` to `Q` trivial, and
   `NoTorusBaseChangeStatement` transfers this to tori over `K` and `Q_K`.
3. The base change `Z_K` is a torus (`IsTorus.baseChange`) and `j_K` is a
   closed subgroup (`IsClosedSubgroup.baseChange`). It remains to show
   maximality. Let `i' : T' ⟶ H_K` be a closed torus and `f : Z_K ⟶ T'`
   with `f ≫ i' = j_K`.
4. The range of `i'` lies in the range of `j_K`. For a point `i' ∘ y`, the
   composite `i' ≫ q_K` is a homomorphism from a torus over `K` to `Q_K`,
   so it is trivial by step 2, and `i' ∘ y` maps to the identity of
   `Q_K`. By `range_baseChangeHom` and `mem_baseChange`, membership in the
   range of `j_K` means that the corresponding point of `H` (under
   `baseChangePointsEquiv`) lies in the range of `j`. That range is the
   kernel of `q` (the kernel clause of `IsFppfQuotient` with
   `mem_range_kernelι_iff`), and the corresponding point lies in it because
   `baseChangePointsEquiv_comp` identifies its image under `q` with the
   point of `Q` corresponding to the identity of `Q_K`. Only the kernel
   clause of `IsFppfQuotient` is used; no base change of the quotient map is
   needed.
5. Since `j_K` represents its range (it is a closed immersion, hence a
   monomorphism), `factorHom` factors `i'` as `g ≫ j_K` with
   `g : T' ⟶ Z_K`. Both `f ≫ g` and `g ≫ f` are identities, checked after
   composing with the monomorphisms `j_K` and `i'` respectively
   (`IsRepresentedBy.hom_ext`): `f ≫ g ≫ j_K = f ≫ i' = j_K` and
   `g ≫ f ≫ i' = g ≫ j_K = i'`. Hence `f` is an isomorphism, and `j_K` is
   maximal.
