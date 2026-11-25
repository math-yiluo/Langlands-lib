# Statement: semisimple conjugation on a commutative unipotent normal subgroup

`Langlands.GroupScheme.SemisimpleUnipotentCentralizerStatement.{u} : Prop` encodes
Milne's Lemma 16.39. It does not prove the lemma. It is an input to the source proof
of Theorem 16.40 (the Library's
[`SolvableSemisimpleCentralizerStatement`](SolvableSemisimpleCentralizerStatement.md)).

## Lean statement

```lean
def SemisimpleUnipotentCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G N : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth N.X.hom] [ConnectedSpace N.X.left] [IsCommMonObj N.X]
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : (SubgroupFunctor.range n).IsNormal),
    IsUnipotent N →
    ∀ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (∀ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
        Module.End.IsSemisimple
          (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin m) (Fin m) k))) →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ N),
      ((G.pointCentralizer s).comap n).IsRepresentedBy c →
      letI : Mono n.hom.hom := hn.mono_overHom
      let d := (LinearKernelTower.normalConjugation n hN).commutatorMap s
      ConnectedSpace C.X.left ∧
        Surjective (((fst N.X C.X ≫ d) * (snd N.X C.X ≫ c.hom.hom)).left)
```

## Source and scope

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), registered as `milne-2017-algebraic-groups`,
`Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Page numbers are printed pages (PDF pages are printed pages plus 16). The 2022 corrected reprint
is registered as `milne-2022-algebraic-groups` (PDF pages are printed pages plus 11).

- Section 16e, p.338 in both editions: “Throughout, G is a connected group variety and k is
  algebraically closed.” In Lemma 16.39, `N` is a connected normal subgroup variety of `G`,
  `s ∈ G(k)` is semisimple, and `N` is commutative and unipotent. The lemma concludes that
  `C_N(s)` is connected and that `N × C_N(s) → N`, `(x, y) ↦ [s, x]·y`, is surjective.
  The lemma has the same hypotheses and conclusions in the 2022 reprint, p.338.
- The Chapter 16 opening, p.324 in both editions, specifies that algebraic groups are affine.
  The remark following 1.26 (2017 p.13, 2022 p.14) uses “group variety” for a smooth algebraic
  group. Thus `G` and `N` have smooth structure maps and are connected; `N` is affine because
  it is closed in `G`. The section's discussion of solvable groups does not add a solvability
  hypothesis to Lemma 16.39.
- For semisimplicity, use 9.19 (p.171 in both editions) and the convention on p.166 that a
  semisimple linear map is diagonalizable after a field extension. Over this algebraically
  closed field, for a finite-dimensional vector space this is equivalent to
  `Module.End.IsSemisimple`. Quantifying over `MatrixRepresentation G (Fin m)` tests all
  finite-dimensional representations by choosing bases, as in the all-representations
  criterion in 9.19.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02` and
`milne-2022-algebraic-groups-errata-2026-11-04` have no entry for Lemma 16.39 or pp.338–339.
The 2017 erratum on p.324 corrects “diagonalizable” to “trigonalizable” in the discussion of
condition (*); it does not affect the affine convention or the lemma.

## Actual subgroup and commutator map

- `GroupScheme S` is `Grp (Over S)`. The closed immersion `n : N ⟶ G` has a normal image
  on all tests, not just a normal subgroup of `G(k)`. The hypotheses on `N` include
  `IsCommMonObj N.X` and the Library's representation-theoretic `IsUnipotent N`
  ([`Reductive.Basic`](../Reductive/Basic.md)): every nonzero finite-dimensional
  representation has a nonzero fixed vector, as in §14b (p.280 in both editions).
- [`pointCentralizer`](../PointCentralizer.md) is the all-test centralizer of the section `s`.
  Its comap along `n` consists of points of `N` whose images commute with the pullback of
  `s` to the test scheme. `IsRepresentedBy c` identifies the range of the monomorphism
  `c` with that subgroup functor. This is a supplied representative of `C_N(s)`; the
  statement concerns every such representative and does not assert its existence anew.
- `hn.mono_overHom` ([`ClosedSubgroupMonomorphism`](../ClosedSubgroupMonomorphism.md))
  supplies the monomorphism needed by the published action
  [`LinearKernelTower.normalConjugation`](TriangularCharacterKernelDescent.md). The published
  [`AutomorphicAction.commutatorMap`](../Reductive/RelativeRootCommutatorMap.md) fixes the
  section `s` in this action. On all tests, `d(x)` has image `s n(x) s⁻¹ n(x)⁻¹` under `n`,
  with `s` pulled back to the test. The multiplication of morphisms in the statement makes
  `N × C → N` the map `(x, y) ↦ d(x)c(y)`.
- The conclusions are `ConnectedSpace C.X.left` and surjectivity of the underlying scheme
  morphism. The statement does not assert that this morphism is an isomorphism or that it
  is surjective on points over every test scheme.

Milne's proof (2017 p.338; 2022 pp.338–339) takes the group-scheme image `M` of `d`, a
homomorphism since `N` is commutative. Uniqueness of the Jordan decomposition makes
`(M ∩ C)(k)` trivial: an element `[s, x]` commuting with `s` would otherwise contribute a
nontrivial unipotent part to a conjugate of `s`. Thus multiplication `M × C → N` has a
finite connected kernel. The formula `dim M + dim C = dim N` for `d` shows that the
multiplication image has full dimension in the irreducible group `N`, so it is all of `N`.
Connectedness of the kernel and quotient makes `M × C` connected, hence `C` is connected.
Composing the surjection `N × C → M × C` with multiplication gives the displayed map.
This argument uses only triviality on rational points of the intersection, not triviality
of the scheme-theoretic intersection.
