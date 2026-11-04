# Finite root index implies semisimplicity, given self-centralizing maximal tori

Worker 1391. This module proves the "if" half of Milne Proposition 21.48 for
the Library's actual-scheme conventions, under one explicit hypothesis: the
published proposition `MaximalTorusCentralizerStatement` (module
`Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement`, Milne
Corollary 17.84), which says that a maximal torus of a connected reductive
group is its own centralizer. The Library has no proof of that proposition, so
this module proves neither `SplitSemisimpleOfFiniteRootIndexStatement` nor
`SplitSemisimpleRootDatumStatement` outright. It proves that each follows from
`MaximalTorusCentralizerStatement`.

## Main results

- `splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer`:
  `MaximalTorusCentralizerStatement.{u} → SplitSemisimpleOfFiniteRootIndexStatement.{u}`.
  The target proposition is in module
  `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity`. It
  says: if `G` is connected reductive over a field `k`, `i : T ⟶ G` is a
  maximal torus with `T` split, `P` is a root datum with `IsRootDatumOf i P`,
  and `characterLattice T ⧸ P.rootSpan ℤ` is finite, then `IsSemisimple G`.
  This result is a `def` whose type is a proposition (the `defProp` linter is
  switched off for it), so that the module has a definition as its
  declaration. Mathematically it is a theorem.
- `splitSemisimpleRootDatum_of_maximalTorusCentralizer`:
  `MaximalTorusCentralizerStatement.{u} → SplitSemisimpleRootDatumStatement.{u}`.
  It composes the previous result with
  `splitSemisimpleRootDatum_of_finiteRootIndex` from the same necessity
  module. That theorem also uses the proved "only if" half
  `IsSemisimple.finite_quotient_rootSpan`. The target is the published
  split semisimplicity criterion in module
  `Langlands.GroupScheme.Reductive.SplitClassificationStatement`, in both its
  root and coroot forms.

All results use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The universe `u` is arbitrary. Nothing restricts the field:
imperfect fields and positive characteristic are allowed. The centre is the
Library's full scheme-theoretic centre, nilpotents included.

## Auxiliary lemmas

- `eq_zero_of_tmul_eq_zero`: over a field `k`, if `v ≠ 0` in a `k`-vector
  space `V` and `b ⊗ v = 0` in `B ⊗[k] V` for a `k`-algebra `B`, then
  `b = 0`. Proof: choose a linear form `f` with `f v ≠ 0`
  (`Module.Projective.exists_dual_ne_zero`), apply `B ⊗ f` followed by
  `B ⊗ k ≅ B`, and obtain `f v • b = 0`.
- `characterValue_root_eq_one_of_isCentral`: let `G` be an affine group of
  locally finite type over the field `k`, `T` a commutative group scheme,
  `i : T ⟶ G`, and `w : Z ⟶ T` a homomorphism with `w ≫ i` central
  (`IsCentral`). Then for every root `α ∈ roots i`, every `k`-algebra `B` and
  every `B`-point `s` of `Z`, the value `Lie.characterValue α (s ≫ w) ∈ Bˣ`
  is `1`. Proof:
  1. Since `α` is a root, its weight space is nonzero; choose `X ≠ 0` in it.
     By `mem_weightSpace`, `Ad(s ≫ w ≫ i)` acts on the scalar extension
     `X_B` of `X` (`lieKernelMapLinear`) as multiplication by
     `characterValue α (s ≫ w)`.
  2. `IsCentral.adjoint_eq` (module
     `Langlands.GroupScheme.Rational.CentralRootRestriction`) says that
     `Ad(s ≫ w ≫ i)` fixes `X_B`.
  3. Hence `(characterValue α (s ≫ w) - 1) • X_B = 0`. The Library
     isomorphism `Lie.kernelScalarExtension : B ⊗[k] Lie(G) ≃ Lie(G_B)`
     (module `Langlands.GroupScheme.Lie.ScalarExtension`; it needs
     `LocallyOfFiniteType`) sends `b ⊗ X` to `b • X_B`. So
     `(characterValue α (s ≫ w) - 1) ⊗ X = 0`, and
     `eq_zero_of_tmul_eq_zero` gives the claim.
- `pointCharacters_algSpec_eq_one`: on the spectrum of a `k`-algebra, a
  character value equal to `1` gives a point character
  (`characterLattice.pointCharacters`, module
  `Langlands.GroupScheme.Torus.KernelDiagonalizable`) equal to `1`. Both are
  the unit attached to the same point of `𝔾_m`; they differ by the
  isomorphism `Γ(Spec A) ≅ A` (`Gm.affinePointsEquiv_val`,
  `Scheme.ΓSpecIso`).
- `pointCharacters_root_eq_one_of_isCentral`: in the same situation, for
  every affine test scheme `U` and every point `x : U ⟶ Z`, the point
  character of `x ≫ w` is `1` at every root. Proof: `U` is isomorphic to
  `Spec A` for some `k`-algebra `A` (Mathlib's `essImage_algSpec`). Apply the
  two previous lemmas to `e.hom ≫ x`, then transport back along `e.inv` by
  `characterLattice.pointCharacters_naturality`.

## Proof of the main result

Fix `k`, `G`, `T`, `i`, `P` as above with `X ⧸ ℤΦ` finite, where
`X = characterLattice T` and `ℤΦ = P.rootSpan ℤ`. Connected reductivity is
part of `IsSemisimple`, so only a finite scheme-theoretic centre is needed.

1. **The centre.** The Library theorem `schemeTheoreticCenterExistence`
   (module `Langlands.GroupScheme.Reductive.CenterExistenceProof`) gives a
   closed immersion `z : Z ⟶ G` representing the centre of `G`.
2. **The centre lies in `T`.** The hypothesis gives
   `torusCentralizer i = range i`. A central point commutes with all points
   of `T`, so `range z = center G ≤ torusCentralizer i = range i`. Since `i`
   is a closed immersion, `range i` is represented by `i`, and
   `SubgroupFunctor.IsRepresentedBy.liftOfLE` gives `w : Z ⟶ T` with
   `w ≫ i = z`. In particular `w ≫ i` is central.
3. **Roots kill the centre.** `Z` is affine over `k`, because `z` is a closed
   immersion into the affine `G`. Let `φ` be the point character of the
   universal point `w` of `T` over `Z`. It is a homomorphism
   `X → Γ(Z)ˣ`. By `pointCharacters_root_eq_one_of_isCentral` (with
   `U = Z` and `x = 𝟙`), `φ` is trivial on every root. So `φ` vanishes on
   `ℤΦ` and descends to `ψ : X ⧸ ℤΦ → Γ(Z)ˣ`.
4. **A map to `D(X/ℤΦ)`.** Let `D` be the diagonalizable group scheme
   `Diagonalizable.groupScheme k (X ⧸ ℤΦ)`, the spectrum of the group algebra
   `k[X ⧸ ℤΦ]`. By `Diagonalizable.characterPointsEquiv`, `ψ` is a point
   `g : Z ⟶ D`. The quotient map `X → X ⧸ ℤΦ` composed with the universal
   point of `D` is a character of `X` over `D`. Since `T` is split,
   `characterLattice.pointCharactersEquiv` turns it into a morphism
   `incl : D ⟶ T`. Both naturality lemmas show that `g ≫ incl` and `w` have
   the same point character, so `g ≫ incl = w`. Hence
   `g ≫ incl ≫ i = z` on underlying schemes.
5. **`Z` is finite.** The composite `z` is a closed immersion, and
   `incl ≫ i` is separated: its composite with the structure morphism of `G`
   is the structure morphism of the affine `D`. So `g` is a closed immersion
   (`IsClosedImmersion.of_comp`), in particular finite. The group algebra
   `k[X ⧸ ℤΦ]` is finite-dimensional because `X ⧸ ℤΦ` is finite
   (`AddMonoidAlgebra.coeffLinearEquiv`), so `D` is finite over `k`
   (`IsFinite.SpecMap_iff`). The structure morphism of `Z` is `g` followed
   by that of `D`, so it is finite. This is the finite centre of
   `IsSemisimple G`.

The proof shows that the centre is a closed subgroup of `D(X/ℤΦ)`. It does not
need the reverse inclusion of Milne's Proposition 21.8.

## Provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Proposition 21.48 (printed p.439, PDF p.455): "A split reductive group is
  semisimple if and only if its root datum is semisimple." Milne's proof: "A
  reductive group is semisimple if and only if its centre is finite (19.10),
  and so this follows from Proposition 21.8." The preceding line recalls
  (C.34) that "a root datum (X, Φ, Φ^∨) is semisimple if ZΦ is of finite
  index in X".
- Proposition 21.7 (printed p.427, PDF p.443): the centre of a reductive group
  is contained in a maximal torus `T` and equals the kernel of `Ad` on `T`.
  Its proof begins: "As Z(G) centralizes T, it is contained in C_G(T) = T."
- Proposition 21.8 (printed p.427, PDF p.443): "Z(G) is the diagonalizable
  subgroup of T with character group X^*(T)/ZΦ." Its proof uses that `T`
  acts on `g` through the roots, so that `Z(G)` is the intersection of the
  root kernels.
- Corollary 17.84 (printed p.379, PDF p.395): "A torus T in a reductive group
  G is maximal if and only if C_G(T) = T." Its "only if" direction is the
  Library's `MaximalTorusCentralizerStatement`, the hypothesis here.

The Library's `IsSemisimple` is connected reductive with finite centre, the
criterion Milne quotes from 19.10. The Lean proof follows Milne's outline for
the inclusion of the centre in the intersection of the root kernels: the
centre lies in `C_G(T) = T` (17.84, as in the proof of 21.7), and every root
is trivial on central points because a central point acts trivially through
`Ad` on a root space (as in the proofs of 21.7 and 21.8). The Lean proof does
not use the reverse inclusion of 21.8 or the unipotence argument of 21.7. The
final step, the closed immersion `Z ⟶ D(X/ZΦ)` and the finiteness of
`k[X/ZΦ]`, is Worker 1391's.
