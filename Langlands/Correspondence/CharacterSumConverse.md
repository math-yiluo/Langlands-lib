# Unramified parameters with a given Euler polynomial are character sums

This is an internal helper module. It proves the converse of
`Langlands/Correspondence/CharacterSumEuler.lean`: an unramified
Frobenius-semisimple parameter class is determined by the Weil–Deligne Euler
polynomial of the geometric Frobenius lift. It defines
`unramifiedCharacterSumClass F c`, the character-sum class of the unramified
characters `w ↦ c_i ^ deg(w)`. If the Euler polynomial of an unramified class is
`∏_i (1 - c_i X)`, the class is `unramifiedCharacterSumClass F c`. For a
geometric candidate and unramified quasi-characters, this gives an
Euler-polynomial characterization of `IsCharacterSumParameter`. The last section
restates these results with the standard Euler polynomial
`parameterEulerPolynomial F D` of `Langlands/Correspondence/UnramifiedEuler.lean`.
In that form no unramifiedness hypothesis is needed, because the degree of the
polynomial detects it. Everything is derived from existing Library interfaces,
the helper modules `UnramifiedReciprocityBridge`, `CharacterSumEuler` and
`UnramifiedEuler`, and Mathlib linear algebra, so the module makes no new
literature claim. It proves neither `FullCorrespondenceUnramifiedStatement` nor
any automorphic statement.

Notation: as in `CharacterSumEuler.md`, `eulerPolynomial f = det(1 - X f)` is
`Langlands.LocalFactor.eulerPolynomial`.
`LocalFactor.WeilDeligne.eulerPolynomial A I g` is the Euler polynomial of `g`
on the `I`-fixed part of the monodromy kernel of `A`. `deg(w)` is the integer
degree `Weil.Local.localDegreeInt F w`, that is, `toAdd` of the multiplicative
degree `Weil.Local.localDegree F w : Multiplicative ℤ`. Inertia
`Weil.Local.localInertia F` consists of the elements of integer degree `0`
(multiplicative degree equal to the identity `1 = ofAdd 0`). `Φ` denotes
`Weil.Local.localGeometricFrobenius F`, of integer degree `1` (multiplicative
degree `ofAdd 1`), and `ϖ` denotes `F.canonicalTopologicalData.uniformizerUnit`.

## Linear algebra (`Langlands.LocalFactor`)

- `eulerPolynomial_eq_prod_of_apply_basis`: let `b` be a finite basis of a
  free finite module over a commutative ring. If `f (b i) = c i • b i` for all
  `i`, then `eulerPolynomial f = ∏ i, (1 - C (c i) * X)`. The proof checks
  that the coordinate functional `b.coord i` composed with `f` is
  `c i • b.coord i` on the basis. It then applies
  `eulerPolynomial_eq_prod_of_repr` from `CharacterSumEuler`.
- `roots_prod_one_sub_C_mul_X`: over a field, if every `a i` is nonzero, the
  root multiset of `∏ i, (1 - C (a i) * X)` is the multiset of the `(a i)⁻¹`.
  Each factor equals `C (-a i) * (X - C (a i)⁻¹)`. No factor vanishes, since
  each has value `1` at `0`. Mathlib's `roots_prod`, `roots_C_mul` and
  `roots_X_sub_C` then give the multiset.
- `exists_equiv_of_map_univ_eq`: if two families `f : α → γ` and `g : β → γ`
  on finite types have the same multiset of values, some bijection
  `e : α ≃ β` satisfies `g (e a) = f a`. Counting each value `c` in the two
  multisets shows that the fibres `{a // f a = c}` and `{b // g b = c}` have
  equal cardinality. `Equiv.ofFiberEquiv` glues bijections between the fibres,
  chosen by `Fintype.equivOfCardEq`.
- `exists_basis_apply_eq_smul_of_isSemisimple`: over an algebraically closed
  field, a semisimple endomorphism `f` of a finite-dimensional space has a
  basis `b` indexed by `Fin (finrank K V)` and eigenvalues `μ` with
  `f (b j) = μ j • b j`. By Mathlib's `eigenspaces_iSupIndep` and
  `IsSemisimple.iSup_eigenspace_eq_top`, the eigenspaces form an internal
  direct sum. Its `collectedBasis` consists of eigenvectors and is reindexed
  to `Fin (finrank K V)`.
- `natDegree_prod_one_sub_C_mul_X`: over a field, if every `c i` is nonzero,
  `∏ i, (1 - C (c i) * X)` has `natDegree` equal to the number of factors.
  Each factor is the linear polynomial `C (-c i) * X + C 1` of degree `1`
  (`natDegree_linear`), so no factor is zero, and `natDegree_prod` sums the
  degrees.

## Unramified parameters (`Langlands.Correspondence`)

- `localUnramifiedCharacter_eq_one_of_mem_localInertia`: the unramified
  character `Weil.Local.localUnramifiedCharacter F z` is trivial on
  `Weil.Local.localInertia F`. This restates the published
  `Weil.Local.localUnramifiedCharacter_on_inertia` for elements with a
  membership proof.
- `representation_apply_of_isUnramified`: let `A` be a local Weil–Deligne pair
  on which inertia acts trivially. Let `v` satisfy
  `A.representation Φ v = z • v`. Then every Weil element `w` acts on `v` by
  `localUnramifiedCharacter F z w = z ^ deg(w)`. The proof first gets
  `Φ⁻¹ v = z⁻¹ • v`, then `Φ ^ k v = z ^ k • v` for every integer `k` by
  induction. With `k = deg(w)`, the element `w * Φ ^ (-k)` has integer degree
  `k - k = 0`, so it lies in inertia and acts trivially. In Lean this is the
  equation `localDegree F (w * Φ ^ (-k)) = 1` in `Multiplicative ℤ`, whose
  identity `1` is `ofAdd 0`. Finally `w = (w * Φ ^ (-k)) * Φ ^ k`.
- `nonempty_equiv_characterSumPair`: let `A` have zero monodromy and trivial
  inertia action, and let `b : Basis (Fin n) ℂ A` satisfy
  `A.representation Φ (b i) = c i • b i`. Then `A` is equivalent to
  `characterSumPair F (fun i => localUnramifiedCharacter F (c i))`. The
  character sum has the standard basis `b₀` of `CharacterSumEuler` (via
  `Module.Basis.ofRepr`), in which every `g` acts on `b₀ i` by the scalar
  `ψ i g`. The linear equivalence `b₀.equiv b` sends `b₀ i` to `b i`. On each
  `b i`, `A` acts by the same scalar by `representation_apply_of_isUnramified`,
  so the map intertwines the actions. Both monodromies are zero.
- `characterSumClass_congr`: `characterSumClass ψ hψ` depends only on `ψ`, not
  on the inertia-triviality proof `hψ`.
- `unramifiedCharacterSumClass F c` (definition): for `c : Fin (r + 1) → ℂˣ`,
  the class in `WeilDeligneClass.{uF, uP} F r.succPNat` given by
  `characterSumClass (fun i => localUnramifiedCharacter F (c i)) _`, the
  direct sum of the zero-monodromy lines on which `w` acts by `c i ^ deg(w)`.
  The inertia-triviality argument is
  `localUnramifiedCharacter_eq_one_of_mem_localInertia`. It is the unramified
  class whose geometric Frobenius lift has eigenvalues `c i`.
- `eq_unramifiedCharacterSumClass_of_eulerPolynomial`: let
  `D : WeilDeligneClass.{uF, uP} F r.succPNat` satisfy
  `IsUnramifiedParameterClass F D`, and let `c : Fin (r + 1) → ℂˣ`. Suppose
  some pair `A` with `classOf A = parameterForget F D` satisfies
  `LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F) Φ =
  ∏ i, (1 - C (c i) * X)`. Then `D = unramifiedCharacterSumClass F c`.
  The proof works with a representative `a` of `D`. From the witness of
  `IsUnramifiedParameterClass`, `a` has zero monodromy and trivial inertia
  action. It is Frobenius-semisimple, and `Φ` has nonzero degree, so
  `a.representation Φ` is semisimple. Over `ℂ` this gives an eigenbasis with
  eigenvalues `μ j`. By `eulerPolynomial_eq_of_monodromy_eq_zero` and
  `eulerPolynomial_eq_of_equiv` from `CharacterSumEuler`,
  `eulerPolynomial (a.representation Φ)` is `∏ i, (1 - C (c i) * X)`. By the
  eigenbasis lemma it is also `∏ j, (1 - C (μ j) * X)`. Each `μ j` is nonzero,
  since `Φ` acts invertibly. Comparing root multisets gives
  `{(μ j)⁻¹} = {(c i)⁻¹}`, and `exists_equiv_of_map_univ_eq` reindexes the
  eigenbasis so that its `i`-th vector has eigenvalue `c i`.
  `nonempty_equiv_characterSumPair`, `parameterForget_characterSumClass` and
  `parameterForget_injective` (from `ZeroMonodromyExtension`) finish the
  proof.
- `isCharacterSumParameter_iff_eulerPolynomial`: let `e` be a geometric
  candidate (`IsGeometricReciprocity F e`) and every `χ i` unramified. For
  every `D` and every pair `A` with `classOf A = parameterForget F D`,
  `IsCharacterSumParameter F e χ D` holds exactly when `D` is unramified and
  `LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F) Φ =
  ∏ i, (1 - C (χ i ϖ) * X)`. The forward direction is
  `isUnramifiedParameterClass_of_isCharacterSumParameter_of_isGeometricReciprocity`
  together with
  `eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity`. For
  the converse, `eq_unramifiedCharacterSumClass_of_eulerPolynomial` with
  `c i = χ i ϖ` identifies `D`. The bridge lemma `weilCharacter_eq_localUnramifiedCharacter`
  rewrites `localUnramifiedCharacter F (χ i ϖ)` as `weilCharacter F e (χ i)`,
  using `characterSumClass_congr`. Then
  `isCharacterSumParameter_characterSumClass` applies.

## The standard Euler polynomial (`Langlands.Correspondence`)

`parameterEulerPolynomial F D` (from `UnramifiedEuler`) is the Weil–Deligne
Euler polynomial at `Φ` of the underlying pair class `parameterForget F D`. The
published `parameterEulerPolynomial_natDegree_eq_rank_iff` says that its
`natDegree` equals the rank `n` exactly when `IsUnramifiedParameterClass F D`.

- `parameterEulerPolynomial_eq_of_classOf`: if
  `classOf A = parameterForget F D`, then `parameterEulerPolynomial F D` is
  `LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F) Φ`. This unfolds
  the definition and uses `eulerPolynomialClass_classOf`.
- `parameterEulerPolynomial_unramifiedCharacterSumClass`:
  `parameterEulerPolynomial F (unramifiedCharacterSumClass F c) =
  ∏ i, (1 - C (c i) * X)`. The representative is the character-sum pair, by
  `parameterForget_characterSumClass`. `eulerPolynomial_characterSumPair` from
  `CharacterSumEuler` gives the factors `1 - C (c i ^ deg Φ) * X`, and
  `Weil.Local.localUnramifiedCharacter_geometricFrobenius` gives
  `localUnramifiedCharacter F (c i) Φ = c i`.
- `isUnramifiedParameterClass_of_parameterEulerPolynomial_eq`: for
  `D : WeilDeligneClass.{uF, uP} F r.succPNat` and `c : Fin (r + 1) → ℂˣ`, if
  `parameterEulerPolynomial F D = ∏ i, (1 - C (c i) * X)`, then
  `IsUnramifiedParameterClass F D`. By `natDegree_prod_one_sub_C_mul_X` the
  polynomial has degree `r + 1`, which is the rank, so
  `parameterEulerPolynomial_natDegree_eq_rank_iff` applies.
- `isUnramifiedParameterClass_unramifiedCharacterSumClass`:
  `unramifiedCharacterSumClass F c` is an unramified parameter class, by the
  two previous results.
- `parameterEulerPolynomial_eq_prod_iff`: for `D` of rank `r + 1` and
  `c : Fin (r + 1) → ℂˣ`,
  `parameterEulerPolynomial F D = ∏ i, (1 - C (c i) * X)` holds exactly when
  `D = unramifiedCharacterSumClass F c`. The reverse direction is
  `parameterEulerPolynomial_unramifiedCharacterSumClass`. For the forward
  direction, `Quotient.out (parameterForget F D)` is a representative `A`.
  `D` is unramified by the previous result, and
  `eq_unramifiedCharacterSumClass_of_eulerPolynomial` applies to `A`.
- `parameterEulerPolynomial_of_isCharacterSumParameter`: for a geometric
  candidate `e`, unramified `χ i`, and `IsCharacterSumParameter F e χ D`,
  `parameterEulerPolynomial F D = ∏ i, (1 - C (χ i ϖ) * X)`. This is
  `eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity`
  applied to the representative `Quotient.out (parameterForget F D)`.
- `isCharacterSumParameter_iff_parameterEulerPolynomial`: for a geometric
  candidate `e` and unramified `χ i`, `IsCharacterSumParameter F e χ D` holds
  exactly when `parameterEulerPolynomial F D = ∏ i, (1 - C (χ i ϖ) * X)`. No
  unramifiedness hypothesis on `D` is needed. The forward direction is the
  previous result. For the converse, `D` is unramified by
  `isUnramifiedParameterClass_of_parameterEulerPolynomial_eq`, and
  `isCharacterSumParameter_iff_eulerPolynomial` applies to the representative
  `Quotient.out (parameterForget F D)`.

The statements in the second section are phrased through an arbitrary
representative `A` of the underlying pair class, as in `CharacterSumEuler`. The
statements in the last section use `parameterEulerPolynomial`, which needs no
representative. The module adds no continuity hypothesis. Semisimplicity of `Φ`
comes from the Frobenius-semisimple condition built into `WeilDeligneClass`.
