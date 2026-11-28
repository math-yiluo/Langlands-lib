# Proof of the twist reduction of (CI1) for Henniart's candidate

Module `Langlands.Correspondence.HenniartCandidateBaseChangeTwistReductionProof`, namespace
`Langlands.Henniart`, universes `uK uW uV`. The theorem `candidateBaseChangeTwistReduction` has
type `CandidateBaseChangeTwistReductionStatement.{uK, uW, uV}` (module
`Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement`). Given candidate
existence, a step `S` (\(M/L\), \(f=f(M|L)\)) and a map `Ch` that commutes with unramified twists
(`Numerical.IsUnramifiedTwistEquivariant`) and satisfies (CI1) on the classes of finite image
(`Numerical.IsCandidateBaseChangeCompatibleOnFiniteImage`), it proves (CI1) for `Ch`
(`Numerical.IsCandidateBaseChangeCompatible`). The module also imports
`Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof` and
`Langlands.Correspondence.HenniartGaloisPullback`.

## Auxiliary results (namespace `Langlands.Henniart.Numerical`)

- `twistDirectSumEquiv`, `twistClass_directSumClass`: for a character \(\chi\) of a group \(G\),
  the twist of a finite direct sum of representations is the direct sum of the twists, through
  the identity of the carrier \(\bigoplus_i A_i\) (both actions send \(x\in A_i\) to
  \(\chi(g)A_i(g)x\)); hence `twistClass χ (directSumClass c) = directSumClass (twistClass χ ∘ c)`.
- `directSumClass_fin_cast`: a direct sum of classes indexed by `Fin n` does not change when the
  family is reindexed along `Fin.cast` for `n = m`.
- `weilClassForget_weilUnramifiedTwist`: the underlying class of `Numerical.weilUnramifiedTwist K k z σ`
  is `twistClass` of the underlying class of `σ` by the unramified character with value `z`
  (`FiniteRepresentation.forget_continuousIrreducibleTwistClass`).
- `unramifiedCharacter_comp_extensionWeilMap`: that character of \(W_L\), composed with the Weil
  map \(W_M\to W_L\) of the step, is the unramified character of \(W_M\) with value \(z^{f}\)
  (`Weil.Local.localUnramifiedCharacter_extensionWeilMap`).
- `IsRestrictionDecomposition.weilUnramifiedTwist`: if `m` is a restriction decomposition of `σ`,
  then the members of `m` twisted by \(z^{f}\) form a restriction decomposition of the twist of
  `σ` by \(z\). The restriction of the twisted class is the twist of the restriction by the
  restricted character (`LocalNumerical.restrictClass_twistClass`); this is the twist of the
  direct sum, hence the direct sum of the twisted summands; the list of twisted members has the
  same length (`List.length_map`, `directSumClass_fin_cast`) and the same entries
  (`List.getElem_map`).
- `weilUnramifiedTwist_weilUnramifiedTwist`, `weilUnramifiedTwist_one`: twists by `a` and `b`
  compose to the twist by `a * b`, and the twist by `1` is the identity
  (`FiniteRepresentation.continuousIrreducibleTwistEquiv_mul`, `..._one`, and multiplicativity
  of `Weil.Local.unramifiedCharacterHom`).
- `multiset_pmap_map`: `Multiset.pmap f (s.map g) H` is `Multiset.pmap (f ∘ g) s _`
  (`List.pmap_map`).

## The proof of `candidateBaseChangeTwistReduction`

Fix `k`, `hL : StableExistsAt S.base k.succPNat`, \(\sigma\), a restriction decomposition `m` of
\(\sigma\) and stable existence `hmS` over \(M\) for its members.

1. `UnramifiedTwistIndependenceStatement` follows from candidate existence by
   `Extension.unramifiedTwistIndependence_of_reciprocity` with
   `LocalClassField.commonClosureReciprocityExistence`.
2. `Extension.rankExtensionBasis_spec` gives a stable decomposition \(\sigma=z\cdot b_0\)
   (`Extension.IsStableDecomposition`). Put \(\sigma_0\) = the twist of \(\sigma\) by \(z^{-1}\).
   Then the twist of \(\sigma_0\) by \(z\) is \(\sigma\), `b₀.val = ⟨k.succPNat, σ₀⟩`
   (`Extension.IsStableDecomposition.eq_twist_inv`), and \(b_0\) factors through a finite quotient
   (the first clause of the `StableMap.IsStableImage` in the decomposition), so \(\sigma_0\) is a
   class of finite image.
3. The members of `m` twisted by \(z^{-f}\) (that is, \((z^{-1})^{f}\)) form a restriction
   decomposition `m₀` of \(\sigma_0\), with the same ranks, so `hmS` gives stable existence for
   them. (CI1) on classes of finite image gives
   `Ch k (rankExtension S.base hL σ₀) = m₀.pmap (rankExtension S.top …)`.
4. Then
   `Ch k (rankExtension S.base hL σ)`
   `= Ch k (rankExtension S.base hL (twist z σ₀))`
   `= Ch k (supercuspidalUnramifiedTwist S.base k z (rankExtension S.base hL σ₀))`
   (`Extension.rankExtension_twist` over \(L\))
   `= (Ch k (rankExtension S.base hL σ₀)).map (twist by z ^ f)` (the twist property of `Ch`)
   `= (m₀.pmap (rankExtension S.top …)).map (twist by z ^ f)` (step 3).
   By `Multiset.map_pmap` and `multiset_pmap_map` this is a `pmap` over `m`; for each member
   \(\tau\), `Extension.rankExtension_twist` over \(M\) moves the twist by \(z^{f}\) inside, and
   the twists by \((z^{-1})^{f}\) and \(z^{f}\) cancel. `Multiset.pmap_congr` gives
   `m.pmap (fun τ h => ⟨τ.1, rankExtension S.top h τ.2⟩) hmS`, which is (CI1) at \(\sigma\).

The proof uses no hypothesis beyond those of the statement; its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
