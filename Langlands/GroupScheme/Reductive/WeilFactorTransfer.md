# Transfer of idempotents along an isomorphism of Weil restrictions

Worker 47.

Module `Langlands.GroupScheme.Reductive.WeilFactorTransfer`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports
[`WeilFactorProjection`](WeilFactorProjection.md) and the statement module
[`WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md). Nothing
here proves that statement. The results that use it take a proof `hR` of it as a hypothesis.

## Provenance

Provenance: derived/internal. An isomorphism `Φ : R_{B/A}(G) ≅ R_{B''/A}(G'')` conjugates
normal idempotent endomorphisms to normal idempotent endomorphisms. By the rigidity statement
these are the factor projections. So `Φ` induces a map `e ↦ transfer e` from idempotents of
`B ⊗_A T` to idempotents of `B'' ⊗_A T`, for every `A`-algebra `T`. This is the formal
counterpart of "an isomorphism of products of absolutely simple groups permutes the factors"
in the proof of Conrad, *Reductive group schemes*, Proposition 6.4.4 (pp.232–233).

## Declarations

Two finite projective `A`-algebras `B`, `B''`, affine groups `G`, `G''` locally of finite type
over `Spec B`, `Spec B''`, and `Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G''`.

- `transportNat f T : Fun A B G T ⟶ Fun A B'' G'' T`: a homomorphism of Weil restrictions
  acting on points (`affinePointsTarget`). `transportNat_inv_hom` and `transportNat_hom_inv`
  record that `Φ.inv` and `Φ.hom` give inverse transformations.
- `conj Φ ψ := transportNat Φ.inv ≫ ψ ≫ transportNat Φ.hom`, with `conj_comp`, `conj_idem`,
  `pt_conj` (formula), `conj_normal` (preserves normality), `pt_conj_eq_one`,
  `restrict_conj` and `conj_symm_conj`.
- `rigidity hR hred'' hsimple''`: the rigidity statement for `G''`, in terms of
  `factorProjection`. Every idempotent normal `ψ` equals `factorProjection e''` for some
  idempotent `e''`.
- `factorProjection_injective hR …`: factor projections of idempotents determine the
  idempotents. This is the uniqueness part of the rigidity statement.
- `transfer Φ hR hred'' hsimple'' e`: for idempotent `e`, an idempotent `e''` (chosen with
  `Classical.choose`) with `factorProjection e'' = conj Φ (factorProjection e)`, and `0`
  otherwise.
- `transfer_spec`, `transfer_isIdempotentElem`, `factorProjection_transfer`: its defining
  property.
- `transfer_mul`: `transfer (f e) = transfer f · transfer e`.
- `transfer_lTensor`: `transfer` commutes with base change `T ⟶ T₁`.
- `transfer_zero`: `transfer 0 = 0`.
- `transfer_symm_transfer` (using the rigidity statement for `G` as well): the transfer along
  `Φ.symm` inverts the transfer along `Φ`.
