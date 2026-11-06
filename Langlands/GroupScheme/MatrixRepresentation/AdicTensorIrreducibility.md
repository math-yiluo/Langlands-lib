# Tensor irreducibility from actual augmentation quotient coefficients

Let `k : Type u` be a field, `G` an actual affine group scheme over `k`,
and `ρ` an actual matrix representation on a finite coordinate type
`n : Type`. `quotientCoefficientMap ρ N` is the `k`-linear map from the
linear dual of the actual algebra `O(G)/I^N` to matrices on `n`, obtained
by applying a functional entrywise to the representation at the genuine
augmentation quotient point. Here `I` is the identity augmentation ideal.
No reducedness or finite dimension is required of the quotient algebra.

Coefficient extraction commutes with the action on constant vectors.
Consequently every all-affine-test stable subspace is preserved by every
extracted matrix. If `k` is algebraically closed, `G` is reduced and
locally of finite type, `O(G)` is a Noetherian domain, and `ρ` is
irreducible, the previously proved universal coefficient and ideal-power
separation results give a single `N` at which this map is surjective.

For an exponential characteristic `p`, whenever `N ≤ p^e`, the actual
Frobenius-powered second representation is identity at the quotient
point. Coefficients of `ρ.tensor (σ.frobeniusPower p e)` therefore recover
the entire first matrix factor from this same quotient. For each rational
point, multiplication of the diagonal tensor matrix by the inverse first
matrix isolates the second rational matrix factor.

Suppose further that `p` is prime, `CharP k p`, and `σ` is irreducible.
To obtain every second-factor matrix, the proof takes the entrywise
Frobenius preimage of the subalgebra whose right tensor matrices preserve
the subspace. This is a `k`-subalgebra even though scalar Frobenius need
not be `k`-linear. The isolated rational matrices belong to this preimage.
Actual-to-rational irreducibility and Burnside imply that their linear
span is every matrix. Perfectness of the algebraically closed field
makes entrywise Frobenius surjective, so every second matrix factor
preserves the subspace. The two full matrix factors generate all
matrices on the original product coordinates. A rank-one matrix sending
any fixed nonzero vector to an arbitrary vector then proves that the
stable subspace is zero or full. Irreducibility of each supplied factor
ensures that the tensor coordinate space is nonzero.

`exists_forall_isIrreducible_tensor_frobeniusPower` thus supplies one `E`,
chosen from `ρ` before `σ`, such that for every `e ≥ E` and every finite
coordinate type `m : Type` with an irreducible actual representation
`σ`, the entire actual tensor is irreducible. The coordinate hypotheses
are precisely the reduced, locally finite type, Noetherian domain
hypotheses above. The proof takes `E = N` and uses `e < p^e`.

For smooth connected affine `G`, the existing coordinate-domain and
Noetherianity theorems discharge these hypotheses; smoothness and
connectedness also give integrality and hence reducedness.
`exists_forall_isIrreducible_tensor_frobeniusPower_of_smooth` is this
specialization. The corresponding
`exists_forall_rationalRepresentation_isIrreducible_tensor_frobeniusPower_of_smooth`
has rational irreducibility premises and conclusion on the same
coordinate spaces. Finally
`exists_ge_rationalRepresentation_isIrreducible_tensor_frobeniusPower_of_smooth`
gives cofinally many exponents for each supplied pair.

This is an internal derivation from the actual quotient points,
coefficient separation, matrix tensor factors, rational irreducibility,
Burnside, and perfect-field Frobenius. It assumes no additive or root
generating family. The group and both irreducible representations remain
supplied inputs. No highest-weight or Steinberg representation, entire
induced-space comparison, or big-cell datum is constructed here; the
exact `SteinbergBigCellStatement` remains a separate proof obligation.
