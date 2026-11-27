# Transport of Jacquet nonvanishing to a level-zero simple type

Theorem `levelZero_not_subsingleton_jacquet` takes level-zero data
`IsLevelZeroSimpleTypeData L e (glRepresentationToAut ρ)` for a smooth
representation `ρ` of `J ≤ GL_n(F)`, with `n > 0` and `e ≥ 2`. If a smooth
representation `π` of `GL_n(F)` contains `ρ`, the theorem obtains a nonzero
Jacquet quotient along a conjugate of the unipotent radical for the block
shape `(f, n - f)`, with `f` the dimension of each layer of `L`. The
conjugating matrix is `changeGL`, formed from the adapted basis.
[Published proposition](LevelZeroNonmaximalTypeJacquetStatement.md)

## Proof

1. Unpack the data of BK93 (5.5.10)(b). The order `𝔄(L)` is principal of
   period `e`, and the type on its unit group is equivalent to the inflation
   through the layer reduction `φ` of the `e`-fold tensor power of an
   irreducible cuspidal representation `σ₀` of `GL_f(k_F)`. The type is
   trivial on the first unit subgroup.
2. Choose a uniformizer and use the adapted basis to obtain `n = f e` and
   `0 < f < n`. The isomorphism `stdToGL` transports `J0` and `J1` to the unit
   group and first unit subgroup of `𝔄(L)`. Pull back `ρ` to `J0` and `π`
   to the standard matrix group. The nonzero map witnessing `ContainsType`
   intertwines the pullbacks on `J0`.
3. The subgroup `J1` is open by `isOpen_unitFiltration` and the homeomorphism
   `stdToGLContinuous`. It is closed in the compact group `J0`, whose
   compactness follows from `isCompact_unitFiltration_zero`. The pullback
   of `π` is smooth by `isSmooth_comp`.
4. By `layerReduction_entry` and `residue_pairGL_unipLift`, the lifted
   element `diag(unipLift r Z, 1)` on blocks `0, m` reduces to
   `Pi.mulSingle 0 (cornerU r Z)`. Transporting the vanishing sums of
   `sum_tensorPower_cornerU_eq_zero` across the type equivalence gives the
   hypotheses of `not_subsingleton_coinvariants_coarseN`.
5. The resulting quotient for the first-block radical `coarseN` is nonzero.
   Each element of `B.conjugateUnipotent g` is the image of an element of
   `coarseN` under `stdToGL`, by
   `exists_mem_coarseN_of_mem_conjugateUnipotent`. Thus its relation submodule
   is contained in the relation submodule for the pulled-back action. The
   quotient along `B.conjugateUnipotent g` surjects onto the nonzero quotient.

[Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)
