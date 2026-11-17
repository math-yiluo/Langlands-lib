# Smoothness of supplied multiplicative-type centralizer representatives

This internal derivation concerns a smooth relatively affine group scheme `G`
over an arbitrary scheme `S`, a commutative group scheme `H` of multiplicative type, and a
map `i : H → G`. Every actual representative `z : Z → G` of the full centralizer
of the range of `i` is smooth over `S`. The map `i` need not be an immersion.
Over `Spec R` the definition `diagonalizableSmoothCentralizerModelOverSpec`
chooses a smooth closed centralizer representative for a diagonalizable `H`.
Existence over an arbitrary base is not asserted here.

Over `Spec R`, a diagonalizable `H` is identified with the actual ring-level
diagonalizable group by `Diagonalizable.baseChangeIso`. Precomposition preserves
the range of `i`. The published smooth closed diagonalizable centralizer model
therefore represents the same functor as `z`, and the compatible isomorphism
transfers smoothness to `Z`.

The auxiliary base descent lemma specializes the published general
`FppfLocal.isLocalAtTarget_fppfPrecoverage` to smooth morphisms and uses
`MorphismProperty.IsLocalAtTarget.of_zeroHypercover`. Smoothness is therefore
detected on arbitrary small fppf covering families. No quasi-compactness of the
original covering family is required.

The canonical affine open cover then proves the diagonalizable assertion over
any base. The fppf splitting cover in `IsMultiplicativeType` proves the final
assertion. Base change of the supplied representative represents the
base-changed centralizer on all scheme tests. All results are derived from the
imported smooth centralizer, subgroup base-change and morphism descent modules.
