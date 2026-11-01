# The actual finite integral Harris Rosati locus

This internal construction takes an actual abelian scheme `B/S`, an actual
integral action `a : O →+* End B` of the Harris integral order, and a morphism
`lam : B ⟶ DB`. Here `DB` and the actual contravariant dual maps are the existing
constructions from the explicitly supplied dual-scheme, evaluation, geometry,
and tensor/Picard compatibility data. The base `S` is locally noetherian.

It also takes an actual scheme `H/S` and a natural isomorphism representing the
relative Hom presheaf from `B` to `DB` on the full category of all locally
noetherian schemes over `S`. The construction does not prove the existence of
this representative. Separatedness of `H/S` is required for the geometric
conclusions below.

For the finite integer basis `b_k` of the actual Harris order and its integral
involution `tau`, the two families of global group homomorphisms are

`p_k = a(b_k) ≫ lam`,

`q_k = lam ≫ dual(a(tau(b_k)))`.

`integralRosatiLocus` applies the relative Hom-equation construction to these
families. It is an actual equalizer in schemes over `S`, hence has a specified
map to the base. When `H/S` is separated, this structural map is a closed
immersion. The underlying locus is locally noetherian because a closed
immersion is locally of finite type and `S` is locally noetherian. Local finite
type of the Hom representative is not needed for this construction.

For each locally noetherian test `T/S`, explicitly supplied dual and evaluation
constructions for `B_T` give the canonical dual base-change isomorphism `beta`.
The transported morphism is the published `dualAbelianBaseChangeMap`, namely
`lam_T = baseChange(lam) ≫ beta.hom`. The private pullback-equation lemma proves
that the base changes of `p_k` and `q_k` agree if and only if

`a_T(b_k) ≫ lam_T = lam_T ≫ dual_T(a_T(tau(b_k)))`.

The proof composes both sides with `beta.hom`, uses functoriality and the
published actual dual base-change naturality theorem, and cancels the
isomorphism. Thus this is an equivalence of actual morphism equalities, with
no faithfulness assumption on arbitrary base change.

`integralRosatiLocus_nonempty_iff_basis` combines that equivalence with the
actual equalizer classification: a morphism from `T` to the locus exists
precisely when the published `IntegralRosatiBasisEquations` hold for the
basechanged action and `lam_T`. With the explicitly supplied actual dual-map
additivity at `T`, `integralRosatiLocus_nonempty_iff` uses the published finite
basis criterion to obtain exactly `IntegralRosatiEquations` on every element
of the integral order. There is no additional Rosati premise on the original
family, and the assertions retain the original full test category, including
nonreduced and disconnected schemes.

The provenance is an internal derivation from
`RelativeHomEquationLocus`, `HarrisIntegralRosatiEquations`, and the actual
`DualAbelianBaseChangeNaturalityProof`; no new literature assertion is used.
This constructs the Rosati locus conditional on the stated Hom and dual data.
It does not establish Hom representability, the existence of an integral lift
of a rational action, a determinant or Lie condition, smoothness, projectivity,
or the normalized CM moduli comparison in the host representability theorem.
