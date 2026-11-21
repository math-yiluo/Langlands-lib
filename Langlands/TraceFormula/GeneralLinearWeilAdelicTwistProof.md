# Adelic comparison for the Weil restriction of GLₙ

`Langlands.TraceFormula.generalLinearWeilAdelicTwist.{u}` proves
`GeneralLinearWeilAdelicTwistStatement.{u}` for a finite extension `L/K` of
number fields and every `n : ℕ`. For `W = Res_{L/K} GL_n`, the comparison `Φ`
from `W(𝔸_K)` to `GL_n(𝔸_L)` is a topological group isomorphism. It carries
each relative automorphism `σ : L ≃ₐ[K] L` to the entrywise action of `σ`
and identifies the image of `W(K)` with the diagonal image of `GL_n(L)`.

## Topological group isomorphism

The helper `adelicIso` applies `AdelicGroupPoints.map` to both directions of
an isomorphism of group schemes. These maps are continuous group
homomorphisms. The identities `map_comp_apply` and `map_id_apply` give the
two inverse laws. The proof composes `AdelicGaloisUnit.weilAdelicEquiv`,
`adelicIso` for `GeneralLinear.baseChangeIso`, and
`GeneralLinearGroupPoints.adelicHomeomorph`. The underlying function is
definitionally `Φ`.

## Entrywise action

The lemma `ringEquiv_eq_adeleEquiv` compares `AdeleGalois.ringEquiv K L σ`
with `AdelicFunctoriality.adeleEquiv σ.toRingEquiv`. It lifts an arbitrary
adele through `numberFieldAdeleTensorEquiv K L` and uses tensor induction.
On a pure tensor `a ⊗ₜ b`, `AdeleGalois.ringEquiv_tensor` and
`numberFieldAdeleTensorEquiv_tmul` give the product of the diagonal image
of `σ a` and the image of `b` from `𝔸_K`. For `adeleEquiv`,
`adeleEquiv_diagonal` gives the same diagonal factor
and `IdeleGaloisDescentProof.adeleEquiv_adeleInclusion` shows that the
factor from `𝔸_K` is fixed. Both maps preserve addition.

The lemma `baseChange_affine_entry` computes an entry over an arbitrary
affine test algebra. It unfolds `GeneralLinear.baseChangeIso` using
`comp_isoOfPoints_hom` and `baseChangeGLPointsEquiv`. The comparison
`Corepresented.map_affineSectionsIso_pointsEquiv` expresses the entry as
evaluation of `GeneralLinear.entrySection` on global sections.
`baseChangePointsEquiv_left` identifies the point on which it is evaluated
with the projection to the ground `GL_n`. The proof specializes this
calculation to the test algebra `𝔸_L`.

Using `adelicAut_apply` and `unitGaloisAut_hom`, the theorem applies
`galoisTwist_weilAdelicEquiv` to transport the Weil-restriction action to the
base change. The identity `galoisTwist_left_fst` from
`AdelicGaloisTwistDescent` expresses the projected twisted point as
precomposition by `Spec` of `AdeleGalois.ringEquiv K L σ`.
`Scheme.Hom.comp_appTop` and `Scheme.ΓSpecIso_naturality` turn that
precomposition into application of the same ring equivalence to the
evaluated coordinate. The ring comparison therefore gives precisely the
entry map in `AdelicGLTransport.adelicEquiv n σ.toRingEquiv`. The proof
uses `Units.ext` and `Matrix.ext` to conclude equality of the invertible
matrices.

## Rational points

`AdelicWeilRestriction.map_rationalSubgroup` identifies the rational
subgroups under `weilAdelicEquiv`. Injectivity of this equivalence
reflects membership.
For the base-change isomorphism, `AdelicGroupPoints.rational_naturality`
in each direction gives the membership equivalence. Finally,
`GeneralLinearGroupPoints.adelicHomeomorph_rational` computes the image
of every diagonal point, and `GeneralLinearGroupPoints.rationalEquiv`
supplies a preimage for each rational invertible matrix. Injectivity of the
homeomorphism then reflects membership in the diagonal image.

## Relation to the sources

This is a derived Library comparison. Arthur and Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), set up
`σ`-conjugation on `GL_n(E)` for a cyclic extension `E/F` in Chapter 1, §1,
in the setup of Lemma 1.1 (printed p. 3, PDF p. 17). Their §2.2, including
Lemma 2.5, uses the action on `GL_n(𝔸_E)` and rational classes from `GL_n(E)`
(printed pp. 12–14, PDF pp. 26–28). Registered source
`arthur-clozel-1989-base-change`.

Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
§18.5, give the reductive group setting with a finite-order automorphism
in equation (18.30) and use rational twisted conjugacy classes in
Corollary 18.5.1 (printed pp. 486–488, PDF pp. 493–495). For a cyclic
extension, the comparison identifies the Weil-restriction group and its
automorphism in this setting with the matrix group and action used by
Arthur and Clozel. The Lean theorem covers every relative automorphism
of a finite extension of number fields. Registered source
`getz-hahn-2024-automorphic-representations`.
