# The conductor formula from weak cyclic presentations

`CuspidalSigmaLiftConductorFromWeakPresentationsStatement` reduces the
four-universe conductor identity to three propositions. They are
`CuspidalPairGlobalFunctionalEquationStatement` for the small global
presentations, `SigmaLiftUniquenessStatement` at irreducible local
actions, and `CuspidalSigmaLiftWeakPresentationDataStatement`.

The presentation premise is for the characteristic-zero field case
above rank one and for the local data of the conductor statement. It
supplies a cyclic Galois extension of number fields with compact adelic
quotients and compatible bicontinuous identifications at a lower finite
place with a unique upper place. The identifications commute with the
scalar embeddings and carry the given local generator to the completion
of the global generator. The cuspidal spectral presentations have
irreducible admissible finite components. The lower distinguished
component is supercuspidal and agrees with the given local action up to
an unramified determinant twist, and the two distinguished components
satisfy the actual distributional tensor lift identity. The upper
spectral system is an arithmetic weak base change of the lower one.

Transport the tensor lift to the distinguished upper completion. Local
lift uniqueness identifies the upper action with the specified orbit
product up to the norm pullback of the lower unramified twist. Choose
actual contragredients of the original presentations and apply
`weakBaseChangeAuxiliaryTwist`. The resulting finite-order Hecke
character and its idelic norm pullback are trivial at the distinguished
places. The local equivalences for Hecke twists preserve the
distinguished identifications, and the upper orbit calculation gives
root separation for the certified forward and dual polynomials there.

At every other finite place, `commonTwistPairComparison` gives equality
of the forward and dual grouped Euler products and the forward
positive epsilon bases. The proof uses the spherical relation where
available and the highly ramified formulas at the finite set of
remaining places. The completed-equation reduction with these data
gives the conductor identity. That reduction also includes the
unconditional rank-one case.

The global functional-equation argument comes from Arthur–Clozel,
Chapter 1, Proposition 6.9(ii), printed pp. 69–70 (PDF pp. 83–84),
literature ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The common auxiliary twist uses the highly ramified factor formulas
from Jacquet–Shalika, Proposition (2.2), printed p. 320 (PDF p. 2),
literature ID `jacquet-shalika-1985-ramified-factors`, SHA-256
`0864a6633c3cf430f576f91eadd05a7f11d88eea1b47095943d3ea76f7c9946b`.
