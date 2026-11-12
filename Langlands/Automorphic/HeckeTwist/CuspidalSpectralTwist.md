# Twists of cuspidal spectral presentations by any Hecke determinant character

Author: Worker 5136.

A cuspidal spectral presentation `P` of an irreducible cuspidal realization `S`
of `GL_{r+1}(𝔸_F)` (the Library's `CuspidalSpectralPresentation`) consists of a
finite slice of `S`, local factors, a finite tensor presentation of the slice,
reference vectors, an exceptional set and unramified data. For an arbitrary
Hecke character `χ`, this internal module builds the corresponding presentation
of the twist `S.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.OperatorTwist`). It is in the namespace
`Langlands.Automorphic.CuspidalSpectralPresentation`.

- `heckeDeterminantTwistLocalFactor P χ v`: the local factor of `P` at `v`
  twisted by `χ_v ∘ det`, as a smooth representation. Smoothness uses the open
  kernel `finiteLocalHeckeDeterminant_isOpen_ker` (module `Admissibility`). The
  `_representation` lemma says its representation is the Library's
  `Langlands.twist`.
- `heckeDeterminantTwist P χ`: the presentation of `S.heckeDeterminantTwist χ`.
  Its finite slice is the twisted slice (module `FiniteSlice`), its local
  factors are the twisted ones, and its tensor presentation is the twisted one
  (module `FiniteTensorTwist`), with the same reference vectors. Its exceptional
  set is `P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1)` (module
  `FiniteTail`), and its unramified data are the twisted ones (module
  `PresentedUnramifiedData`). The `@[simp]` lemmas `_finiteSlice`,
  `_tensorExceptional` and `_exceptional` record these fields.
- `heckeDeterminantTwist_spectralSystem`: the spectral system of the new
  presentation is the system of `P` with every Satake parameter at `v` scaled
  by `χ_v(ϖ_v)` (`SpectralSystem.scale χ.finiteUniformizerValue`), restricted
  to the places outside the enlarged exceptional set.
- `heckeDeterminantTwistLocalComponentEquiv`: at every finite place `v`, the
  local component of the new presentation is equivalent, as a representation
  of `GL_{r+1}(F_v)`, to `(P.localComponent v).heckeDeterminantTwist χ`. The
  proof composes the Library's `localComponentEquiv` of both presentations with
  `Langlands.twistEquiv` and `heckeDeterminantTwistRepresentationEquiv`
  (module `FiniteLocalTwist`). `heckeDeterminantTwist_localComponent_isoClass`
  restates it for isomorphism classes.
- `heckeDeterminantTwist_powerTrace` and `heckeDeterminantTwist_eulerPolynomial`:
  outside the enlarged set, power traces are multiplied by `χ_v(ϖ_v)^k` and the
  Euler polynomial `P_v(X)` becomes `P_v(χ_v(ϖ_v) X)`.
- `samePowerTraces_heckeDeterminantTwist` and
  `sameEulerPolynomials_heckeDeterminantTwist`: the scaled system of `P` and the
  system of the new presentation have the same power traces, respectively Euler
  polynomials, at almost every place.
- `heckeDeterminantTwist_samePowerTraces_scale_iff`,
  `heckeDeterminantTwist_sameEulerPolynomials_scale_iff`,
  `heckeDeterminantTwist_samePowerTraces_iff` and
  `heckeDeterminantTwist_sameEulerPolynomials_iff`: twisting by the same `χ`
  preserves and reflects almost-everywhere agreement of spectral systems, with
  a scaled system or with the twist of another presentation `Q`, in any rank.

Provenance: internal. This is the presentation part of the Library module
`Langlands.Automorphic.CuspidalSpectralDeterminantTwist` with the finite-order
hypothesis removed. The sections on isomorphism classes of cuspidal
realizations are not ported. The construction realizes, for presentations,
the twist `Π ↦ (χ ∘ det) ⊗ Π` of Henniart (2000), §2.2.
