# Arithmetic pullback of a supercuspidal component

Module `Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof`. It
proves `ArithmeticComapSupercuspidalComponentStatement.{uK, uL, uV}` (module
`Langlands.Automorphic.CuspidalArithmeticTransportStatement`), at independent
universes `uK`, `uL` for the number fields and `uV` for the carriers of the
local factors.

## Results

Let `e : K ≃+* L` be a ring isomorphism of number fields, `S` a cuspidal
realization over `L` of rank `r + 1`, and `P` a spectral presentation of `S`
with local factors in `Type uV`. The pulled-back presentation
`P.arithmeticComap e` of `S.arithmeticComap e` is the Library's
`CuspidalSpectralPresentation.arithmeticComap`
(`Langlands/Automorphic/CuspidalArithmeticSpectralTransportProof.lean`). Its
local factors stay in `Type uV`.

- `CuspidalSpectralPresentation.arithmeticComap_localComponent_isSupercuspidal_iff`:
  for every finite place `v` of `K`, the local component of
  `P.arithmeticComap e` at `v` is supercuspidal (`LocalRealization.IsSupercuspidal`)
  if and only if the local component of `P` at the place
  `finitePlaceEquiv e.symm v` of `L` is supercuspidal.
- `CuspidalSpectralPresentation.arithmeticComap_localComponent_isSupercuspidal`:
  if the local component of `P` at a finite place `w` of `L` is supercuspidal,
  then so is the local component of `P.arithmeticComap e` at
  `finitePlaceEquiv e w`.
- `arithmeticComapSupercuspidalComponent`: the target statement.

## Proof

**The pulled-back local factor.** By definition of
`CuspidalSpectralPresentation.arithmeticComap`, its local factor at a place `v`
of `K` is `SmoothRep.pullback (localEquiv (r + 1) e.symm v).symm
(P.localFactor w)`, where `w = finitePlaceEquiv e.symm v`. The carrier is that
of `P.localFactor w`. The action is pulled back along the inverse of
`AdelicGLTransport.localEquiv (r + 1) e.symm v`, the entrywise isomorphism
`GL_{r+1}(L_w) ≃ GL_{r+1}(K_v)` of the completions. That isomorphism is built
from `finiteCompletionEquiv e.symm v : L_w ≃+* K_v`. Write
`σ = (finiteCompletionEquiv e.symm v).symm : K_v ≃+* L_w`. It is continuous
with continuous inverse (`continuous_finiteCompletionEquiv_symm`,
`continuous_finiteCompletionEquiv`). The pulled-back action is then, by `rfl`,
the action of `P.localFactor w` composed with
`GeneralLinear.fieldEquiv (r + 1) σ`. The comparison uses this actual local
factor at the given place. It does not use the numerical spectral system, so
`v` need not be unramified for the presentation.

**Reduction to the local actions.**
`LocalRealization.isSupercuspidal_iff_representation`
(`Langlands/Automorphic/Unramified/CyclicInductionSupercuspidalReduction.lean`)
rewrites `IsSupercuspidal` of a local component. The definition asks for
irreducibility, admissibility and a supercuspidal `p`-adic class. The rewritten
form asks for irreducibility and `GeneralLinear.IsSupercuspidal` of the
component's action.

**Components and factors.** The embedded local component of a presentation
comes with `FiniteTensorPresentation.localComponentEquiv`, an equivariant
linear equivalence from the local factor. The proof applies it to `P` at `w`
and to `P.arithmeticComap e` at `v`. Irreducibility crosses these equivalences
by `Langlands.isIrreducible_iff_of_equiv`, and supercuspidality by
`GeneralLinear.isSupercuspidal_of_equiv`.

**Field transport.** Irreducibility of the pulled-back factor is equivalent to
irreducibility of `P.localFactor w`, by
`isIrreducible_comp_continuousMulEquiv_iff` applied to the inverse of
`localEquiv (r + 1) e.symm v`. Supercuspidality of the pulled-back factor is
equivalent to supercuspidality of `P.localFactor w`, by
`GeneralLinear.isSupercuspidal_comp_fieldEquiv_iff`
(`Langlands/VirtualRepresentation/Supercuspidal/FieldTransport.lean`). Under
entrywise transport, proper standard block parabolics and conjugates of their
unipotent radicals correspond, so all proper Jacquet modules vanish together.
Chaining the four equivalences gives the `iff` lemma in both directions.

**The corresponding place.** `finitePlaceEquiv e.symm v` equals
`(finitePlaceEquiv e).symm v`, by `finitePlaceEquiv_trans`,
`RingEquiv.self_trans_symm` and `finitePlaceEquiv_refl`. At
`v = finitePlaceEquiv e w` the corresponding place of `L` is therefore `w`.
This gives the second lemma.

**The class statement.** The hypothesis `c.HasSupercuspidalComponent w`
supplies a representative `S` of `c` and a presentation `P` of `S`, with local
factors in `Type uV`, whose local component at `w` is supercuspidal. Then
`S.arithmeticComap e` represents `IsoClass.arithmeticComap e c`; this holds
definitionally (`IsoClass.arithmeticComap_isoClass`). The presentation
`P.arithmeticComap e` has local factors in `Type uV`, and by the second lemma
its local component at `finitePlaceEquiv e w` is supercuspidal. This is
`(IsoClass.arithmeticComap e c).HasSupercuspidalComponent (finitePlaceEquiv e w)`
with the same carrier universe `uV`.

## Provenance

The statement is a transport-of-structure interface, derived rather than taken
from the literature. Harris uses it without comment in the proof of
Proposition 4.8 (M. Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210, printed p. 203;
`math_9611226v1.tex` lines 1646–1663). There the supercuspidal representations
`α^j(Π(e,t-1)_{v(*)_1})` are treated as the local components of the Galois
conjugates `α^j(Π(e,t-1))` at the place above `v(*)_1`. The proof above is an
internal consequence of the Library's presentation pullback, the local
component equivalences of finite tensor presentations, and entrywise field
transport of supercuspidality.
