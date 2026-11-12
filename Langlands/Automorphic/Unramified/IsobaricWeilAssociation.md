# Weak association of Weil representations with isobaric constituent data

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. The declarations lie in the namespaces
`Langlands.ClassField.Global.RelativeWeilGroup` (relative Weil group `W_{E/F}`) and
`Langlands.ClassField.Global.WeilMapSystem` (absolute Weil group `S.WeilGroup`). The module
extends Henniart's association of Weil representations with automorphic representations,
already published for actual cuspidal classes, to isobaric constituent data
(`Langlands.Automorphic.IsobaricData`). No representation, isobaric sum or spectrum is
constructed.

## Setting

The relative part uses number fields `F E : Type u`, `[Algebra F E]`, `[IsGalois F E]` and a
class family `c`, as in the published `Langlands.Automorphic.Unramified.RelativeWeilAssociation`.
The absolute part uses a system `S : WeilMapSystem c F Ω h`, as in
`Langlands.Automorphic.Unramified.AbsoluteWeilAssociation`. The isobaric relations also
assume `[CompactSpace (AdeleQuotient F)]`. Representations are published
`FiniteRepresentation.{0, u, uV} ℂ _`. `uP` is the universe of the spectral presentations'
local factors.

## Declarations

For both the relative group (`RelativeWeilGroup.…`) and the absolute group
(`WeilMapSystem.…`, with `S` explicit):

- `IsWeaklyAssociated.of_sameEulerPolynomials`: if `A` is weakly associated with a spectral
  system `s`, and `t` has the same rank and the same Euler polynomials as `s` outside a finite
  set, then `A` is weakly associated with `t`. On a cofinite set of places, `s` and `t` are
  both defined and agree, and `A` matches `s` there.
- `IsWeaklyAssociatedIsobaric A D`: some spectral system `s` of rank `D.rank` is attached to
  the isobaric data `D` (`IsobaricData.HasSpectralSystem`), and `A` is weakly associated
  with `s` in the published (relative) or absolute sense. In particular `A` is continuous
  of rank `D.rank`. At almost every finite place `v`, `A` is unramified along every local Weil
  map at `v`. Its Euler polynomial `det(1 - X A(Fr_v))` is the product of the constituents'
  Euler polynomials.
- `isWeaklyAssociatedIsobaric_ofCuspidal_iff`: for the data
  `IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank π)` of one actual cuspidal
  class `π`, isobaric association is the published cuspidal class relation
  `IsWeaklyAssociatedClass A π`. It follows from `HasSpectralSystem.exists_ofCuspidal`,
  `hasSpectralSystem_ofCuspidal_of` and `IsWeaklyAssociated.of_sameEulerPolynomials`.
- `IsWeaklyAssociatedIsobaric.of_equiv`: the relation depends only on the equivalence class
  of `A`, through the published (relative) or absolute `IsWeaklyAssociated.of_equiv`.

Absolute only:

- `isWeaklyAssociatedIsobaric_inflate`: relative isobaric association of a representation
  `A` of `W_{K/F}` gives absolute isobaric association of `S.inflate K A`. This holds when
  local-to-global Weil maps exist at all but finitely many finite places, an explicit
  hypothesis passed to `isWeaklyAssociated_inflate`.

## Source correspondence

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique*, Invent. Math. 139 (2000), literature ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`, §2.2, printed p.444
(PDF p.6). A continuous representation `S` of degree `n` of `W_F` and an automorphic
representation `Π` of `GL_n(𝔸_F)` are associated if `L(S_v, s) = L(Π_v, s)` at almost every
finite place where both are unramified. The same paragraph considers isobaric `Π`.

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), literature ID `arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`, Chapter 3, Definition
4.1 and the notation `Π₁ × ⋯ × Π_b`, printed p.202 (PDF p.216): representations induced from
cuspidal data.

### Derived formulation

1. **Isobaric `Π` through data.** Henniart's `Π` may be isobaric. Here it is replaced by its
   cuspidal constituent data. `L(Π_v, s)` at unramified `v` is the product of the
   constituents' factors, which the attached system encodes through Euler polynomials (see
   `IsobaricData.md`). The remaining conventions are those of the cuspidal relations in the
   relative and absolute association modules: Euler polynomials, one cofinite set,
   geometric normalizations, and explicit continuity and rank.
2. **Agreement with the cuspidal case.** For data of one cuspidal class, the relation is
   proved equal to the published cuspidal relation, so no second notion of association is
   introduced for cuspidal representations.

## Scope

The module does not prove existence or uniqueness of associated data or representations,
the Jacquet–Shalika rigidity that makes associated data unique, or any compatibility at
ramified places.
