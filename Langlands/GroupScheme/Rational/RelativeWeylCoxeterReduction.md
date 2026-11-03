# Reducing the relative Weyl Coxeter theorem to three published statements

This module is a conditional supporting step toward
`RelativeWeylCoxeterStatement` (module
`Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement`). For a maximal
split torus `i` of a connected reductive group `G` over a field `k` and a
generic cocharacter `ν`, that statement says `N(k)/Z(k)` is a finite Coxeter
group that realizes the relative root action. The module shows that the
statement follows from three published statements in the Library, none of
which it proves:

* `RelativeRootSystemStatement` (module `Langlands.GroupScheme.Rational.Statement`):
  for every maximal split torus `i` of a connected reductive group, the
  relative roots satisfy `HasRelativeRootSystem i`;
* `RelativeRootReflectionExistenceStatement` (module
  `Langlands.GroupScheme.Rational.RootReflectionExistenceStatement`): for every
  such `i` there is integral reflection data `D : RelativeRootReflectionData i`
  whose chosen representative of each relative root `a` is a rational point of
  `RelativeRoot.kernelCentralizer i a`;
* `Langlands.Group.RootPairingWeylCoxeterStatement` (module
  `Langlands.Group.RootPairingCoxeterStatement`), used at the universes
  `.{u, 0, u, u}`: the Weyl group of a finite crystallographic root pairing over
  a linearly ordered field is finite and is a Coxeter group on the simple
  reflections of the base for a generic linear form, with the inversion-count
  length formula and the descent criterion.

All the mathematical work is in the published module
`Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly`. Its theorem
`RelativeRootReflectionData.hasRelativeWeylCoxeterSystem_of_rootPairing`
carries a Coxeter system on the Weyl group of `D.rootPairing` over to
`N(k)/Z(k)`. This module only supplies its inputs. The universe is an
arbitrary `u`.

## Per-torus step

`RelativeRootReflectionData.hasRelativeWeylCoxeterSystem_of_rootPairingWeylCoxeter`
works for a fixed field `k : Type u`, commutative group scheme `T` and affine
group scheme `G` over `Spec k`, and a monomorphism `i : T.toGrp ⟶ G`. It
assumes the abstract statement `RootPairingWeylCoxeterStatement.{u, 0, u, u}`,
reflection data `D`, that `T` is a split torus, `HasRelativeRootSystem i`, a
generic cocharacter `ν`, and that every representative of `D` centralizes the
kernel of its root. It concludes `HasRelativeWeylCoxeterSystem i ν`.

The proof follows these steps:

1. The relative roots are finite. This is the published
   `HasRelativeRootSystem.finite_relativeRoots` for the split torus.
2. The pairing `D.rootPairing` is crystallographic. This is the published
   `RelativeRootReflectionData.rootPairing_isCrystallographic`.
3. The abstract statement is applied to the index type `relativeRoots i`, the
   field `ℚ`, the rational root span `relativeRootSpan i`, its `ℚ`-dual, the
   pairing `D.rootPairing`, and the linear form
   `RelativeRootSystem.corootFunctional i ν`. The form is nonzero on every root
   because, by the published `RelativeRootSystem.corootFunctional_rootVector`,
   its value on the root vector of `β` is the integer `⟨β, ν⟩` cast to `ℚ`.
   That integer is nonzero because `ν` is generic. This step uses only the
   Coxeter part of the conclusion. The finiteness of the abstract Weyl group
   is not needed, since the assembly theorem proves finiteness of `N(k)/Z(k)`
   by itself.
4. The resulting Coxeter matrix, Coxeter system, simple-reflection identity,
   length formula and descent criterion are passed, together with the other
   hypotheses, to `hasRelativeWeylCoxeterSystem_of_rootPairing`.

## The premise bundle and the reduction

`RelativeWeylCoxeterPremises.{u}` is the `Prop`-valued definition
`RelativeRootSystemStatement.{u} ∧ RelativeRootReflectionExistenceStatement.{u} ∧
RootPairingWeylCoxeterStatement.{u, 0, u, u}`. It names the conjunction of the
three inputs above. It introduces no new mathematical notion.

`relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement` assumes the
three statements as separate hypotheses and proves
`RelativeWeylCoxeterStatement.{u}`. It introduces `k`, `G`, `T`, `i`, `ν`, the
affineness of `G` (from `IsConnectedReductive`) and the monomorphism property
of `i` (from `IsMaximalSplitTorus`), as the target statement does. It then
obtains `D` and the kernel-centralizer property from the reflection existence
statement and `HasRelativeRootSystem i` from the root system statement. Finally
it applies the per-torus step with the split torus given by
`IsMaximalSplitTorus`.

`RelativeWeylCoxeterPremises.relativeWeylCoxeterStatement` is the same
reduction with the hypotheses bundled in `RelativeWeylCoxeterPremises`.

## Status and provenance

None of the three premises is proved here, so this module does not prove
`RelativeWeylCoxeterStatement`. At the time of writing each one has its own
open proof task: `RelativeRootSystemStatement` (task 51ecd216),
`RelativeRootReflectionExistenceStatement` (task 5c031416), and
`RootPairingWeylCoxeterStatement` (task b4659a9e). Once proofs of the three are
in the Library, applying the reduction to them proves the target.

The content is internal. It is a direct composition of published Library
results and introduces no mathematics of its own. The route through the
kernel-centralizer property and the abstract Coxeter theorem is the one used
by the assembly module. The literature sources are cited with exact locations
in the Markdown of `RelativeWeylCoxeterStatement` (Borel–Tits 5.3 and
5.15–5.17; Renard V.3.7 and V.4.6) and of `RootPairingWeylCoxeterStatement`
(Springer, *Linear Algebraic Groups*, Chapter 8; Renard). This file quotes no
source.
