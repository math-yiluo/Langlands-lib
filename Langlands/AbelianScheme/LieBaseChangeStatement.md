# Canonical Lie base change for abelian schemes

For an arbitrary scheme `S`,
`Langlands.AbelianScheme.LieBaseChangeStatement S` states that the
relative Lie module of every actual abelian scheme over `S` commutes
with arbitrary base change, with the isomorphism identified by the
canonical cotangent and dual pullback maps. It is a Prop-valued
definition; this file does not prove the proposition.

## Exact statement

All schemes lie in a common universe. For every scheme `T`, every
scheme morphism `b : T ⟶ S`, and every `A : Langlands.AbelianScheme S`,
write `A_T = (Langlands.AbelianScheme.baseChange b).obj A`,
`C = Langlands.GroupScheme.cotangentAtIdentity A.toGrp`, and
`C_T = Langlands.GroupScheme.cotangentAtIdentity A_T.toGrp`.
These are the actual base-changed abelian scheme and the cotangent
module sheaves at the identity. By definition,
`A.Lie = dual C` and `A_T.Lie = dual C_T`, where the dual is the
internal module-sheaf Hom into the structure sheaf.

The proposition is the conjunction of the following conclusions:

1. The constructed morphism
   `c = Langlands.GroupScheme.cotangentBaseChangeMap b A.toGrp`,
   with source `b* C` and target `C_T`, is invertible.
2. There is an isomorphism of actual `O_T`-module sheaves
   `ell : b* A.Lie ≅ A_T.Lie` satisfying
   `ell.hom ≫ Langlands.Scheme.Modules.dualMap c =
   Langlands.Scheme.Modules.dualPullbackComparison b C`.

The dual of `c` has source `dual C_T = A_T.Lie` and target `dual (b* C)`.
Thus both sides of the equation have source `b* A.Lie` and target
`dual (b* C)`. The right side is the actual canonical comparison
from pullback of the dual to the dual of the pullback, with explicit
inputs only `b` and `C`. The statement assumes neither a comparison
map nor laws for an unspecified map.

The equation identifies the desired isomorphism with the canonical
Lie comparison: once `c` is invertible, its dual is invertible, and
the forward map of `ell` is the dual pullback comparison followed
by the inverse of `dualMap c`. It also determines that forward map
uniquely. No inverse is used in the statement before its invertibility
is established.

The actual `AbelianScheme` bundle includes smoothness, properness,
geometrically connected fibres, and commutative group operations.
No extra hypothesis is imposed on `S`, `T`, or `b`; in particular
`b` need not be flat. No chosen global relative dimension is required.

## Sources and derivation

Conrad, Gabber, and Prasad, *Pseudo-reductive Groups*, second edition
(2015), Section 2.1, printed page 52 (PDF page 78), define the cotangent
module along the identity and its linear-dual tangent module. Their
map (2.1.3) is the natural tangent base-change map. They state it is
invertible for a group scheme locally of finite presentation when
either the base extension is flat or the identity cotangent module
is flat; they explicitly include smooth group schemes. This is
registered source `conrad-gabber-prasad-2015-pseudo-reductive`,
content SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The passage is stated over rings. The present target is its sheaf
form for abelian schemes over arbitrary schemes: smoothness gives
a finite locally free cotangent module along the identity, and on
an open set trivializing that module the dual pullback comparison
is the usual finite-free dual base-change map. These canonical
local identifications agree on overlaps. Establishing this argument
for the actual project constructions is a future proof obligation,
not a theorem proved in this statement file.

Stacks Project Lemma 29.33.8 (tag 01UV) constructs the canonical
relative-differential map. Lemma 29.33.10 (tag 01V0) asserts that
this map is invertible for an arbitrary scheme base-change square.
Lemma 29.33.16 (tag 0474) identifies the cotangent module along a
section with the section pullback of the relative differentials.
All three occur in `01UM.html` in registered source
`stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
Pulling back the differential comparison along the new identity
section and applying pullback-composition coherence gives precisely
the map `c` in the statement. Its invertibility is the abelian-scheme
specialization of `Langlands.GroupScheme.CotangentBaseChangeIsIsoStatement`.

For the dual comparison, Stacks Lemma 17.22.5 (tag 0C6I) in
`01CM.html` of the same registered source requires a finitely
presented first module and a flat morphism of ringed spaces. It
does not by itself justify the arbitrary base morphism here.
The smooth case uses the finite locally free cotangent module,
as in the preceding CGP passage. The target makes no assertion
that the dual of an arbitrary module commutes with arbitrary
pullback, or that unrestricted nonsmooth group schemes have
invertible Lie comparisons.

The conjunction and its canonical-map equation are a derived
formulation using the project's actual `Lie`, `LieBaseChange`,
and `ModuleDualPullback` constructions. No new definition of an
abelian scheme, differential, cotangent module, or Lie module is
introduced here. A proof of this exact target remains separate.
