# Actual quadratic unitary coordinates and the full centralizer action for type R2 roots

Author: Worker 1045.

`QuasiSplitR2RootUnitaryCoordinatesStatement` is an unproved existence
proposition for the type R2 structural prerequisite of the apartment
construction. It is the multipliable-root counterpart of the Library's
`QuasiSplitR1RootFieldCoordinatesStatement`, with the same quantifier structure.
It applies to every field `k : Type u`, every actual affine quasi-split connected
reductive group `G` (`IsAffineHom G.X.hom` and `IsQuasiSplit G`), and every
prescribed actual maximal split torus inclusion `i : S → G`
(`IsMaximalSplitTorus i`). There is no valuation, topology, henselianity,
characteristic, residue-field, rank or split-group restriction.

The root `a : characterLattice S` is required to satisfy `a ∈ relativeRoots i`
and `2 • a ∈ relativeRoots i`, using the Library's actual relative roots. So
`a` is multipliable, which is type R2 in the source's classification, and
`2 • a` is the divisible type R3 root above it. Roots of type R1 are outside
this proposition.

For every actual group-scheme representative `j : Z → G` of the full all-test
torus centralizer (`(torusCentralizer i).IsRepresentedBy j`) and every factor
`s : S → Z` with `s ≫ j = i`, the proposition requires a
`RootUnitaryCoordinates i j s a`. This structure is defined in the Library
module `Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility` and
consists of:

- fields `E` and `L`, with `L / E` a separable quadratic extension, a scalar
  tower `k → E → L`, and `L` finite-dimensional and separable over `k`;
- a group isomorphism
  `e : SU3Root.rationalParameters E L ≃* rootGroupPoints i a` from the
  quadratic unitary parameter group to the existing actual rational root group
  `U_a(k)`. The parameter group is `{(u, v) ∈ L × L | v + v̄ = u ū}`, with
  product `(u, v) · (u', v') = (u + u', v + v' + u ū')`, where the bar is the
  nontrivial automorphism of `L / E`;
- the condition that a point of `G(k)` lies in `rootGroupPoints i (2 • a)` if
  and only if it is `e(p)` for a parameter `p` with first coordinate `0`;
- an actual rational character `β` of the base change `Z_L`, whose restriction
  along `s_L` is exactly the base change of the root character `a`, as an
  equality of scheme characters;
- for every `z ∈ Z(k)` and every parameter `p`, the identity

  ```text
  j(z) · e(p) · j(z)⁻¹ = e(scale (β(z_L)) p)
  ```

  in the ambient rational-point group `G(k)`. Here `z_L` is the existing actual
  rational scalar extension of `z`, `β(z_L)` lies in `Lˣ`, and
  `scale λ (u, v) = (λ u, λ λ̄ v)`.

The fields, their algebra structures, the isomorphism and the character are
outputs. A centralizer datum, character-evaluation bijectivity, coordinates, an
action identity or a valuation is not an extra premise. The statement is
universal in the supplied actual centralizer presentation, so a consumer can use
any constructed representative and factor.

## Source

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023)
(source `kaletha-prasad-2023-bruhat-tits-new-approach`).

Section 2.6, Notation 2.6.11 and the paragraphs after it, printed pp.96–97
(PDF127–128), treat a quasi-split connected reductive group with a maximally
split maximal torus `T`, the centralizer of `S`. For a pair `a, 2a` of relative
roots, choose an absolute root `ã` over `a` and let `ã'` be the unique other
absolute root over `a` not orthogonal to `ã`; then `b̃ = ã + ã'` is a root over
`2a`. The extension `F_ã / F_b̃` of fields of definition is Galois of degree 2,
its automorphism being the element of the Galois group switching `ã` and `ã'`.
The product `U[ã] = U_ã · U_ã' · U_b̃` is an `F_b̃`-group, non-canonically
isomorphic to the group `U_{F_ã/F_b̃}` of (2.7.2), and (2.6.2) is the
isomorphism `R_{F_b̃/F} U[ã] → U_a`. On rational points this gives the
isomorphism `e` above, with `E = F_b̃` and `L = F_ã`, both finite separable
over the base field.

Section 2.7, printed pp.108–110 (PDF139–141), works this out for `SU3`. It
defines `U_{ℓ/k}` in (2.7.2) with the product displayed above, which is the
Library law. It shows that `U_{2a}` is the subgroup of parameters `(0, v)`, and
Fact 2.7.1 shows that this subgroup is central. Construction 2.9.16 (isomorphisms
(2.9.3), printed p.117, PDF148) gives the same identification for quasi-split
semisimple simply connected groups compatibly with a Chevalley–Steinberg system.
There `U_{2a}` corresponds to `R_{k_b/k} U⁰_{k_a/k_b}`.

The source does not display the centralizer identity in this form. It follows
from the construction, and the statement records it as a consequence. An
isomorphism `U[ã] ≅ U_{F_ã/F_b̃}` is built from a coordinate `x_ã` of `U_ã`
over `F_ã`, its Galois conjugate `x_ã'`, and `U_b̃`. Since `T` normalizes each
absolute root group, `t ∈ T(F)` multiplies the `ã`-coordinate by
`λ = ã(t) ∈ F_ã^×` and the `ã'`-coordinate by `ã'(t) = λ̄`. It multiplies the
`b̃`-coordinate by `b̃(t) = λ λ̄`. Because the map (2.6.2) is the product of
Galois conjugates, it is equivariant for `T(F)`. The character `ã` is defined
over `F_ã` and restricts to `a` on `S`, so it serves as `β`, and `Z = T` in the
quasi-split case. For `SU3`, the defining condition `g = Ad(J) ḡ⁻ᵗ` of p.108
gives `T(k) = {diag(t, t̄/t, 1/t̄) | t ∈ ℓ^×}`. Conjugating the matrices
`u_a(u, v)` of p.110 by such an element gives `u ↦ (t²/t̄) u` and
`v ↦ t t̄ v`, which is `scale λ` with `λ = t²/t̄`. As in the R1 statement, only
this rational-point consequence is asserted, not the scheme-level
isomorphism (2.6.2).

The 2024 corrections (source `kaletha-prasad-2024-corrections`, PDF25) amend
§2.6 only in 2.6(d) and Definitions 2.6.20 and 2.6.23. They do not change the
type R2 description used here.

## Scope

Construction 6.1.17, printed pp.205–206 (PDF236–237), composes the inverse of
these coordinates with the valuation of `F_ã` to define the root functions at
`a` and `2a`. The Library module `RootUnitaryCoordinateCompatibility` proves
that root functions so defined satisfy the whole-centralizer axiom V6 at `a` and
`2a`. This proposition supplies neither a proof of its existence conclusion nor
a compatible Chevalley–Steinberg system, the axioms V0–V5, the type R1
coordinates, the normalizer-stable equipollence class, centralizer
character-evaluation bijectivity, or apartment existence. Those remain separate
obligations of `QuasiSplitIntegerApartmentExistenceStatement`.
