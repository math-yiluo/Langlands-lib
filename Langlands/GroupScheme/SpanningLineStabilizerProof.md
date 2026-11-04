# Proof of the spanning representation reduction preserving a line stabilizer

Author: Worker 1038.

The theorem `Langlands.GroupScheme.spanningLineStabilizer` proves
`Langlands.GroupScheme.SpanningLineStabilizerStatement.{u}`, stated in the
unchanged Library module `Langlands.GroupScheme.SpanningLineStabilizerStatement`,
at an arbitrary universe `u`. It adds no hypothesis: `G` need not be connected
or reductive. The statement's affineness instance `IsAffineHom G.X.hom` is
accepted but not used.

## What is proved

Let `k` be an algebraically closed field in universe `u`. Let `G` be a group
scheme over `Spec k` whose structure morphism is smooth and affine, and let
`ρ : MatrixRepresentation G (Fin (n + 1))` be a representation with a
distinguished coordinate `j`. The theorem supplies `n'`, a coordinate
`j' : Fin (n' + 1)` and `ρ' : MatrixRepresentation G (Fin (n' + 1))` such that:

1. for every test `Z : Over (Spec k)` and every point `x : Z ⟶ G.X`, there is
   a unit `c` of `Γ(Z.left, ⊤)` with `ρ'(x) e_j' = c • e_j'` if and only if
   there is a unit `c` of `Γ(Z.left, ⊤)` with `ρ(x) e_j = c • e_j`;
2. the `k`-span of the vectors `ρ'.rationalMatrix g *ᵥ e_j'`, for `g` ranging
   over the rational sections `Over.mk (𝟙 (Spec k)) ⟶ G.X`, is all of
   `Fin (n' + 1) → k`.

## The proof

The Lean proof introduces the data of the statement and applies the published
theorem `MatrixRepresentation.exists_spanning_sameCoordinateLineStabilizer`
(module `Langlands.GroupScheme.MatrixRepresentation.SpanningOrbitCoordinates`)
to `ρ` and `j`. That theorem needs `[IsAlgClosed k]` and `[Smooth G.X.hom]`,
both supplied by the statement. It returns `d`, `s : Fin (d + 1)` and
`σ : MatrixRepresentation G (Fin (d + 1))` with two properties:

- `SameCoordinateLineStabilizer ρ j σ s`. This definition is, by unfolding, the
  required equivalence of item 1 with `n' := d`, `j' := s` and `ρ' := σ`. The
  new representation is on the left in both, and both use units of the same
  ring `Γ(Z.left, ⊤)`.
- The spanning property of item 2, in exactly the form of the statement.

The tuple `⟨d, s, σ, hsame, hspan⟩` therefore proves the statement. No
conversion is needed: `SameCoordinateLineStabilizer` is a `def`, and Lean
unfolds it when it checks the anonymous constructor against the statement's
conjunction.

## The construction behind the cited theorem

The published module builds `σ` as the task context suggests. This section
describes those Library proofs; the present file does not reprove them.

- Smoothness over the field gives that `G.X.left` is reduced
  (`SmoothReducedProof.isReduced_of_smooth_over_field`). Smoothness also gives
  local finite type, by a Mathlib instance.
- `MatrixRepresentation.exists_rationalOrbit_coordinates` (module
  `MatrixRepresentation.OrbitCoordinates`) takes the `k`-span `W` of the
  vectors `ρ(g) e_j` for rational points `g`. The identity point puts the
  nonzero vector `e_j` in `W`. The theorem then selects split coordinates:
  an inclusion `B : Matrix (Fin (n + 1)) (Fin d) k` and a retraction
  `C : Matrix (Fin d) (Fin (n + 1)) k` with `C * B = 1`. Every column of `B`
  is some `ρ(g) e_j`, and some column `s` of `B` is `e_j`. It proves
  `ρ.IsStableCoordinates B C`, which is stability on every scheme test. Its
  proof first checks stability at rational points. It then upgrades this to
  all tests with `isStableCoordinates_of_rationalMatrix`, using reducedness
  and local finite type.
- `σ` is `restrictCoordinates ρ B C hCB hstable`, the restriction of `ρ` to
  these coordinates. Because column `s` exists, `d ≥ 1`, so `d` is rewritten
  as `d' + 1`.
- The stabilizer equivalence
  (`sameCoordinateLineStabilizer_restrictCoordinates`) holds on every test
  `Z`. Pushing `B` and `C` to `Γ(Z.left, ⊤)` gives `B_Z e_s = e_j` and
  `C_Z e_j = e_s`. The intertwining identity
  `restrictCoordinates_intertwines`, `ρ(x) B_Z = B_Z σ(x)`, together with
  `σ(x) = C_Z ρ(x) B_Z`, transfers `c • e_s` to `c • e_j` and back, with the
  same unit `c`.
- The spanning property (`span_restrictCoordinates_orbit_eq_top`) holds
  because each basis vector `e_t` is a rational orbit vector. If column `t` of
  `B` is `ρ(g) e_j`, then `σ(g) e_s = C ρ(g) B e_s = C ρ(g) e_j = C B e_t = e_t`.

## Checks

`lean_check` (diagnostic `708d2734-f341-4421-867b-c4210a1afcc4`): lake build
with zero errors and zero warnings. The theorem has level parameter `u` and
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The file proves only this reduction. It changes no Library file and claims
nothing about invariant affine covers, dual-line covering or flag theorems.
