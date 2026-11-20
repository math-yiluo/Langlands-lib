# Frame-normalized cubic embeddings of ordinary polarized data

This module defines two predicates on an ordinary polarized finite-level datum
`a : Datum P S g d n` (module `Data`) over a scheme `S`, for a family
`ρ : Fin (m + 2) → Fin (2*g) → ZMod n` of level coefficient tuples and a morphism
`ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m`. All schemes lie in one universe `u`.
Nothing is proved here.

## `Datum.IsFrameEmbedding a ρ ψ`

A structure of five propositions:

- `toBase`: `ψ` is a morphism over `S` (`ψ ≫ toBase S m = a.abelian.X.hom`);
- `isClosedImmersion`: `ψ` is a closed immersion;
- `cubic`: for some line bundle `N` on `S`, the pullback along `ψ` of the degree-one twist
  `RelativeProjectiveSpace.twistOne S m` (that is, `𝒪(1)`) is isomorphic to
  `a.cubicBundle ⊗ π^* N`, where `π = a.abelian.X.hom` and `⊗` is `LineBundle.tensor` with
  the tensor comparison `P.preservation`;
- `basis`: for `j k : Fin (m + 1)` with `k ≠ j`, the coordinate section `X_k`
  (`RelativeProjectiveSpace.twistOneCoordinate S m k`) vanishes along
  `a.torsionPoint (ρ j.castSucc) ≫ ψ` (`VanishesAlong`: its pullback is zero);
- `unit`: for all `i k : Fin (m + 1)`, the pullbacks of `X_i` and `X_k` along
  `a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ` are equal.

Since the coordinates of a point of projective space generate, `basis` says exactly that
the torsion point with coefficients `ρ j` (for `j ≤ m`) is sent to the `j`-th coordinate
point `[0 : … : 1 : … : 0]`, and `unit` says that the torsion point with coefficients
`ρ (m + 1)` is sent to `[1 : 1 : … : 1]`. Together: `ψ` sends the `m + 2` torsion points
`ρ` to the standard projective frame.

## `Datum.Realizes a ψ I σ`

For an ideal sheaf `I` on `RelativeProjectiveSpace S m` and integral projective points
`σ r : S ⟶ ProjectiveSpace (ULift ℤ) m`, one for each level coefficient tuple `r`:
`ψ.ker = I`, and for every `r`, `a.torsionPoint r ≫ ψ ≫ toIntegral S m = σ r`. For a closed
immersion `ψ`, `I` cuts out the image of the abelian scheme and `σ r` records the image of
the torsion section with coefficients `r`.

## Provenance

Derived from Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), §7.2,
registered source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`:

- Definition 7.5 (printed p.130, PDF p.143): a linear rigidification of a polarized abelian
  scheme `X/S` is an isomorphism `P(π_* L_Δ(ω)^3) ≅ P^m × S`. For the resulting embedding
  `ψ : X ⊂ P^m × S`, relation `(*)` (printed p.131, PDF p.144) reads
  `ψ^* 𝒪(1) ≅ L_Δ(ω)^3 ⊗ π^* M` with `M = e^* ψ^* 𝒪(1)` (since `L_Δ(ω)` is trivial along
  the identity `e`). This is the `isClosedImmersion` and `cubic` part, with the Library's
  `Datum.cubicBundle` (the tensor cube of `(1, λ)^* 𝒫`) in the role of `L_Δ(ω)^3` and the
  existential line bundle `N` in the role of `M`.
- The data `(a)` the embedding and `(b)` the sections (printed p.131) are what `Realizes`
  records: Mumford's `2g + 1` sections are here all torsion sections, indexed by their
  coefficient tuples.
- The frame normalization (`basis`, `unit`) replaces Mumford's quotient by `PGL(m + 1)`:
  a projective frame of torsion points fixes the linear rigidification uniquely. It is the
  slice described in `FrameChartRepresentabilityStatement.md`.

The level conditions are those of the published `Datum.torsionPoint` (module `FrameLocus`).
The predicates are used in `FrameHilbertLocusStatement` and in Task 7811's reduction of
`FrameChartRepresentabilityStatement`.
