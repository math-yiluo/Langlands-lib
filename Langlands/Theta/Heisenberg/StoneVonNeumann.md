# The Stone–von Neumann theorem over a nonarchimedean local field

**GKT §1.3** (Theorem 1.31, the smooth Stone–von Neumann theorem, p. 36), without its last clause
(the representation is unitarizable, Lemma 1.30); with Schur's lemma for the isomorphism.

The module `Langlands.Theta.Heisenberg.StoneVonNeumann` proves that the Heisenberg group of a
non-degenerate alternating form over a nonarchimedean local field has, up to isomorphism, exactly
one smooth irreducible complex representation with a given non-trivial central character, and
that the isomorphism is unique up to a scalar.

## Content

Let `F` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`, any
characteristic) with `[Invertible (2 : F)]`, `W` a finite-dimensional `F`-vector space with its
module topology, `B` a non-degenerate alternating form on `W`, and `ψ : AddChar F ℂ` continuous and
non-trivial.

```text
theorem Langlands.HeisenbergGroup.exists_isIrreducible_isSmooth (hB : B.IsAlt)
    (hn : B.Nondegenerate) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module ℂ S)
      (ρ : Representation ℂ (HeisenbergGroup B) S),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧ HasCentralCharacter ρ ψ

theorem Langlands.HeisenbergGroup.nonempty_equiv (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {S S'} …
    (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : HasCentralCharacter ρ ψ)
    (hρ' : IsSmooth ρ') (hi' : ρ'.IsIrreducible) (hc' : HasCentralCharacter ρ' ψ) :
    Nonempty (ρ.Equiv ρ')

theorem Langlands.HeisenbergGroup.equiv_eq_smul (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (e e' : ρ.Equiv ρ') : ∃ c : ℂ, ∀ v, e' v = c • e v
```

`IsSmooth` is the Library's `Langlands.IsSmooth` (each vector is fixed by an open subgroup),
`HasCentralCharacter ρ ψ` says that `(0, t)` acts by `ψ t` (`Theta/Heisenberg/Representation`). The
model of the first theorem is the induced model of a self-dual datum
(`Theta/Heisenberg/InducedModel`), in the universe of `W`; the representations of the second and
third theorems are in arbitrary universes.

Existence: the induced model of a self-dual datum. Uniqueness: choose a self-dual datum
`(A, α)`; `ρ` and `ρ'` contain non-zero `α`-eigenvectors `e`, `e'` of `A`; the span `P` of the
translates of `(e, e')` in `ρ × ρ'` is irreducible; the two projections `P → ρ`, `P → ρ'` are
non-zero intertwining maps between irreducible representations, hence bijective (Schur), and
`ρ ≅ P ≅ ρ'`. Uniqueness of the isomorphism: `e⁻¹ ∘ e'` is an endomorphism of the smooth
irreducible `ρ`, hence a scalar, by the Library's Schur lemma for representations of σ-compact
totally disconnected locally compact groups
(`Langlands.Renard.Smooth.sigmaCompactSchur`; D. Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, III.1.8, p. 62).

For that lemma the Heisenberg group over a local field is a Hausdorff, locally compact, totally
disconnected and σ-compact topological group: instances `T2Space`, `LocallyCompactSpace`,
`TotallyDisconnectedSpace`, `SigmaCompactSpace` for `HeisenbergGroup B`, through
`HeisenbergGroup B ≃ₜ W × F` and `W ≃ₜ F^n`. The field is totally disconnected because it is a
nonarchimedean group (instance in `HarmonicAnalysis/AdditiveCharacterExists`), and σ-compact because
its topology is that of a proper normed field (a private lemma; the same argument is the Library's
`Langlands.HarmonicAnalysis.GeneralLocalField.sigmaCompactSpace`, whose module imports much more).

Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps p-adique* (Lecture Notes in
Math. 1291, Springer 1987), chapter 2, I.2, Théorème (Stone, von Neumann), p. 28 (existence I.3,
pp. 28–30; uniqueness I.5, pp. 30–31); A. Weil, *Sur certains groupes d'opérateurs unitaires*,
Acta Math. 111 (1964), chapter I, n° 4, p. 149 (the operators `U(w)` on `L²(G)` and the group
`A(G)`, an extension of `G × G*` by `T`) and n° 10, Théorème 1, p. 157 (the centralizer of `A(G)` in
the automorphisms of `L²(G)` is its centre `T`). Weil works with the unitary representation on
`L²(G)` of a locally compact abelian group `G` and does not state the uniqueness.

## Source and licence

Lines 652–678 (`StoneVonNeumann_holds`) of
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`. The repository
has no licence file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The `Prop` `StoneVonNeumann` and its proof `StoneVonNeumann_holds` are replaced by the two
  theorems `exists_isIrreducible_isSmooth` and `nonempty_equiv`; the source's `IsIrrSmoothOf` is
  dissolved into `IsSmooth`, `Representation.IsIrreducible` and `HasCentralCharacter`; its
  `PRep.IsSmooth` is replaced by the Library's `IsSmooth`.
- `(2 : F) ≠ 0` → `[Invertible (2 : F)]`; universes arbitrary (the source: `Type`).
- New: the four topological instances and `equiv_eq_smul`.
- Not taken: `planeForm`, `planeForm_isAlt`, `planeForm_nondegenerate`, `plane_model` (lines
  717–733: the case `W = F²`, an application).

## Declarations

- `instance : T2Space (HeisenbergGroup B)`, `LocallyCompactSpace`, `TotallyDisconnectedSpace`,
  `SigmaCompactSpace`.
- `exists_isIrreducible_isSmooth`, `nonempty_equiv`, `equiv_eq_smul`.

## Dependencies

`Langlands.Theta.Heisenberg.InducedModel`,
`Langlands.Representation.Smooth.RenardSigmaCompactSchurProof` (Schur's lemma); Mathlib:
`Topology.Algebra.Nonarchimedean.TotallyDisconnected`, `Topology.Algebra.Valued.LocallyCompact`.
