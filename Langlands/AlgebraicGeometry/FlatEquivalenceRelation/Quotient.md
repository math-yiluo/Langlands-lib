# The quotient by a flat proper equivalence relation, inside the Hilbert scheme

Helper module of the proof of
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement` (entry
module `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`).
It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.FlatEquivalenceRelation`, with the notation of
`FlatEquivalenceRelation.Classifier` and `FlatEquivalenceRelation.OpenLocus`. The section
assumes the following. `C : Classifier f` with `f : X ⟶ S` proper and `C.πH` separated. The
morphism `i : Z ⟶ X` is an immersion with `i ≫ f = p`. The family `R ⟶ X ×_S Z` is a closed
immersion. `Rel s t` is an equivalence relation on `T`-points for all `T` (`hEq`), and
`φ : Z ⟶ H` classifies the family (`hW`). Several results also need `p` quasi-compact. Put
`H'' = C.locus i.coborderRange` and `D'' = C.Dl i.coborderRange`.

- `φq : Z ⟶ H''` and `Γq : Z ⟶ D''` are the classifying morphism and its graph over the open
  locus. `Γq` is a closed immersion (instance, from `isClosedImmersion_graphl`).
  `quasiCompact_φq`: `φq` is quasi-compact when `p` is.
- `Q` is the scheme-theoretic image of `φq` (Mathlib's `Scheme.Hom.image`). `π : Z ⟶ Q` is the
  induced morphism (`toImage`), and `ιQ : Q ⟶ H''` is the closed immersion `imageι`.
- `ker_pullback_snd`: the kernel of `Z ×_{H''} D'' ⟶ D''` equals the kernel of `Γq`. The graph
  gives a section `Z ⟶ Z ×_{H''} D''`, which proves one inequality. For the other, every point of
  `Z ×_{H''} D''` factors through `Γq` by `exists_factor`.
- `isPullback_Γq_π`: **`Z = D'' ×_{H''} Q`**, that is, the square formed by `Γq`, `π`, the
  universal family `D'' ⟶ H''` and `ιQ` is a pullback. Mathlib's
  `isPullback_of_isClosedImmersion` reduces this to an equality of ideal sheaves on `D''`: the
  pullback of the kernel of `φq` along the flat `D'' ⟶ H''` must equal the kernel of `Γq`.
  `KernelFlatBaseChange.ker_comap_of_flat` identifies the left side with the kernel of
  `Z ×_{H''} D'' ⟶ D''`, and `ker_pullback_snd` finishes.
- `flat_π`, `isProper_π`, `locallyOfFinitePresentation_π`: `π` is flat, proper and locally of
  finite presentation, as a base change of `D'' ⟶ H''`.
- `surjective_π`: `π` is surjective. The proof is instance search: `π = φq.toImage` is
  dominant because `φq` is quasi-compact (Mathlib's `IsDominant` instance for `toImage`), it is
  universally closed because it is proper (`isProper_π`), and Mathlib's
  `Surjective.of_universallyClosed_of_isDominant` gives surjectivity: the range is closed and
  dense.
- `π_ι_ι`: `π ≫ ιQ ≫ H''.ι = φ`.
- `comp_π_eq_iff`: `x ≫ π = y ≫ π ↔ Rel s t x y`, from `rel_iff`, since `ιQ ≫ H''.ι` is a
  monomorphism.
- `isPullback_s_t`: **`R = Z ×_Q Z`**, that is, `IsPullback s t π π`, when
  `pullback.lift s t h` is a monomorphism. The lift of a cone is chosen by `comp_π_eq_iff`, and
  it is unique because `R ⟶ Z ×_S Z` is a monomorphism.

## Provenance

This is steps (ii) and (iii) of the proof of Nitsure, *Construction of Hilbert and Quot
schemes* (`nitsure-2005-hilbert-quot-arxiv-math0504590v1`), Theorem 6.8 (pp.34–35), with one
change of route. Nitsure obtains `Q` from fpqc descent of the closed subscheme `Γφ ⊆ D` along
`D ⟶ H` (his Lemma 6.7(2)). Here `Q` is defined as the scheme-theoretic image of `φ`, and flat
base change of kernels gives the cartesian square. Nitsure's identity `ϕ = (Q ↪ H) ∘ q` is
`π_ι_ι`.
