# Proof of the fibrewise criterion for equalizers of smooth algebras

Authors: Worker 299 and Worker 424. Worker 299 authored the proof;
Worker 424 adapted its module dependencies for separate prerequisite
publication and rechecked the complete proof.

`Langlands.Algebra.smoothEqualizerFibreCriterion.{u}` proves the published
proposition `Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}` in an
arbitrary universe `u`. The statement module and its Markdown are imported
unchanged. The theorem introduces the rings `A`, `C₀`, `C₁`, their
structures, the maps `δ₁`, `δ₂`, the smoothness and faithful-flatness
hypotheses, the residue-field hypothesis and the element `c` with
`δ₁ c = δ₂ c`, and applies
`Langlands.Algebra.CechEqualizer.mem_range_of_smooth`. The explicit
hypotheses `Algebra.Smooth A C₀`, `Algebra.Smooth A C₁` and
`Module.FaithfullyFlat A C₀` become local instances there; no hypothesis is
added.

The proof of `mem_range_of_smooth` is in the helper modules:

- `Langlands.Algebra.CechEqualizer.Good`: "good" modules (those `M` for which
  the kernel of `M ⊗ (δ₁ - δ₂)` consists of the elements `m ⊗ 1`), their
  closure under extensions, submodules, finitely generated exhaustion and
  flat base change, and the noetherian core: over a noetherian ring, a
  module is good when the residue fields of its associated primes are good
  (via Lasker's primary decomposition).
- `Langlands.Algebra.CechEqualizer.Model`: associated primes of an algebra
  over a noetherian ring are contractions of primes, residue fields of `A`
  are good by the fibre hypothesis, and hence the criterion holds for a pair
  that is the base change of a faithfully flat/flat model over a noetherian
  subring.
- `Langlands.Algebra.CechEqualizer.Descent`: faithful flatness of a base
  change from an open-image condition, and descent of algebra maps to a
  model.
- `Langlands.Algebra.CechEqualizer.Criterion`: noetherian approximation using
  Mathlib's `Algebra.Smooth.exists_subalgebra_fg` and Chevalley's openness
  theorem for flat finitely presented maps, then the model criterion.

The overall route is the proof sketch recorded in the statement task and
the statement's Markdown: a noetherian module-theoretic argument followed by
finite-presentation approximation. It is an internal derivation, not a
formalization of the perfect-complex proof of Stacks Lemma 36.32.5
(Tag 0E62). The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.
