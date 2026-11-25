# Coordinates of the second kind on a linear Lie group

`Langlands.Geometry.Manifold.LinearLieGroup.ProductCoordinates`. For `h : IsExpLieAlgebra G 𝔤`
(`Basic`) and a basis `b` of `𝔤` indexed by `Fin d`, the coordinates of the second kind
`t ↦ h.prodExp b t = ∏ᵢ exp (tᵢ bᵢ)` (ordered product) are a local diffeomorphism from a neighbourhood
of `0` in `ℝᵈ` onto a neighbourhood of `1` in `G`. Namespace `Langlands.LinearLieGroup`.

## Content

- `prodExpVal X t = ∏ᵢ exp (tᵢ Xᵢ)` in `𝔸`: smooth (`contDiff_prodExpVal`, by induction on `d`),
  `1` at `t = 0`, with derivative `t ↦ ∑ᵢ tᵢ Xᵢ` at `0` (`hasFDerivAt_prodExpVal_zero`).
- `logCoord b w`: the coordinates in the basis `b` of the projection of `log w` to `𝔤`, smooth on
  the domain of the local logarithm; its derivative at `1` is the inverse of `t ↦ ∑ᵢ tᵢ bᵢ`.
- `prodExpCoord b = logCoord b ∘ prodExpVal b`: smooth near `0`, with derivative the identity at
  `0` (`hasFDerivAt_prodExpCoord_zero`).
- `IsExpLieAlgebra.exists_prodExp_coord`: open `S ∋ 0` and `T` and a smooth inverse
  `ψ : T → S` of `prodExpCoord b` (Mathlib's inverse function theorem
  `ContDiffAt.toOpenPartialHomeomorph`, restricted to where the derivative stays invertible and the
  product stays in the neighbourhood `nhdOne` of `1`).
- `IsExpLieAlgebra.prodExp_coord_eq`: for `y ∈ G` near `1` with logarithmic coordinates in `T`,
  `prodExp b (ψ (logCoord b y)) = y`; so `y ↦ ψ (logCoord b y)` inverts the coordinates of the
  second kind on a neighbourhood of `1` in `G`.
- `IsExpLieAlgebra.val_prodExp`, `continuous_prodExp`: `prodExp` seen in `𝔸`, and its continuity.

These coordinates are used in `HaarDensity` (Haar measure near `1`) and in the iteration over a
basis of the Dixmier–Malliavin theorem (`IteratedKernel`, `LinearGroup`).

## Literature

Coordinates of the second kind: J. Dixmier and P. Malliavin, *Factorisations de fonctions et de
vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, proof of Theorem 3.1,
step (1), p. 6: a basis `(x₁, …, x_m)` of `𝔤` for which `(t₁, …, t_m) ↦ (exp t₁x₁) ⋯ (exp t_m x_m)`
is a diffeomorphism of `(-1, 1)^m` onto an open set of `G`, stated there without proof. The page is
that of the English translation *Factorizations of infinitely differentiable functions and smooth
vectors* (typeset in LaTeX, translator not named, paginated 1–24), which does not give the pages of
the original. B. C. Hall, *Lie groups, Lie algebras, and representations*, 2nd edition (Springer GTM
222, 2015), does not treat coordinates of the second kind for a basis; the same inverse function
argument for the two-factor map `X + Y ↦ e^X e^Y` on `𝔤 ⊕ D` is his proof of Theorem 3.42,
pp. 69–70.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean`, lines 11–193 and
203–240, of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. Lines 194–201 of that file are in `Basic`; its lines
242–320 (three analysis lemmas) are replaced or moved: `contDiff_det_pi` by the Library's
`Langlands.Analysis.contDiff_continuousLinearMap_det`, the two others into `HaarDensity`. The
repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.LinearLieGroup`.
- The exponential lemmas lose their field argument (`expPartialHomeomorph 𝔸`, see `Exponential`).
- `contDiff_apply ℝ ℝ i` is written `contDiff_apply ℝ (fun _ => ℝ) i` (changed signature in the
  present Mathlib).
- The file option `linter.unusedSectionVars false` is removed; unused section instances are left
  out with `omit … in`.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
