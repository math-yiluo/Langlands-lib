# The module `Q` of a linear system from a Čech projective representative

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`. Let `π : X ⟶ Spec R`, `M` a module on `X` and `𝒰` an ordered affine cover (FLT port).

- `baseChangePresheaf π M A`: the FLT Čech presheaf of `M_A` on `X_A = X ×_R Spec A`.
- `CechRep π M 𝒰`: the terms `K₀, K₁, K₂` (finite projective `R`-modules) and differentials
  `δ : K₀ → K₁`, `δ₁ : K₁ → K₂` (`δ₁ ∘ δ = 0`) of a Čech projective representative of `M`, with the
  comparison maps `Θ A : A ⊗ K₀ → C⁰(𝒰_A, M_A)` and `Θ₁ A : A ⊗ K₁ → C¹(𝒰_A, M_A)` after every
  base change `R → A`, the explicit formula `Θ_tmul` for `Θ`, and the facts: `Θ` maps `δ`-cocycles
  to Čech cocycles and is bijective onto Čech `0`-cocycles (`Θ_cocycle`, `Θ_inj`, `Θ_surj`), `Θ₁`
  maps `δ₁`-cocycles to Čech `1`-cocycles (`Θ₁_cocycle`), and a `δ₁`-cocycle whose image is a Čech
  coboundary is a `δ`-coboundary (`Θ₁_exact`).
- `nonempty_cechRep`: such data exist when `R` is noetherian, `π` is proper and flat and `M` is
  locally trivial. This is a repackaging of degrees `0, 1, 2` of the Library's
  `Modules.noetherianCechProjectiveRepresentative`
  (`NoetherianCechProjectiveRepresentativeStatement`).
- `CechRep.sectionsEquivH0`, `kerEquivH0`: global sections of `M_A` are the Čech `0`-cocycles
  (FLT `AC3Aux.toH0`), which are the `δ`-cocycles of `A ⊗ K₀`.
- `CechRep.Q := CokernelDualHom.Q δ` and `CechRep.homEquivSections A : (Q →ₗ[R] A) ≃ Γ(M_A, ⊤)`.

## Source

Kleiman, *The Picard scheme* (arXiv math/0504020v1), Subsection 3.10 (p.24): the module `Q` with
`Hom(Q, N) ≅ f_*(F ⊗ f^*N)` (3.10.1), from EGA III 7.7.6, compatible with base change (EGA III
7.7.9). Here it is built from a perfect Čech model and stated for algebras `N = A`.
