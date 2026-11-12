# Reduction of quasi-affine-source AF representability to Noetherian scheme sources

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFNoetherianSchemeApproximationProof`.

## Statement

`quasiAffineSourceAFNoetherianSchemeApproximation` proves
`QuasiAffineSourceAFNoetherianSchemeApproximationStatement.{u}`, the implication

`NoetherianSchemeQuasiAffineSourceAFStatement.{u} → FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`.

Assume the AF representability of a quasi-compact quasi-separated algebraic space `Y`, over any
base scheme, that has a finite surjection from a quasi-affine Noetherian scheme. Then the
same holds over `Spec R`, for every commutative ring `R`, with no Noetherian hypothesis on
the quasi-affine source.

This is Gross, Proposition 3.5, Step 3: "By approximating `X` and `p`, we may assume that `X`
is of finite type over `Z`." The Lean proof does not approximate the algebraic space `Y`
itself. It approximates an étale presentation of the finite cover. This avoids transporting
spaces between `Spec R` and an absolute base.

## Proof

The theorem is `approximation_of_interfaces presentationInterface approximationInterface
quotientInterface`. The four modules of `QuasiAffineApproximation` supply its parts:

- `Skeleton` (Worker 5045) states the three interfaces. It proves
  `approximation_of_interfaces`: the three interfaces together imply the statement. Fix
  `f : U ⟶ Y` over `Spec R`.
  1. Part I presents `f` by a cartesian morphism `(φ, g) : E' ⟶ E` of étale equivalence
     relations and a flat, finitely presented, surjective `q : E'.U ⟶ U`.
  2. Part II approximates this by a Noetherian level `(φ₁, g₁) : E₁' ⟶ E₁` with quotient
     `q₁ : E₁'.U ⟶ M₁` and affine `hM : U ⟶ M₁`.
  3. Part III produces an AF scheme `P` and an affine `ψ : M₁ ⟶ P` with
     `q₁ ≫ ψ = φ₁ ≫ ψV`.
  4. The composite `hM ≫ ψ : U ⟶ P` is affine. It takes equal values on any two points of `U`
     with the same image in `Y`: lift them to `E'.U` by Part I and use the commuting squares.
     So the preimages of affine neighbourhoods in `P` are saturated affine neighbourhoods. The
     published `exists_AF_representation_of_saturated_affine_opens` then represents `Y` by an
     AF scheme.
- `Presentation` (Part I, `presentationInterface`): an affine étale atlas `U₀ ⟶ Y`, its kernel
  pair `E`, and the fibre product `U₀ ×_Y U` with the kernel pair `E'` of its projection to
  `U`.
- `Approximation` (Part II, `approximationInterface`). The cover `E' ⟶ E` is written as a limit
  of stable finitely generated levels over an affine first level of finite type over `ℤ`.
  The quasi-affine quotient `U` of `E'` descends to a quasi-affine quotient at some level
  (Stacks Tag 07RN). A finite surjective level pair through that level is then chosen. The
  quotient `M₁` at that level is quasi-affine and of finite type over `ℤ`, hence Noetherian.
- `QuotientSpace` (Part III, `quotientInterface`, Worker 5045). All schemes of the Noetherian
  configuration are regarded as schemes over the terminal affine scheme `Spec (ULift ℤ)`.
  There, the quotient algebraic space of `E₁` receives a finite surjection from the
  Noetherian quasi-affine `M₁`, induced by `φ₁`. The hypothesis
  `NoetherianSchemeQuasiAffineSourceAFStatement` applies to this surjection.
- `SeparatedQuotient` (Worker 5045): the relation `E` is closed in `E.U × E.U` when its finite
  cover has a separated quotient. Part II needs this for the first level.

Each module's Markdown describes its proof in detail.
