/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePresentationModel

/-!

# The separated finite-presentation envelope as an explicit construction

Stacks Project Tags 01ZH and 01ZJ are proved in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` as existence statements. This
file packages the selections made in the blueprint as definitions:

- `AlgebraicGeometry.Scheme.separatedStage`: for a cofiltered system of qcqs schemes over `S`
  with affine transition maps whose limit is separated over `S`, a selected stage from which on
  every model is separated over `S` (blueprint: `theorem-nagata-s-compactification-theorem--1`);
- `AlgebraicGeometry.Scheme.Hom.separatedFPEnvelope`: for a separated morphism `f : X ⟶ S` of
  finite type between qcqs schemes, the model of the finite presentation model system of
  `f` (`AlgebraicGeometry.Scheme.Hom.finitePresentationApproximation`) at the selected separated
  stage, together with the closed immersion
  `AlgebraicGeometry.Scheme.Hom.toSeparatedFPEnvelope` and the structure morphism
  `AlgebraicGeometry.Scheme.Hom.separatedFPEnvelopeHom`
  (blueprint: `theorem-nagata-s-compactification-theorem--1`).

## Main results

- `AlgebraicGeometry.Scheme.isSeparated_app_separatedStage`: every model past the selected stage
  is separated over `S` (blueprint: `theorem-nagata-s-compactification-theorem--1`).
- `AlgebraicGeometry.Scheme.Hom.separatedFPEnvelope_spec`: the constructed envelope is separated
  and of finite presentation over `S`, and `X ⟶ X^fp` is a closed immersion over `S`
  (blueprint: `theorem-nagata-s-compactification-theorem--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section SeparatedStage

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) [∀ i, QuasiCompact (t.app i)]
  (i₀ : I) [IsSeparated (c.π.app i₀ ≫ t.app i₀)]

/-- **The selected separated stage** (blueprint: `theorem-nagata-s-compactification-theorem--1`):
for a cofiltered system `{Dᵢ}` of quasi-compact quasi-separated schemes over `S` with affine
transition maps and quasi-compact structure morphisms whose limit is separated over `S`, a chosen
index `α_sep` from which on every model is separated over `S`. It is selected from the existence
statement `AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit` (Stacks Project Tag 01ZH,
blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def Scheme.separatedStage : I :=
  (Scheme.exists_isSeparated_app_of_isLimit hc t i₀).choose

/-- **The models past the selected stage are separated** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): for every `i ⟶ α_sep`, the model `Dᵢ` is
separated over `S`. -/
theorem Scheme.isSeparated_app_separatedStage {i : I} (g : i ⟶ Scheme.separatedStage hc t i₀) :
    IsSeparated (t.app i) :=
  (Scheme.exists_isSeparated_app_of_isLimit hc t i₀).choose_spec g

instance Scheme.isSeparated_app_separatedStage_self :
    IsSeparated (t.app (Scheme.separatedStage hc t i₀)) :=
  Scheme.isSeparated_app_separatedStage hc t i₀ (𝟙 _)

end SeparatedStage

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f]

variable [IsSeparated f]

/-- The index of the finite presentation model system used to start the separated
stage selection: any index works, and we choose one. -/
noncomputable def finitePresentationApproximationIndex : f.finitePresentationApproximation.I :=
  Classical.choice (IsCofiltered.nonempty (C := f.finitePresentationApproximation.I))

instance isSeparated_π_app_p_app_finitePresentationApproximationIndex :
    IsSeparated ((Cone.mk X f.finitePresentationApproximation.π).π.app
        f.finitePresentationApproximationIndex ≫
      f.finitePresentationApproximation.p.app f.finitePresentationApproximationIndex) := by
  change IsSeparated (f.finitePresentationApproximation.π.app _ ≫
    f.finitePresentationApproximation.p.app _)
  rw [f.finitePresentationApproximation.w]
  infer_instance

/-- The selected separated stage `α_sep^{X/S}` of the finite presentation model system
of `f` (blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def separatedFPEnvelopeIndex : f.finitePresentationApproximation.I :=
  Scheme.separatedStage f.finitePresentationApproximation.isLimit
    f.finitePresentationApproximation.p f.finitePresentationApproximationIndex

/-- **The separated finite-presentation envelope** `X^fp = X_{α_sep}` of a separated morphism of
finite type between quasi-compact quasi-separated schemes: the model of the selected
finite-presentation approximation of `f` at the selected separated stage
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def separatedFPEnvelope : Scheme.{u} :=
  f.finitePresentationApproximation.D.obj f.separatedFPEnvelopeIndex

/-- The closed immersion `i^fp : X ⟶ X^fp` of the separated finite-presentation envelope
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def toSeparatedFPEnvelope : X ⟶ f.separatedFPEnvelope :=
  f.finitePresentationApproximation.π.app f.separatedFPEnvelopeIndex

/-- The structure morphism `X^fp ⟶ S` of the separated finite-presentation envelope
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def separatedFPEnvelopeHom : f.separatedFPEnvelope ⟶ S :=
  f.finitePresentationApproximation.p.app f.separatedFPEnvelopeIndex

/-- **The separated finite-presentation envelope** (Stacks Project Tag 01ZJ, blueprint:
`theorem-nagata-s-compactification-theorem--1`): the constructed morphism `X^fp ⟶ S` is separated,
quasi-compact and locally of finite presentation, and the constructed map `X ⟶ X^fp` is a
closed immersion over `S`. -/
theorem separatedFPEnvelope_spec :
    IsClosedImmersion f.toSeparatedFPEnvelope ∧
      LocallyOfFinitePresentation f.separatedFPEnvelopeHom ∧
      QuasiCompact f.separatedFPEnvelopeHom ∧ IsSeparated f.separatedFPEnvelopeHom ∧
      f.toSeparatedFPEnvelope ≫ f.separatedFPEnvelopeHom = f :=
  ⟨f.finitePresentationApproximation.isClosedImmersion_π _,
    f.finitePresentationApproximation.locallyOfFinitePresentation_p _,
    f.finitePresentationApproximation.quasiCompact_p _,
    Scheme.isSeparated_app_separatedStage_self _ _ _,
    f.finitePresentationApproximation.w _⟩

instance : IsClosedImmersion f.toSeparatedFPEnvelope := f.separatedFPEnvelope_spec.1

instance : LocallyOfFinitePresentation f.separatedFPEnvelopeHom := f.separatedFPEnvelope_spec.2.1

instance : QuasiCompact f.separatedFPEnvelopeHom := f.separatedFPEnvelope_spec.2.2.1

instance : IsSeparated f.separatedFPEnvelopeHom := f.separatedFPEnvelope_spec.2.2.2.1

@[reassoc (attr := simp)]
lemma toSeparatedFPEnvelope_separatedFPEnvelopeHom :
    f.toSeparatedFPEnvelope ≫ f.separatedFPEnvelopeHom = f :=
  f.separatedFPEnvelope_spec.2.2.2.2

end Scheme.Hom

end AlgebraicGeometry
