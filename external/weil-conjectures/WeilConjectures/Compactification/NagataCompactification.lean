/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Constructions
public import WeilConjectures.Compactification.FinitePresentation

/-!

# Main Statements of Nagata Compactification

This file assembles **Nagata's compactification theorem** in its final form
(`AlgebraicGeometry.NagataCompactification`): a separated, quasi-compact morphism `f : X ⟶ Y`
locally of finite type over a quasi-compact quasi-separated base factors as an open immersion
followed by a proper morphism.

The assembly has three steps. The morphism `f` is only locally of finite *type*, while
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` needs finite
*presentation*; the bridge is the finite-presentation envelope `f.fpEnvelope` (Stacks Tag 01ZJ,
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation`),
which writes `f` as a closed immersion `X ⟶ f.fpEnvelope` followed by a separated,
quasi-compact morphism `f.fpEnvelope ⟶ Y` of finite presentation. Compactifying the latter and
cutting back to the closed subscheme `X` with
`AlgebraicGeometry.Compactification.ofIsClosedImmersion` gives the constructed
compactification `AlgebraicGeometry.constructedCompactification` of `f`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.fpEnvelope`: the finite-presentation envelope of `f`, with
  `AlgebraicGeometry.Scheme.Hom.toFpEnvelope` and `AlgebraicGeometry.Scheme.Hom.fpEnvelopeHom`;
- `AlgebraicGeometry.constructedCompactification`: the compactification of `f` obtained from
  a compactification of the envelope by taking the scheme-theoretic image of `X`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.fpEnvelope_spec`: the properties of the envelope;
- `AlgebraicGeometry.isProper_constructedCompactification_g`,
  `AlgebraicGeometry.isOpenImmersion_constructedCompactification_i` and
  `AlgebraicGeometry.constructedCompactification_i_g`: the constructed factorization is a
  compactification;
- `AlgebraicGeometry.NagataCompactification`: the compactification of a separated,
  quasi-compact morphism locally of finite type over a quasi-compact quasi-separated base.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The finite-presentation envelope -/

namespace Scheme.Hom

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- The finite-presentation envelope exists (Stacks Tag 01ZJ); this is the existence statement
behind `AlgebraicGeometry.Scheme.Hom.fpEnvelope`. -/
lemma exists_fpEnvelope :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ Y), IsClosedImmersion i ∧
      LocallyOfFinitePresentation f' ∧ QuasiCompact f' ∧ IsSeparated f' ∧ i ≫ f' = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation

/-- **The finite-presentation envelope** of a separated, quasi-compact morphism `f : X ⟶ Y`
locally of finite type over a quasi-compact quasi-separated base (blueprint:
`theorem-nagata-s-compactification-theorem--1`): a chosen scheme `X'` together with a closed
immersion `f.toFpEnvelope : X ⟶ X'` and a separated, quasi-compact morphism
`f.fpEnvelopeHom : X' ⟶ Y` of finite presentation through which `f` factors (Stacks Tag 01ZJ). -/
noncomputable def fpEnvelope : Scheme.{u} :=
  (exists_fpEnvelope f).choose

/-- The closed immersion of `X` into its finite-presentation envelope
`AlgebraicGeometry.Scheme.Hom.fpEnvelope` (blueprint:
`theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def toFpEnvelope : X ⟶ f.fpEnvelope :=
  (exists_fpEnvelope f).choose_spec.choose

/-- The structure morphism of the finite-presentation envelope
`AlgebraicGeometry.Scheme.Hom.fpEnvelope` (blueprint:
`theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def fpEnvelopeHom : f.fpEnvelope ⟶ Y :=
  (exists_fpEnvelope f).choose_spec.choose_spec.choose

/-- **Properties of the finite-presentation envelope** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): `X ⟶ f.fpEnvelope` is a closed immersion over `Y`,
and `f.fpEnvelope ⟶ Y` is separated, quasi-compact and locally of finite presentation. These are
the properties of the envelope of Stacks Tag 01ZJ. -/
theorem fpEnvelope_spec :
    IsClosedImmersion f.toFpEnvelope ∧ LocallyOfFinitePresentation f.fpEnvelopeHom ∧
      QuasiCompact f.fpEnvelopeHom ∧ IsSeparated f.fpEnvelopeHom ∧
      f.toFpEnvelope ≫ f.fpEnvelopeHom = f :=
  (exists_fpEnvelope f).choose_spec.choose_spec.choose_spec

instance : IsClosedImmersion f.toFpEnvelope := (fpEnvelope_spec f).1

instance : LocallyOfFinitePresentation f.fpEnvelopeHom := (fpEnvelope_spec f).2.1

instance : QuasiCompact f.fpEnvelopeHom := (fpEnvelope_spec f).2.2.1

instance : IsSeparated f.fpEnvelopeHom := (fpEnvelope_spec f).2.2.2.1

@[reassoc (attr := simp)]
lemma toFpEnvelope_fpEnvelopeHom : f.toFpEnvelope ≫ f.fpEnvelopeHom = f :=
  (fpEnvelope_spec f).2.2.2.2

end Scheme.Hom

/-! ### The constructed compactification -/

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- The compactification of the finite-presentation envelope `f.fpEnvelope ⟶ Y` used in the
final assembly: a chosen compactification provided by
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def fpEnvelopeCompactification : Compactification f.fpEnvelopeHom :=
  have := nagataCompactification_of_locallyOfFinitePresentation f.fpEnvelopeHom
  HasCompactification.compactification f.fpEnvelopeHom

/-- **The constructed Nagata compactification** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): the closed-subscheme compactification
`AlgebraicGeometry.Compactification.ofIsClosedImmersion` of the closed immersion
`X ⟶ f.fpEnvelope` inside the compactification `AlgebraicGeometry.fpEnvelopeCompactification`
of the finite-presentation envelope. -/
noncomputable def constructedCompactification : Compactification f :=
  (Compactification.ofIsClosedImmersion f.toFpEnvelope (fpEnvelopeCompactification f)).copy
    (f.toFpEnvelope_fpEnvelopeHom).symm

/-- **Components of the constructed compactification** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): the ambient scheme is the scheme-theoretic image
of `X ⟶ f.fpEnvelope ⟶ Z`, where `Z` is the ambient scheme of the compactification of the
envelope; the open immersion is the canonical image factor and the structure morphism is the
restriction of the ambient structure morphism `Z ⟶ Y`. -/
theorem constructedCompactification_spec :
    (constructedCompactification f).Z =
        (f.toFpEnvelope ≫ (fpEnvelopeCompactification f).i).image ∧
      (constructedCompactification f).i =
        (f.toFpEnvelope ≫ (fpEnvelopeCompactification f).i).toImage ∧
      (constructedCompactification f).g =
        (f.toFpEnvelope ≫ (fpEnvelopeCompactification f).i).imageι ≫
          (fpEnvelopeCompactification f).g :=
  ⟨rfl, rfl, rfl⟩

/-- **The ambient morphism of the constructed compactification is proper** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): it is the composite of the closed immersion of a
scheme-theoretic image with the proper structure morphism of the compactification of the
finite-presentation envelope. -/
theorem isProper_constructedCompactification_g : IsProper (constructedCompactification f).g := by
  rw [(constructedCompactification_spec f).2.2]
  infer_instance

/-- **The source map of the constructed compactification is a quasi-compact open immersion**
(blueprint: `theorem-nagata-s-compactification-theorem--1`): `X ⟶ f.fpEnvelope ⟶ Z` is a
quasi-compact immersion, so its image factor is a quasi-compact open immersion. -/
theorem isOpenImmersion_constructedCompactification_i :
    IsOpenImmersion (constructedCompactification f).i ∧
      QuasiCompact (constructedCompactification f).i := by
  have : QuasiCompact (fpEnvelopeCompactification f).i :=
    (fpEnvelopeCompactification f).quasiCompact_openImmersion inferInstance
  rw [(constructedCompactification_spec f).2.1]
  exact ⟨inferInstance, inferInstance⟩

/-- **Factorization equality for the constructed compactification** (blueprint:
`theorem-nagata-s-compactification-theorem--1`): `X ⟶ f.fpEnvelope ⟶ Z` followed by the image
inclusion is the original composite, and the structure morphism of the envelope composed with
`X ⟶ f.fpEnvelope` is `f`. -/
theorem constructedCompactification_i_g :
    (constructedCompactification f).i ≫ (constructedCompactification f).g = f := by
  rw [(constructedCompactification_spec f).2.1, (constructedCompactification_spec f).2.2,
    Scheme.Hom.toImage_imageι_assoc, Category.assoc, ← (fpEnvelopeCompactification f).comm,
    f.toFpEnvelope_fpEnvelopeHom]

/-- **Nagata compactification** (blueprint: `theorem-nagata-s-compactification-theorem--1`,
`theorem-nagata-s-compactification-theorem--1`).

A chosen compactification of a separated, quasi-compact morphism `f` locally of finite type over
a quasi-compact quasi-separated base. It exists since `f` has the constructed compactification
`AlgebraicGeometry.constructedCompactification`: its source map is an open immersion
(`AlgebraicGeometry.isOpenImmersion_constructedCompactification_i`), its ambient morphism is
proper (`AlgebraicGeometry.isProper_constructedCompactification_g`) and their composite is `f`
(`AlgebraicGeometry.constructedCompactification_i_g`). -/
noncomputable def NagataCompactification : Compactification f :=
  have : HasCompactification f :=
    have := (isOpenImmersion_constructedCompactification_i f).1
    have := isProper_constructedCompactification_g f
    ⟨⟨⟨_, _, _, (constructedCompactification_i_g f).symm, ‹_›, ‹_›⟩⟩⟩
  HasCompactification.compactification f

instance : HasCompactification f :=
  (NagataCompactification f).hasCompactification

/-- A morphism `f : X ⟶ Y` over a quasi-compact and quasi-separated scheme `S`, between `S`-schemes
that are separated and of finite type over `S`, has a compactification: it is separated, locally
of finite type and quasi-compact, and `Y` is quasi-compact and quasi-separated, so Nagata's
compactification theorem applies. This is not an instance, since `S` cannot be inferred from `f`;
it can be used as a local instance. -/
theorem HasCompactification.of_isOver {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] [IsSeparated (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [IsSeparated (Y ↘ S)] [QuasiCompact (Y ↘ S)] [CompactSpace S] [QuasiSeparatedSpace S] :
    HasCompactification f := by
  have e := comp_over f S
  have : IsSeparated (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : LocallyOfFiniteType (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : QuasiCompact (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have := IsSeparated.of_comp f (Y ↘ S)
  have := locallyOfFiniteType_of_comp f (Y ↘ S)
  have := QuasiCompact.of_comp f (Y ↘ S)
  have := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have := quasiSeparatedSpace_of_quasiSeparated (Y ↘ S)
  infer_instance

/-- The underlying morphism of schemes `f.left` of a morphism `f : X ⟶ Y` of `Over S`, `S`
quasi-compact and quasi-separated, between objects whose structure morphisms are separated and
of finite type, has a compactification: this is `HasCompactification.of_isOver`. This is not an
instance, since `S` cannot be inferred from `f.left`; it can be used as a local instance. -/
theorem HasCompactification.of_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [QuasiCompact Y.hom] [CompactSpace S] [QuasiSeparatedSpace S] :
    HasCompactification f.left :=
  have : IsSeparated (X.left ↘ S) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (X.left ↘ S) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ S) := ‹QuasiCompact X.hom›
  have : IsSeparated (Y.left ↘ S) := ‹IsSeparated Y.hom›
  have : QuasiCompact (Y.left ↘ S) := ‹QuasiCompact Y.hom›
  of_isOver (S := S) f.left

end AlgebraicGeometry
