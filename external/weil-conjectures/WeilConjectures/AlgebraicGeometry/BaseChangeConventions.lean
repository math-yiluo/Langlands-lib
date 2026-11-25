/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Base change, fibres and induced sections

Source: Stacks Project, Tags 01JX, 01K0, 0095; blueprint
`sec-abelian-varieties/def-sc-jacobian/def-pc-base-change.md`
(blueprint: def-pc-base-change).

`(Over.pullback T.hom).obj (Over.mk f)` is `X_T` over `T`: its underlying scheme is
`pullback f T.hom`, its structure map `pr_T` is `pullback.snd`, and its map `f_T` to `X`
is `pullback.fst`. The functor's map is `h_T` for an `S`-morphism `h`.
`baseChangeMap f g` is the existing map `g_X`, and `sectionBaseChange` is the existing
induced section. Geometric points use the recorded unbundled description
`Spec (.of Ω) ⟶ T.left` with `Ω` algebraically closed, and `Scheme.SpecToEquivOfField`.

## Main definitions

- `Scheme.Modules.moduleBaseChange`: module pullback along `g_X`.
- `Scheme.Hom.geometricFiberAt`: the fibre over a chosen algebraic closure of `κ(t)`.
- The remaining statements record the comparison and section clauses of the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}}

/-- Module base change along `g : T' ⟶ T` over `S` is `g_X^*`.
Source: Stacks, Tag 0095 (blueprint: def-pc-base-change). -/
def Scheme.Modules.moduleBaseChange (f : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    (Limits.pullback f T.hom).Modules ⥤ (Limits.pullback f T'.hom).Modules :=
  Scheme.Modules.tensorPullback (baseChangeMap f g)

/-- Base change of an `S`-morphism is the induced map with the two prescribed projections.
Source: Stacks, Tag 01JX (6) (blueprint: def-pc-base-change).
Proof: the object and map of `Over.pullback` are the chosen pullback and its universal lift
(def-pc-fibre-product). Its first projection is `fst ≫ h.left`, its second is `snd`;
the second equation also expresses that the map is a morphism over `T`. -/
theorem baseChange_morphism_projections {A B : Over S} (h : A ⟶ B) (T : Over S) :
    ((Over.pullback T.hom).map h).left ≫ pullback.fst B.hom T.hom =
      pullback.fst A.hom T.hom ≫ h.left ∧
    ((Over.pullback T.hom).map h).left ≫ pullback.snd B.hom T.hom =
      pullback.snd A.hom T.hom := by
  constructor <;> simp [Over.pullback_map_left]

/-- The map `g_X` exhibits `X_{T'}` as `X_T ×_T T'`, with compatible projections.
Source: Stacks, Tag 01JX and pullback pasting (blueprint: def-pc-base-change).
Proof: the square with `g_X` and the two second projections is cartesian by
`isPullback_baseChangeMap` (def-pc-fibre-product). Its universal property gives a unique
isomorphism to the chosen pullback, compatible with its projections. -/
theorem baseChange_iterated (f : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    ∃ e : pullback f T'.hom ≅ pullback (pullback.snd f T.hom) g.left,
      e.hom ≫ pullback.fst (pullback.snd f T.hom) g.left = baseChangeMap f g ∧
      e.hom ≫ pullback.snd (pullback.snd f T.hom) g.left = pullback.snd f T'.hom := by
  let h := isPullback_baseChangeMap f g
  exact ⟨h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩

/-- `X ×_S Spec κ(t)` is the scheme-theoretic fibre of `pr_T` over `t`.
Source: Stacks, Tag 01K0 (blueprint: def-pc-base-change).
Proof: expand the fibre as the pullback along `T.fromSpecResidueField t`
(def-pc-scheme-fibre, def-weil-residue-field). Pullback pasting
(def-pc-fibre-product) gives the canonical isomorphism and the two displayed equations. -/
theorem baseChange_fiber (f : X ⟶ S) (T : Over S) (t : T.left) :
    ∃ e : pullback f (T.left.fromSpecResidueField t ≫ T.hom) ≅
        (pullback.snd f T.hom).fiber t,
      e.hom ≫ (pullback.snd f T.hom).fiberι t ≫ pullback.fst f T.hom =
        pullback.fst f (T.left.fromSpecResidueField t ≫ T.hom) ∧
      e.hom ≫ (pullback.snd f T.hom).fiberToSpecResidueField t =
        pullback.snd f (T.left.fromSpecResidueField t ≫ T.hom) := by
  refine ⟨(pullbackLeftPullbackSndIso f T.hom
    (T.left.fromSpecResidueField t)).symm, ?_, ?_⟩
  · exact pullbackLeftPullbackSndIso_inv_fst f T.hom (T.left.fromSpecResidueField t)
  · exact pullbackLeftPullbackSndIso_inv_snd_snd f T.hom
      (T.left.fromSpecResidueField t)


/-- The geometric fibre `X ×_S Spec Ω` at `t`, for a chosen algebraic closure `Ω` of `κ(t)`.
The map from `Spec Ω` is induced by the residue-field embedding and the canonical point map.
Source: blueprint Definition def-pc-base-change; Stacks, Tags 01K0, 03PO
(blueprint: def-pc-base-change). -/
def Scheme.Hom.geometricFiberAt (f : X ⟶ S) (T : Over S) (t : T.left)
    (Ω : Type u) [Field Ω] [Algebra (T.left.residueField t) Ω]
    [IsAlgClosure (T.left.residueField t) Ω] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
    T.left.fromSpecResidueField t ≫ T.hom)

/-- The existing induced section is the unique map with the prescribed projections,
and is a section of `pr_T`.
Source: Stacks, Tag 01JX; blueprint induced-section clause (blueprint: def-pc-base-change).
Proof: a section supplies `σ.section_ ≫ f = 𝟙 S` (def-pc-section). Thus its composite
with `T.hom`, together with `𝟙 T.left`, is a compatible pair. `sectionBaseChange` is
its universal lift (def-pc-fibre-product); the lift equations give the two equations,
and pullback hom-extensionality gives uniqueness. -/
theorem baseChange_section_characterization (f : X ⟶ S) (σ : SplitEpi f) (T : Over S) :
    sectionBaseChange f σ.section_ σ.id T ≫ pullback.snd f T.hom = 𝟙 T.left ∧
    sectionBaseChange f σ.section_ σ.id T ≫ pullback.fst f T.hom = T.hom ≫ σ.section_ ∧
    ∀ s : T.left ⟶ pullback f T.hom,
      s ≫ pullback.snd f T.hom = 𝟙 T.left →
      s ≫ pullback.fst f T.hom = T.hom ≫ σ.section_ →
      s = sectionBaseChange f σ.section_ σ.id T := by
  refine ⟨sectionBaseChange_snd f σ.section_ σ.id T, pullback.lift_fst .., ?_⟩
  intro s hs₁ hs₂
  apply pullback.hom_ext
  · simpa only [sectionBaseChange, pullback.lift_fst] using hs₂
  · simpa only [sectionBaseChange, pullback.lift_snd] using hs₁


end
end AlgebraicGeometry
