/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The fixed scheme of a correspondence

Let `c = (c₁, c₂) : C ⟶ X ×_s X` be a pair of morphisms over a base `s`. Its *fixed scheme* is

`Fix(c) = C ×_{X ×_s X, c, Δ_X} X`,

the scheme-theoretic intersection of the image of `c` with the diagonal, with projections
`i_F : Fix(c) ⟶ C` and `d : Fix(c) ⟶ X` satisfying `c₁ i_F = d = c₂ i_F`. It is the equalizer of
`c₁` and `c₂` (`AlgebraicGeometry.Scheme.fixedSchemeIsLimit`). For an endomorphism `h : X ⟶ X`
over `s`, `Fix(h) = Fix(𝟙, h)` is the scheme-theoretic equalizer of `𝟙 X` and `h`.

## Main definitions

- `AlgebraicGeometry.Scheme.fixedScheme`, `fixedSchemeι`, `fixedSchemeProj`: the fixed scheme
  `Fix(c)` and its projections `i_F` and `d`.
- `AlgebraicGeometry.Scheme.Hom.fixedScheme`: the fixed scheme `Fix(h)` of an endomorphism.
- `AlgebraicGeometry.Scheme.HasFiniteClopenComponents`: a scheme with finitely many connected
  components, all of them open and closed.

## Main statements

- `AlgebraicGeometry.Scheme.fixedSchemeIsLimit`: `Fix(c)` is the equalizer of `c₁` and `c₂`.
- `AlgebraicGeometry.Scheme.isClopen_connectedComponent_of_hasFiniteClopenComponents`: the
  connected components of a scheme with finitely many components are open and closed, so that
  the scheme is their disjoint union.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {C X s : Scheme.{u}} (aX : X ⟶ s) (c₁ c₂ : C ⟶ X) (h : c₁ ≫ aX = c₂ ≫ aX)

/-- Blueprint `definition-correspondence--3`: Fixed scheme of a correspondence.

For `c = (c₁, c₂) : C ⟶ X ×_s X`, the fixed scheme is `Fix(c) = C ×_{X ×_s X, c, Δ_X} X`, the
scheme-theoretic intersection of the image of `c` with the diagonal `Δ_X : X ⟶ X ×_s X`. Its
first projection is `i_F = fixedSchemeι` and its second projection `d = fixedSchemeProj`, with
`c₁ i_F = d = c₂ i_F`. -/
def fixedScheme : Scheme.{u} :=
  pullback (pullback.lift c₁ c₂ h) (pullback.diagonal aX)

/-- The first projection `i_F : Fix(c) ⟶ C` of the fixed scheme. -/
def fixedSchemeι : fixedScheme aX c₁ c₂ h ⟶ C :=
  pullback.fst _ _

/-- The second projection `d : Fix(c) ⟶ X` of the fixed scheme. -/
def fixedSchemeProj : fixedScheme aX c₁ c₂ h ⟶ X :=
  pullback.snd _ _

/-- The defining square of the fixed scheme is Cartesian:

```
  Fix(c) ──i_F──▶ C
     │            │
   d │            │ c = (c₁, c₂)
     ▼            ▼
     X ───Δ_X───▶ X ×_s X
```
-/
lemma isPullback_fixedScheme :
    IsPullback (fixedSchemeι aX c₁ c₂ h) (fixedSchemeProj aX c₁ c₂ h) (pullback.lift c₁ c₂ h)
      (pullback.diagonal aX) :=
  IsPullback.of_hasPullback _ _

/-- `c₁ ∘ i_F = d`. -/
@[reassoc (attr := simp)]
lemma fixedSchemeι_comp_fst : fixedSchemeι aX c₁ c₂ h ≫ c₁ = fixedSchemeProj aX c₁ c₂ h := by
  have := (isPullback_fixedScheme aX c₁ c₂ h).w =≫ pullback.fst aX aX
  simpa using this

/-- `c₂ ∘ i_F = d`. -/
@[reassoc (attr := simp)]
lemma fixedSchemeι_comp_snd : fixedSchemeι aX c₁ c₂ h ≫ c₂ = fixedSchemeProj aX c₁ c₂ h := by
  have := (isPullback_fixedScheme aX c₁ c₂ h).w =≫ pullback.snd aX aX
  simpa using this

/-- The two legs agree on the fixed scheme: `c₁ ∘ i_F = c₂ ∘ i_F`. -/
@[reassoc]
lemma fixedSchemeι_condition : fixedSchemeι aX c₁ c₂ h ≫ c₁ = fixedSchemeι aX c₁ c₂ h ≫ c₂ := by
  simp

/-- The fixed scheme is isomorphic to the equalizer of the two legs. -/
def fixedSchemeIsoEqualizer : fixedScheme aX c₁ c₂ h ≅ equalizer c₁ c₂ :=
  (isPullback_fixedScheme aX c₁ c₂ h).isoIsPullback _ _ (isPullback_equalizer_ι_diagonal c₁ c₂ h)

@[reassoc (attr := simp)]
lemma fixedSchemeIsoEqualizer_hom_ι :
    (fixedSchemeIsoEqualizer aX c₁ c₂ h).hom ≫ equalizer.ι c₁ c₂ = fixedSchemeι aX c₁ c₂ h :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The fixed scheme `Fix(c)`, with `i_F : Fix(c) ⟶ C`, is the scheme-theoretic equalizer of
`c₁` and `c₂`. -/
def fixedSchemeIsLimit :
    IsLimit (Fork.ofι (fixedSchemeι aX c₁ c₂ h) (fixedSchemeι_condition aX c₁ c₂ h)) :=
  IsLimit.ofIsoLimit (equalizerIsEqualizer c₁ c₂)
    (Fork.ext (fixedSchemeIsoEqualizer aX c₁ c₂ h).symm
      (by
        rw [Iso.symm_hom, Iso.inv_comp_eq]
        simp))

instance : Mono (fixedSchemeι aX c₁ c₂ h) :=
  Fork.IsLimit.mono (fixedSchemeIsLimit aX c₁ c₂ h)

/-- A morphism `t : T ⟶ C` on which the two legs agree factors through the fixed scheme. -/
def fixedSchemeLift {T : Scheme.{u}} (t : T ⟶ C) (ht : t ≫ c₁ = t ≫ c₂) :
    T ⟶ fixedScheme aX c₁ c₂ h :=
  pullback.lift t (t ≫ c₁) (by apply pullback.hom_ext <;> simp [ht])

@[reassoc (attr := simp)]
lemma fixedSchemeLift_ι {T : Scheme.{u}} (t : T ⟶ C) (ht : t ≫ c₁ = t ≫ c₂) :
    fixedSchemeLift aX c₁ c₂ h t ht ≫ fixedSchemeι aX c₁ c₂ h = t :=
  pullback.lift_fst _ _ _

/-- The inclusion `i_F : Fix(c) ⟶ C` is an immersion, a base change of the diagonal. -/
instance : IsImmersion (fixedSchemeι aX c₁ c₂ h) :=
  MorphismProperty.of_isPullback (isPullback_fixedScheme aX c₁ c₂ h).flip inferInstance

/-- The inclusion `i_F : Fix(c) ⟶ C` is a closed immersion if `X` is separated over `s`. -/
instance [IsSeparated aX] : IsClosedImmersion (fixedSchemeι aX c₁ c₂ h) :=
  MorphismProperty.of_isPullback (isPullback_fixedScheme aX c₁ c₂ h).flip inferInstance

/-- The inclusion `i_F : Fix(c) ⟶ C` is quasi-compact if `X` is quasi-separated over `s`. -/
instance [QuasiSeparated aX] : QuasiCompact (fixedSchemeι aX c₁ c₂ h) :=
  MorphismProperty.of_isPullback (isPullback_fixedScheme aX c₁ c₂ h).flip inferInstance

/-- The fixed scheme `Fix(h) = Fix(𝟙, h)` of an endomorphism `h : X ⟶ X` over `s`
(blueprint `definition-correspondence--3`): the scheme-theoretic equalizer of `h` and `𝟙 X`
(`Scheme.fixedSchemeIsLimit`). -/
abbrev Hom.fixedScheme (g : X ⟶ X) (hg : g ≫ aX = aX) : Scheme.{u} :=
  Scheme.fixedScheme aX (𝟙 X) g (by rw [hg, Category.id_comp])

/-- A scheme `F` *has finitely many open-and-closed components* if its set `π₀(F)` of connected
components is finite (blueprint `definition-correspondence--3`). The components are then open and
closed (`isClopen_connectedComponent_of_hasFiniteClopenComponents`), and `F` is their disjoint union
(`isIso_sigmaDesc_connectedComponents`). -/
def HasFiniteClopenComponents (F : Scheme.{u}) : Prop :=
  Finite (ConnectedComponents F)

/-- The connected components of a scheme with finitely many components are open and closed:
the complement of a component is a finite union of closed components. -/
lemma isClopen_connectedComponent_of_hasFiniteClopenComponents {F : Scheme.{u}}
    (hF : F.HasFiniteClopenComponents) (x : F) : IsClopen (connectedComponent x) := by
  refine ⟨isClosed_connectedComponent, ?_⟩
  have : Finite (ConnectedComponents F) := hF
  have : (connectedComponent x)ᶜ =
      ⋃ c ∈ ({ConnectedComponents.mk x}ᶜ : Set (ConnectedComponents F)),
        ConnectedComponents.mk ⁻¹' {c} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop, exists_eq_right']
    rw [← ConnectedComponents.coe_eq_coe', eq_comm]
  rw [← isClosed_compl_iff, this]
  refine (Set.toFinite _).isClosed_biUnion fun c _ ↦ ?_
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

end AlgebraicGeometry.Scheme
