/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The maximal open on which a target-local property holds

For a morphism `q : Z ⟶ X` and a property `P` of morphisms of schemes we define
`q.maximalOpen P` as the union of all opens `W ⊆ X` over which `q ∣_ W` satisfies `P`.
If `P` is Zariski-local on the target, then `q ∣_ q.maximalOpen P` satisfies `P`:
the defining opens cover `q.maximalOpen P`, so `P` glues over them
(`AlgebraicGeometry.Scheme.Hom.restrict_maximalOpen`).

The instance `P = MorphismProperty.isomorphisms Scheme` is the **maximal isomorphism
open** `AlgebraicGeometry.Scheme.Hom.maximalIsomorphismOpen` used by the modification
layer of the Nagata compactification proof
(blueprint: `def:nagata-maximal-isomorphism-open`,
`lemma:nagata-maximal-isomorphism-open`); other instances of interest are the flat
locus and the open-immersion locus.

We also record that a target-local property restricts to smaller opens
(`AlgebraicGeometry.Scheme.Hom.restrict_of_le`, and its isomorphism instance
`AlgebraicGeometry.Scheme.Hom.isIso_restrict_of_le`), and that a partial isomorphism
can be cancelled on the right (`AlgebraicGeometry.isIso_morphismRestrict_of_comp`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (q : Z ⟶ X) (P : MorphismProperty Scheme.{u})

/-- The **maximal open on which `P` holds** for a morphism `q : Z ⟶ X`: the union of
all opens `W ⊆ X` such that the restriction `q ∣_ W` satisfies `P`. -/
def Scheme.Hom.maximalOpen : X.Opens :=
  sSup {W : X.Opens | P (q ∣_ W)}

variable {q P}

/-- Every open over which `q ∣_ W` satisfies `P` is contained in the maximal open of
`P`. -/
lemma Scheme.Hom.le_maximalOpen {W : X.Opens} (hW : P (q ∣_ W)) : W ≤ q.maximalOpen P :=
  le_sSup hW

variable (q P)

/-- **The maximal open of a target-local property is a locus for it**: `q ∣_ q.maximalOpen P`
satisfies `P`, because `P` is Zariski-local on the target and the defining opens cover the
maximal open. -/
lemma Scheme.Hom.restrict_maximalOpen [IsZariskiLocalAtTarget P] :
    P (q ∣_ q.maximalOpen P) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (U := fun W : {W : X.Opens // P (q ∣_ W)} ↦ (q.maximalOpen P).ι ⁻¹ᵁ W.1) ?_ fun W ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    have hx : x.1 ∈ q.maximalOpen P := x.2
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
  · have himg : (q.maximalOpen P).ι ''ᵁ ((q.maximalOpen P).ι ⁻¹ᵁ W.1) = W.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (Scheme.Hom.le_maximalOpen W.2)]
    exact (MorphismProperty.arrow_mk_iso_iff P
      (morphismRestrictRestrict q _ _ ≪≫ morphismRestrictEq q himg)).mpr W.2

/-- The **maximal isomorphism open** of a morphism `q : Z ⟶ X`: the union of all opens
`W ⊆ X` such that `q` restricts to an isomorphism over `W`.
(Blueprint: `def:nagata-maximal-isomorphism-open`.) -/
def Scheme.Hom.maximalIsomorphismOpen : X.Opens :=
  q.maximalOpen (MorphismProperty.isomorphisms Scheme)

variable {q}

/-- Every open over which `q` restricts to an isomorphism is contained in the maximal
isomorphism open. -/
lemma Scheme.Hom.le_maximalIsomorphismOpen {W : X.Opens} (hW : IsIso (q ∣_ W)) :
    W ≤ q.maximalIsomorphismOpen :=
  Scheme.Hom.le_maximalOpen (P := MorphismProperty.isomorphisms Scheme) hW

variable (q)

/-- **The maximal isomorphism open is an isomorphism locus**: `q` restricts to an
isomorphism over `q.maximalIsomorphismOpen`. This is
`AlgebraicGeometry.Scheme.Hom.restrict_maximalOpen` for the isomorphisms.
(Blueprint: `lemma:nagata-maximal-isomorphism-open`.) -/
lemma Scheme.Hom.isIso_restrict_maximalIsomorphismOpen :
    IsIso (q ∣_ q.maximalIsomorphismOpen) :=
  q.restrict_maximalOpen (MorphismProperty.isomorphisms Scheme)

/-- **A target-local property restricts to smaller opens**: if `q ∣_ W` satisfies a
property which is Zariski-local on the target and `V ≤ W`, then `q ∣_ V` satisfies it
too. -/
lemma Scheme.Hom.restrict_of_le [IsZariskiLocalAtTarget P] {V W : X.Opens} (hVW : V ≤ W)
    (hW : P (q ∣_ W)) : P (q ∣_ V) := by
  have himg : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVW]
  have hres : P (q ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict hW (W.ι ⁻¹ᵁ V)
  exact (MorphismProperty.arrow_mk_iso_iff P
    (morphismRestrictRestrict q W (W.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq q himg)).mp hres

variable {q P}

/-- **An isomorphism over an open is an isomorphism over every smaller open.** -/
lemma Scheme.Hom.isIso_restrict_of_le {V W : X.Opens} (hVW : V ≤ W) (hW : IsIso (q ∣_ W)) :
    IsIso (q ∣_ V) :=
  Scheme.Hom.restrict_of_le q (MorphismProperty.isomorphisms Scheme) hVW hW

/-- **Cancelling a partial isomorphism on the right**: if `f ≫ π = g` and both `π` and
`g` restrict to isomorphisms over an open `V` of the common target, then `f` restricts
to an isomorphism over the inverse image of `V` in the intermediate scheme. -/
lemma isIso_morphismRestrict_of_comp {Y X' X : Scheme.{u}} (f : Y ⟶ X') (π : X' ⟶ X)
    {g : Y ⟶ X} (hg : f ≫ π = g) (V : X.Opens) (hπ : IsIso (π ∣_ V))
    (hgV : IsIso (g ∣_ V)) : IsIso (f ∣_ (π ⁻¹ᵁ V)) := by
  subst hg
  have := hπ
  have := hgV
  have : IsIso ((f ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (π ∣_ V)

end AlgebraicGeometry
