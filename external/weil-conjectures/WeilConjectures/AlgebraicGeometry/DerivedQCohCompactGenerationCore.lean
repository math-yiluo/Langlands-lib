/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectLocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-! # Perfect representatives detect zero

Source: Stacks Project, Tag 09IS, and the orthogonal-class argument in
lem-pc-derived-qcoh-compact-generation.
(blueprint: lem-pc-derived-qcoh-representatives-generate).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A family representing every perfect object weakly generates whenever perfect objects
have the whole category as their localizing closure. No compactness is asserted here.
Source: Stacks Project, Tag 09IS; the orthogonal-class reduction in the proof of
lem-pc-derived-qcoh-compact-generation.
(blueprint: lem-pc-derived-qcoh-representatives-generate).

Proof: Suppose every map from the coproduct of P into every shift of K is zero.
A map from a single P i extends to the coproduct by using zero on the other summands,
so every map from P i into every shift of K vanishes. By the representative isomorphisms,
the same holds for every perfect object. Shift adjunction transfers this to vanishing
of maps from every shift of a perfect object into K. In the ambient derived category,
let A consist of quasi-coherent objects whose every shift has only zero maps into K.obj.
This property is invariant under isomorphisms and shifts. It is closed under retracts
by composing with the inclusion and projection. For an ambient distinguished triangle
with first two terms in A, exactness of Hom into K.obj makes every map from a shift of
the third term factor through a shift of the first term, so it is zero. For an ambient
coproduct of objects in A, shifts preserve its universal property, and a map into K.obj
is zero because its restrictions to all summands are zero. Thus A is one of the
properties defining perfectLocalizingClosure X. The assumed equality with top implies
K lies in A. Taking its identity in shift zero shows that K.obj is zero. Fullness of the
inclusion then implies K is zero in the full subcategory. Contraposition gives the weak
generator condition. For an empty family, the representative hypothesis and closure
assumption force the category to be zero, and the same argument applies. -/
theorem schemeDerivedQCoh_representatives_generate (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (htri : (schemeDerivedQCohProperty X).IsTriangulated)
    {I : Type u} (P : I → schemeDerivedQCohCategory X)
    (hrepresentatives : ∀ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj →
      ∃ i : I, Nonempty (E ≅ P i))
    (hclosure : perfectLocalizingClosure X =
      (⊤ : ObjectProperty (schemeDerivedQCohCategory X))) :
    letI := htri
    letI := derivedQCohDirectSums X
    IsTriangulatedGeneratingFamily P := by
  classical
  let := htri
  let := derivedQCohDirectSums X
  intro K hK
  by_contra h
  change ¬ (∃ n : ℤ, ∃ f : ∐ P ⟶ K⟦n⟧, f ≠ 0) at h
  push Not at h
  have hsingle (i : I) (n : ℤ) (f : P i ⟶ K⟦n⟧) : f = 0 := by
    let g : ∐ P ⟶ K⟦n⟧ := Sigma.desc fun j ↦
      if hj : j = i then eqToHom (congrArg P hj) ≫ f else 0
    have hg := h n g
    have := congrArg (fun g ↦ Sigma.ι P i ≫ g) hg
    simpa [g] using this
  have hperfect (E : schemeDerivedQCohCategory X) (hE : Scheme.IsPerfect X E.obj)
      (n : ℤ) (f : E ⟶ K⟦n⟧) : f = 0 := by
    obtain ⟨i, ⟨e⟩⟩ := hrepresentatives E hE
    have hf := hsingle i n (e.inv ≫ f)
    have := congrArg (fun g ↦ e.hom ≫ g) hf
    simpa using this
  let S : ObjectProperty (schemeDerivedCategory X) := fun Y ↦ Y = K.obj
  let Q := (S.shiftClosure ℤ).leftOrthogonal
  let A : ObjectProperty (schemeDerivedQCohCategory X) := fun E ↦ Q E.obj
  have hA : A ∈ {R : ObjectProperty (schemeDerivedQCohCategory X) |
      (∀ E, Scheme.perfectSubcategory X E.obj → R E) ∧
      (∀ B C, R B → Nonempty (B ≅ C) → R C) ∧
      (∀ B (n : ℤ), R B → ∀ C, Nonempty (C.obj ≅ B.obj⟦n⟧) → R C) ∧
      (∀ B C, R B → R C → ∀ T : Pretriangulated.Triangle (schemeDerivedCategory X),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ B.obj) → Nonempty (T.obj₂ ≅ C.obj) →
        ∀ D, Nonempty (T.obj₃ ≅ D.obj) → R D) ∧
      (∀ B C, R C → Nonempty (Retract B.obj C.obj) → R B) ∧
      (∀ (J : Type u) (E : J → schemeDerivedQCohCategory X),
        ∀ S' : schemeDerivedCategory X, ∀ ι : ∀ j, (E j).obj ⟶ S',
        IsColimit (Cofan.mk S' ι) → ∀ B, Nonempty (B.obj ≅ S') →
          (∀ j, R (E j)) → R B)} := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro E hE Y f hY
      obtain ⟨Y', n, e, hY'⟩ := hY
      change Y' = K.obj at hY'
      subst Y'
      let c := ((schemeDerivedQCohProperty X).ι.commShiftIso n).app K
      let g : E ⟶ K⟦n⟧ := ObjectProperty.homMk (f ≫ e.hom ≫ c.inv)
      have hg := hperfect E hE n g
      have hf : f ≫ e.hom ≫ c.inv = 0 := by
        have := congrArg (fun g ↦ (schemeDerivedQCohProperty X).ι.map g) hg
        simpa [g] using this
      apply (cancel_mono (e.hom ≫ c.inv)).1
      simpa using hf
    · rintro B C hB ⟨e⟩
      exact Q.prop_of_iso ((schemeDerivedQCohProperty X).ι.mapIso e) hB
    · rintro B n hB C ⟨e⟩
      exact Q.prop_of_iso e.symm (Q.le_shift n B.obj hB)
    · rintro B C hB hC T hT ⟨eB⟩ ⟨eC⟩ D ⟨eD⟩
      apply Q.prop_of_iso eD
      exact Q.ext_of_isTriangulatedClosed₃ T hT
        (Q.prop_of_iso eB.symm hB) (Q.prop_of_iso eC.symm hC)
    · rintro B C hC ⟨r⟩ Y f hY
      have hf := hC (r.r ≫ f) hY
      have := congrArg (fun g ↦ r.i ≫ g) hf
      simpa using this
    · rintro J E S' ι hcol B ⟨e⟩ hE
      apply Q.prop_of_iso e.symm
      intro Y f hY
      apply hcol.hom_ext
      intro j
      simpa using hE j.as (ι j.as ≫ f) hY
  have hle : perfectLocalizingClosure X ≤ A := sInf_le hA
  have hAK : A K := hle K (by rw [hclosure]; trivial)
  have hid : 𝟙 K.obj = 0 := hAK (𝟙 K.obj) (S.le_shiftClosure K.obj rfl)
  apply hK
  rw [IsZero.iff_id_eq_zero]
  apply (schemeDerivedQCohProperty X).ι.map_injective
  simpa using hid

end AlgebraicGeometry
