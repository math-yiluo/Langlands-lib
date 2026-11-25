/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation

/-!
# The family object of the deformation to the normal cone

For a deformation datum `D` of a closed section `s` of a smooth `g : V ⟶ B`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is the section
invariant `ℱ = Ls̃^* ω_{g̃}` of the pair `(g̃, s̃)`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObject`). Its fibre over
`t = 0` is the section invariant of the normal cone with its zero section, and for the
deformation space of a section constructed in
`WeilConjectures.AlgebraicGeometry.DeformationToNormalCone` it is pulled back from the base over
the punctured line, and constant for the standard pair: this is smooth base change for `R^!`
(`proposition-exceptional-inverse-image-smooth-morphism` (c)) applied to the cartesian squares of
the deformation.

## Main statements

- `DeformationToNormalConeData.nonempty_iso_leftDerivedUpperStar_zeroSection_familyObject`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_puncturedLine_familyObject`
- `AlgebraicGeometry.Etale.nonempty_iso_familyObject_standardPair`
- `AlgebraicGeometry.Etale.nonempty_iso_familyObject_standardPair_twistShift`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)
  [HasInvertibleExponent Λ B]

/-- Blueprint `prose-09-12` (1), the fibre over `t = 0`: the restriction of the family
object along the zero section is the section invariant of the normal cone with its zero
section,

`Li₀^* ℱ ≃ 𝒞(π_N, 0_N)`. -/
theorem nonempty_iso_leftDerivedUpperStar_zeroSection_familyObject
    [HasCompactification N.proj] [QuasiSeparatedSpace B] [QuasiCompact N.proj] :
    Nonempty ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
        (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection) :=
  have := D.hasInvertibleExponent_scheme Λ
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj D.isPullback_zeroFibre
    D.sect N.zeroSection D.comp_zeroFibre

end Scheme.Hom.DeformationToNormalConeData

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}}

section Construction

variable {d : ℕ} (g : V ⟶ B) [IsSeparated g] [SmoothOfRelativeDimension d g]
  [HasCompactification g] [HasInvertibleExponent Λ V] (s : B ⟶ V) [IsClosedImmersion s]

include d in
/-- Blueprint `prose-09-12` (3), the punctured trivialisation: over the punctured line
`j : 𝔾_{m,B} ⊆ 𝔸¹_B` the family object `ℱ = Ls̃^* ω_{g̃}` of the deformation space of `s` is
pulled back from the base,

`κ° : j^* ℱ ≃ j^* a^* 𝒞(g, s)`, `a : 𝔸¹_B ⟶ B`,

since over `𝔾_{m,B}` the deformation space is `V ×_B 𝔾_{m,B}` with `s̃ = s × 1`. -/
theorem nonempty_iso_leftDerivedUpperStar_puncturedLine_familyObject (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasInvertibleExponent Λ s.ker.deformationSpace] [QuasiSeparatedSpace B] [QuasiCompact g] :
    Nonempty ((L(((Scheme.Hom.puncturedLine B).ι)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≅
      (L(((Scheme.Hom.puncturedLine B).ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ g s))) := by
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  set j := (Scheme.Hom.puncturedLine B).ι
  have PG := Scheme.Hom.isPullback_deformationSpaceGeneric g s
  have hm : (j ≫ s.deformationSpaceSection) ≫ Scheme.Hom.deformationSpaceProj g s = 𝟙 _ ≫ j := by
    rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs,
      Category.comp_id, Category.id_comp]
  set m := PG.lift (j ≫ s.deformationSpaceSection) (𝟙 _) hm
  have hm₁ : m ≫ Scheme.Hom.deformationSpaceGeneric g s = j ≫ s.deformationSpaceSection :=
    PG.lift_fst _ _ _
  have hm₂ : m ≫ pullback.fst _ _ = j ≫ (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s := by
    rw [← Scheme.Hom.deformationSpaceGeneric_toBase g s, reassoc_of% hm₁,
      Scheme.Hom.deformationSpaceSection_toBase]
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d)
    (Scheme.Hom.deformationSpaceProj g s) PG s.deformationSpaceSection m hm₁
  obtain ⟨e₂⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) g
    (IsPullback.of_hasPullback g (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)) s m
    (hm₂.trans (Category.assoc _ _ _).symm)
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ (leftDerivedUpperStarComp _ j (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _⟩

end Construction
section StandardPair

variable (n : Type u) (B : Scheme.{u}) {d : ℕ} [IsSeparated (𝔸(n; B) ↘ B)]
  [SmoothOfRelativeDimension d (𝔸(n; B) ↘ B)] [HasCompactification (𝔸(n; B) ↘ B)]
  [HasInvertibleExponent Λ 𝔸(n; B)]

include d in
/-- Blueprint `prose-09-12` (4), the family object of the standard pair: for the zero section
`0` of `𝔸^n_B ⟶ B`, the deformation space is `𝔸^n_{𝔸¹_B}`
(`AlgebraicGeometry.Scheme.Hom.isIso_deformationSpaceToAffineSpace`), so the family object is
pulled back from the base,

`ℱ ≃ a^* (0^* ω_{𝔸^n_B / B})`, `a : 𝔸¹_B ⟶ B`. -/
theorem nonempty_iso_familyObject_standardPair
    [HasCompactification
      (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))]
    [QuasiSeparatedSpace B] :
    Nonempty (sectionInvariant Λ
        (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
        (AffineSpace.zeroSection n B).deformationSpaceSection ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))) := by
  set Φ := Scheme.Hom.deformationSpaceToAffineSpace n B
  set a := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  have sq : IsPullback (Φ ≫ AffineSpace.map n a)
      (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
      (𝔸(n; B) ↘ B) a := by
    have := (IsPullback.of_horiz_isIso (g := 𝟙 _)
      ⟨(Scheme.Hom.deformationSpaceToAffineSpace_over n B).trans
        (Category.comp_id _).symm⟩).paste_horiz (AffineSpace.isPullback_map (n := n) a)
    simpa using this
  have : QuasiCompact
      (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B)) :=
    MorphismProperty.of_isPullback sq inferInstance
  have hm : (AffineSpace.zeroSection n B).deformationSpaceSection ≫ Φ ≫ AffineSpace.map n a =
      a ≫ AffineSpace.zeroSection n B := by
    rw [reassoc_of% Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace,
      AffineSpace.zeroSection_comp_map]
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) (𝔸(n; B) ↘ B) sq
    (AffineSpace.zeroSection n B) _ hm
  exact ⟨e.symm⟩

end StandardPair
/-- Blueprint `prose-09-12` (4), the family object of the standard pair, made explicit: for
the zero section of `𝔸^c_B ⟶ B` over a separated scheme of finite type over a field, the
family object is the constant Tate twist,

`ℱ ≃ a^* (0^* ω_{𝔸^c_B / B}) ≃ a^* Λ_B(c)[2c] ≃ Λ_{𝔸¹_B}(c)[2c]`,

where `0^* ω = Λ(c)[2c]` is vector-bundle purity for the trivial bundle
(`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`). -/
theorem nonempty_iso_familyObject_standardPair_twistShift [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (c : ℕ) (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]
    [SmoothOfRelativeDimension c (𝔸(ULift.{u} (Fin c); B) ↘ B)]
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (𝔸(ULift.{u} (Fin c); B) ↘ B)
      (AffineSpace.zeroSection (ULift.{u} (Fin c)) B))] :
    Nonempty (sectionInvariant Λ
        (Scheme.Hom.deformationSpaceProj (𝔸(ULift.{u} (Fin c); B) ↘ B)
          (AffineSpace.zeroSection (ULift.{u} (Fin c)) B))
        (AffineSpace.zeroSection (ULift.{u} (Fin c)) B).deformationSpaceSection ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) c).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B))) := by
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated aB
  obtain ⟨e₁⟩ := nonempty_iso_familyObject_standardPair Λ (ULift.{u} (Fin c)) B (d := c)
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_affineSpace Λ c B aB
  exact ⟨e₁ ≪≫ (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (e₂ ≪≫ twistShiftConstantComplexIso Λ B c) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ c ≪≫ (twistShiftConstantComplexIso Λ _ c).symm⟩

end Etale

end AlgebraicGeometry
