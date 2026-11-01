import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.PushforwardVanishing
import Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange

/-! # Vanishing after arbitrary affine base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- Jointly zero cohomology of a smooth proper line bundle over an affine base
stays zero after any affine scalar extension. -/
theorem isZero_relativeCohomology_baseChange_of_isZero
    {R S : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [Smooth f] [IsProper f] (L : Picard.LineBundle X)
    (hL : ∀ n : ℕ, IsZero ((relativeCohomology f n).obj L.obj))
    (φ : R ⟶ S) (n : ℕ) :
    IsZero ((relativeCohomology (pullback.snd f (Spec.map φ)) n).obj
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj L.obj)) := by
  obtain ⟨K, hK, ⟨e⟩, hbc⟩ :=
    universalPerfectSections R X f inferInstance inferInstance L
  have hacyclic : K.Acyclic :=
    DerivedPlus.acyclic_of_iso_derivedComplex (relativeGlobalSections f) e hL
  obtain ⟨a, b, ha, hb⟩ := hK.1
  let := hb
  obtain ⟨e'⟩ := hbc S φ
  refine DerivedPlus.isZero_rightDerived_of_iso_derivedComplex
    (relativeGlobalSections (pullback.snd f (Spec.map φ))) e' ?_ n
  exact ModuleComplex.exactAt_baseChange_of_flat φ.hom K b hacyclic
    (fun k => by let := (hK.2 k).2; infer_instance)

/-- Affine opens of the source whose images lie in some affine open of the target. -/
def affineSubordinateBasis {T Y : Scheme.{u}} (x : T ⟶ Y) : Set T.Opens :=
  { W : T.Opens | IsAffineOpen W ∧
    ∃ V : Y.Opens, IsAffineOpen V ∧ W ≤ x ⁻¹ᵁ V }

/-- The affine opens subordinate to the affine cover of the target form a basis,
without any quasi-compactness assumption. -/
theorem isBasis_affineOpens_subordinate {T Y : Scheme.{u}} (x : T ⟶ Y) :
    TopologicalSpace.Opens.IsBasis (affineSubordinateBasis x) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U t ht
  obtain ⟨V, hV, htV, _⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (U := ⊤) (x := x t) (by trivial)
  obtain ⟨W, hW, htW, hWU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (U := U ⊓ x ⁻¹ᵁ V) (x := t) ⟨ht, htV⟩
  exact ⟨W, ⟨hW, V, hV, hWU.trans inf_le_right⟩, htW, hWU.trans inf_le_left⟩

/-- A local affine scalar extension computes the cohomology over a subordinate
affine open of an arbitrary affine base change. -/
theorem isZero_openCohomology_pullback_of_affineRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f]
    (Q : Picard.LineBundle X) {R : CommRingCat.{u}} (x : Spec R ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V)
    (hQ : ∀ n : ℕ, IsZero ((relativeCohomology (affineRestrict f hV) n).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj Q.obj)))
    {W : (Spec R).Opens} (hW : IsAffineOpen W) (hWV : W ≤ x ⁻¹ᵁ V) (n : ℕ) :
    IsZero ((openCohomology ((pullback.snd f x) ⁻¹ᵁ W) n).obj
      ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj)) := by
  let L := (Picard.LineBundle.pullback (f ⁻¹ᵁ V).ι).obj Q
  let φ := x.appLE V W hWV
  have hb := isZero_relativeCohomology_baseChange_of_isZero
    (affineRestrict f hV) L hQ φ n
  have h₁ := (IsPullback.of_hasPullback (affineRestrict f hV) (Spec.map φ)).paste_horiz
    (isPullback_affineRestrict f hV)
  have h₂ := ((isPullback_morphismRestrict (pullback.snd f x) W).flip).paste_horiz
    (IsPullback.of_hasPullback f x)
  have he : hW.isoSpec.hom ≫ (Spec.map φ ≫ hV.fromSpec) = W.ι ≫ x := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWV]
    simp
  have hb' := hb.of_iso ((relativeCohomology _ n).mapIso
    ((Scheme.Modules.pullbackComp _ (f ⁻¹ᵁ V).ι).app Q.obj).symm)
  have ht := isZero_relativeCohomology_of_isPullback f h₁ h₂ hW.isoSpec he
    (pullback.snd (affineRestrict f hV) (Spec.map φ))
    ((pullback.snd f x ∣_ W) ≫ hW.isoSpec.hom) Q.obj n hb'
  have hc := (isZero_cohomology_iff_relativeCohomology _ n _).2 ht
  exact hc.of_iso ((cohomology _ n).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback
      ((pullback.snd f x) ⁻¹ᵁ W).ι).app _ ) ≪≫
      (Scheme.Modules.pullbackComp _ (pullback.fst f x)).app Q.obj))

/-- Vanishing over the inverse images of all affine opens implies vanishing
after any affine base change of a smooth proper line bundle. -/
theorem isZero_relativeCohomology_pullback_of_affineRestricts
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f]
    (Q : Picard.LineBundle X)
    (hQ : ∀ (V : Y.Opens) (hV : IsAffineOpen V) (n : ℕ),
      IsZero ((relativeCohomology (affineRestrict f hV) n).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj Q.obj)))
    {R : CommRingCat.{u}} (x : Spec R ⟶ Y) (n : ℕ) :
    IsZero ((relativeCohomology (pullback.snd f x) n).obj
      ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj)) := by
  have hz : ∀ k : ℕ, IsZero ((higherDirectImage (pullback.snd f x) k).obj
      ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj)) := by
    intro k
    refine isZero_higherDirectImage_of_isBasis (pullback.snd f x)
      (isBasis_affineOpens_subordinate x) k _ ?_
    rintro W ⟨hW, V, hV, hWV⟩
    exact isZero_openCohomology_pullback_of_affineRestrict f Q x hV
      (hQ V hV) hW hWV k
  simpa using isZero_relativeCohomology_of_higherDirectImage (pullback.snd f x)
    (𝟙 (Spec R)) ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj) hz n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
