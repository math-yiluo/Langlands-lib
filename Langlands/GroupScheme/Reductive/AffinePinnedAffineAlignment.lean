import Langlands.GroupScheme.Reductive.AffinePinnedLocalAlignment

/-! # Affine neighbourhoods with based coordinate alignment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

variable {S U V : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]

/-- A prescribed full character formula on an actual pullback persists after
any further refinement, with the direct normalized pullback as its endpoint. -/
theorem characters_pullHom_comp (τ : splitTorus S I ⟶ splitTorus S J)
    (w : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (q : U ⟶ S) (r : V ⟶ U)
    (h : ∀ (Z : Over U) (t : Z ⟶ (splitTorus U I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J Z (t ≫ (pullHom τ q).hom.hom) j ^ m j =
        ∏ i, pointsEquiv I Z t i ^ w m i) :
    ∀ (Z : Over V) (t : Z ⟶ (splitTorus V I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J Z (t ≫ (pullHom τ (r ≫ q)).hom.hom) j ^ m j =
        ∏ i, pointsEquiv I Z t i ^ w m i := by
  have hq := (characters_iff_pullHom τ q w).mp h
  let a : Over.mk (r ≫ q) ⟶ Over.mk q := Over.homMk r rfl
  have ha : a ≫ TorusConjugation.overHom (U := Over.mk (𝟙 S)) q =
      TorusConjugation.overHom (U := Over.mk (𝟙 S)) (r ≫ q) := by
    apply Over.OverMorphism.ext
    rfl
  have hqa := HomFamily.ActsBy.comp (Iso.refl _) (Iso.refl _) hq a
  rw [ha] at hqa
  exact (characters_iff_pullHom τ (r ≫ q) w).mpr hqa

end splitTorus

namespace AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A point has an affine open neighbourhood carrying the based alignment,
with the exact specified group and torus maps pulled directly from `T`. -/
theorem exists_affine_basedCoordinateIso (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) (x : T) :
    ∃ (A : CommRingCat.{u}) (q : Spec A ⟶ T),
      IsOpenImmersion q ∧ x ∈ Set.range q ∧
      ∃ d : BasedCoordinateIso
        (M.inclusionOver (q ≫ f)) (N.inclusionOver (q ≫ g))
        M.rootDatum N.rootDatum M.basis N.basis,
        d.groupIso = pullComparison e q ∧ d.torusIso = splitTorus.pullIso τ q := by
  obtain ⟨W, hxW, d, hde, hdτ⟩ := exists_open_basedCoordinateIso e τ hτ hb x
  obtain ⟨A, q, hq, hxq, hqW⟩ := Scheme.exists_affine_mem_range_and_range_subset hxW
  have hqW' : Set.range q ⊆ Set.range W.ι := by
    simpa only [Scheme.Opens.range_ι] using hqW
  let a : Spec A ⟶ W := IsOpenImmersion.lift W.ι q hqW'
  have ha : a ≫ W.ι = q := IsOpenImmersion.lift_fac W.ι q hqW'
  have hc := d.characters
  rw [hdτ] at hc
  have hca := splitTorus.characters_pullHom_comp τ.hom d.rootEquiv.weightMap W.ι a hc
  rw [ha] at hca
  refine ⟨A, q, hq, hxq, ?_⟩
  exact ⟨{
    groupIso := pullComparison e q
    torusIso := splitTorus.pullIso τ q
    rootEquiv := d.rootEquiv
    sourcePairing := d.sourcePairing
    targetPairing := d.targetPairing
    simple_iff := d.simple_iff
    square := torusSquare_pull e τ hτ q
    characters := hca
  }, rfl, rfl⟩

/-- An actual affine open chart with based alignment of the specified maps. -/
structure AffineBasedAlignment (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates) (x : T) where
  ring : CommRingCat.{u}
  map : Spec ring ⟶ T
  openImmersion : IsOpenImmersion map
  point : Spec ring
  image_point : map point = x
  data : BasedCoordinateIso
    (M.inclusionOver (map ≫ f)) (N.inclusionOver (map ≫ g))
    M.rootDatum N.rootDatum M.basis N.basis
  groupIso_eq : data.groupIso = pullComparison e map
  torusIso_eq : data.torusIso = splitTorus.pullIso τ map

/-- Choose an affine aligned chart above each point. -/
def affineBasedAlignment (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) (x : T) : AffineBasedAlignment e τ x :=
  Classical.choice <| by
    obtain ⟨A, q, hq, ⟨y, hy⟩, d, hde, hdτ⟩ :=
      exists_affine_basedCoordinateIso e τ hτ hb x
    exact ⟨{
      ring := A
      map := q
      openImmersion := hq
      point := y
      image_point := hy
      data := d
      groupIso_eq := hde
      torusIso_eq := hdτ
    }⟩

/-- The affine aligned charts form a covering family, even over an empty or
non-quasi-compact base. -/
def affineBasedAlignmentCover (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) : Scheme.AffineCover.{u} @IsOpenImmersion T where
  I₀ := T
  X x := (affineBasedAlignment e τ hτ hb x).ring
  f x := (affineBasedAlignment e τ hτ hb x).map
  idx := id
  covers x := ⟨(affineBasedAlignment e τ hτ hb x).point,
    (affineBasedAlignment e τ hτ hb x).image_point⟩
  map_prop x := (affineBasedAlignment e τ hτ hb x).openImmersion

/-- The actual comparison on the selected affine chart preserves the canonical
ambient cocharacter. -/
theorem AffineBasedAlignment.preservesCocharacter
    {e : Comparison f g}
    {τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates} {x : T}
    (d : AffineBasedAlignment e τ x) :
    PreservesCocharacter (pullComparison e d.map) := by
  have h := d.data.cocharacter_comp
  rw [d.groupIso_eq] at h
  exact h

end AffinePinnedModel

end Langlands.GroupScheme
