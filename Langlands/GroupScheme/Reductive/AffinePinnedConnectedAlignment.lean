import Langlands.GroupScheme.Reductive.AffinePinnedLocalAlignment

/-! # A single based coordinate alignment over a connected base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

variable {S : Scheme.{u}} [PreconnectedSpace S]
  {I J : Type u} [Fintype I] [Fintype J]

/-- A full character formula on one field fibre of an actual split-torus map
holds over the whole preconnected base. -/
theorem characters_of_field_pullHom
    (τ : splitTorus S I ⟶ splitTorus S J)
    (r : (J → ℤ) →ₗ[ℤ] (I → ℤ))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J U (x ≫ (pullHom τ b).hom.hom) j ^ m j =
        ∏ i, pointsEquiv I U x i ^ r m i) :
    ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J U (x ≫ τ.hom.hom) j ^ m j =
        ∏ i, pointsEquiv I U x i ^ r m i := by
  classical
  let U₀ : Over S := Over.mk (𝟙 S)
  let : PreconnectedSpace U₀.left := inferInstanceAs (PreconnectedSpace S)
  have hp := (HomFamily.actsBy_overHom_iff (Iso.refl _) (Iso.refl _)
    (homFamily_isHomFamily τ) b (weightMatrix r)).mp
      ((characters_iff_pullHom τ b r).mp hb)
  have hall := HomFamily.actsBy_of_forall_actsAtPoint (Iso.refl _) (Iso.refl _)
    (homFamily_isHomFamily τ) (weightMatrix r)
      (HomFamily.actsAtPoint_of_preconnected (Iso.refl _) (Iso.refl _)
        (homFamily_isHomFamily τ) (weightMatrix r) hp)
  intro U x m
  let a : U ⟶ U₀ := Over.homMk U.hom (by simp [U₀])
  have h := hall U a (pointsEquiv I U x)
  simp only [Category.comp_id, HomFamily.famUnits, homFamily, Iso.refl_inv,
    Iso.refl_hom, Grp.id_hom_hom, Category.comp_id, MulEquiv.symm_apply_apply] at h
  rw [h]
  exact rectPow_character r (pointsEquiv I U x) m

end splitTorus

namespace AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}} [PreconnectedSpace T]
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A torus- and Borel-compatible comparison over a nonempty preconnected base
admits a single full based root-datum equivalence for its actual torus map. -/
theorem exists_basedCoordinateIso_of_preconnected (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) (x : T) :
    ∃ d : BasedCoordinateIso (M.inclusionOver f) (N.inclusionOver g)
      M.rootDatum N.rootDatum M.basis N.basis,
      d.groupIso = e ∧ d.torusIso = τ := by
  let q := T.fromSpecResidueField x
  obtain ⟨r, hs, hpM, hpN, hc⟩ :=
    exists_fieldCoordinateData (T.residueField x) (q ≫ f) (q ≫ g)
      (pullComparison e q) (splitTorus.pullIso τ q)
      (torusSquare_pull e τ hτ q) (hb.pull q)
  exact ⟨{
    groupIso := e
    torusIso := τ
    rootEquiv := r
    sourcePairing := hpM
    targetPairing := hpN
    simple_iff := hs
    square := hτ
    characters := splitTorus.characters_of_field_pullHom τ.hom r.weightMap q hc
  }, rfl, rfl⟩

omit [PreconnectedSpace T] in
/-- Connectedness gives a single based coordinate alignment with the supplied
actual ambient and torus maps. -/
theorem exists_basedCoordinateIso_of_connected [ConnectedSpace T]
    (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) :
    ∃ d : BasedCoordinateIso (M.inclusionOver f) (N.inclusionOver g)
      M.rootDatum N.rootDatum M.basis N.basis,
      d.groupIso = e ∧ d.torusIso = τ :=
  exists_basedCoordinateIso_of_preconnected e τ hτ hb (Classical.choice inferInstance)

end AffinePinnedModel

end Langlands.GroupScheme
