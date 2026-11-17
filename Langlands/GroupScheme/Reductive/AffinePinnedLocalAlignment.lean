import Langlands.GroupScheme.Reductive.AffinePinnedFieldAlignment
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonPullback
import Langlands.GroupScheme.Torus.LocalExponentTransport

/-! # Local based coordinate alignment of actual comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T W : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- The square for a supplied torus isomorphism persists under actual pullback. -/
theorem torusSquare_pull (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (q : W ⟶ T) :
    M.inclusionOver (q ≫ f) ≫ (pullComparison e q).hom =
      (splitTorus.pullIso τ q).hom ≫ N.inclusionOver (q ≫ g) := by
  rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q]
  simp only [pullComparison, splitTorus.pullIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, BasedBorelTransport.baseChangeInclusion,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, hτ, Functor.map_comp]
  simp only [Category.assoc]

/-- Actual field maps to the two coefficient spectra yield based full
coordinate data for the prescribed torus map. -/
theorem exists_fieldCoordinateData (k : Type u) [Field k]
    (f : Spec (CommRingCat.of k) ⟶ M.base)
    (g : Spec (CommRingCat.of k) ⟶ N.base)
    (e : Comparison f g)
    (τ : splitTorus (Spec (CommRingCat.of k)) M.coordinates ≅
      splitTorus (Spec (CommRingCat.of k)) N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) :
    ∃ r : RootPairing.Equiv N.rootDatum M.rootDatum,
      (∀ a, a ∈ N.basis.support ↔ r.indexEquiv a ∈ M.basis.support) ∧
      (∀ m n, M.rootDatum.toLinearMap m n = ∑ i, m i * n i) ∧
      (∀ m n, N.rootDatum.toLinearMap m n = ∑ i, m i * n i) ∧
      ∀ (U : Over (Spec (CommRingCat.of k)))
        (x : U ⟶ (splitTorus (Spec (CommRingCat.of k)) M.coordinates).X)
        (m : N.coordinates → ℤ),
        ∏ j, splitTorus.pointsEquiv N.coordinates U (x ≫ τ.hom.hom.hom) j ^ m j =
          ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ r.weightMap m i := by
  let : Algebra M.ring k := (Spec.preimage f).hom.toAlgebra
  let : Algebra N.ring k := (Spec.preimage g).hom.toAlgebra
  have hf : algebraBaseMap M.ring k = f := Spec.map_preimage f
  have hg : algebraBaseMap N.ring k = g := Spec.map_preimage g
  let e' : Comparison (algebraBaseMap M.ring k) (algebraBaseMap N.ring k) :=
    eqToIso (congrArg M.groupOver hf) ≪≫ e ≪≫ (eqToIso (congrArg N.groupOver hg)).symm
  have H (f' : Spec (CommRingCat.of k) ⟶ M.base)
      (g' : Spec (CommRingCat.of k) ⟶ N.base)
      (hf' : f' = f) (hg' : g' = g) :
      let e'' := eqToIso (congrArg M.groupOver hf') ≪≫ e ≪≫
        (eqToIso (congrArg N.groupOver hg')).symm
      (M.inclusionOver f' ≫ e''.hom = τ.hom ≫ N.inclusionOver g') ∧
        PreservesBorel e'' := by
    subst f'
    subst g'
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_refl] using
      And.intro hτ hb
  obtain ⟨ht, hb'⟩ := H _ _ hf hg
  let d := fieldBasedCoordinateIso M N k e' τ ht hb'
  exact ⟨d.rootEquiv, d.simple_iff, d.sourcePairing, d.targetPairing, d.characters⟩

/-- Near each point, the supplied Borel- and torus-compatible comparison has
based coordinate data with the exact normalized pullback maps. -/
theorem exists_open_basedCoordinateIso (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) (x : T) :
    ∃ W : T.Opens, x ∈ W ∧
      ∃ d : BasedCoordinateIso
        (M.inclusionOver (W.ι ≫ f)) (N.inclusionOver (W.ι ≫ g))
        M.rootDatum N.rootDatum M.basis N.basis,
        d.groupIso = pullComparison e W.ι ∧
          d.torusIso = splitTorus.pullIso τ W.ι := by
  let q := T.fromSpecResidueField x
  obtain ⟨r, hs, hpM, hpN, hc⟩ :=
    exists_fieldCoordinateData (T.residueField x) (q ≫ f) (q ≫ g)
      (pullComparison e q) (splitTorus.pullIso τ q)
      (torusSquare_pull e τ hτ q) (hb.pull q)
  obtain ⟨W, hxW, hW⟩ :=
    splitTorus.exists_open_character_pullHom τ.hom r.weightMap x hc
  refine ⟨W, hxW, ?_⟩
  exact ⟨{
    groupIso := pullComparison e W.ι
    torusIso := splitTorus.pullIso τ W.ι
    rootEquiv := r
    sourcePairing := hpM
    targetPairing := hpN
    simple_iff := hs
    square := torusSquare_pull e τ hτ W.ι
    characters := hW
  }, rfl, rfl⟩

/-- A neighbourhood equipped with based coordinate alignment of the specified
actual comparison and torus map. -/
structure BasedAlignmentNeighbourhood (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates) (x : T) where
  neighbourhood : T.Opens
  mem_neighbourhood : x ∈ neighbourhood
  data : BasedCoordinateIso
    (M.inclusionOver (neighbourhood.ι ≫ f)) (N.inclusionOver (neighbourhood.ι ≫ g))
    M.rootDatum N.rootDatum M.basis N.basis
  groupIso_eq : data.groupIso = pullComparison e neighbourhood.ι
  torusIso_eq : data.torusIso = splitTorus.pullIso τ neighbourhood.ι

/-- Choose the based alignment near a point from its residue-field comparison
and local constancy of the prescribed full character map. -/
def basedAlignmentNeighbourhood (e : Comparison f g)
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g)
    (hb : PreservesBorel e) (x : T) : BasedAlignmentNeighbourhood e τ x := by
  let h := exists_open_basedCoordinateIso e τ hτ hb x
  let W := h.choose
  let hd := h.choose_spec.2
  exact {
    neighbourhood := W
    mem_neighbourhood := h.choose_spec.1
    data := hd.choose
    groupIso_eq := hd.choose_spec.1
    torusIso_eq := hd.choose_spec.2
  }

/-- The aligned comparison preserves the exact canonical ambient cocharacter
on the chosen neighbourhood. -/
theorem BasedAlignmentNeighbourhood.preservesCocharacter
    {e : Comparison f g}
    {τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates} {x : T}
    (d : BasedAlignmentNeighbourhood e τ x) :
    PreservesCocharacter (pullComparison e d.neighbourhood.ι) := by
  have h := d.data.cocharacter_comp
  rw [d.groupIso_eq] at h
  exact h

end Langlands.GroupScheme.AffinePinnedModel
