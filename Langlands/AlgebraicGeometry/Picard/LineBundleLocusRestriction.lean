import Langlands.AlgebraicGeometry.Picard.LineBundleLocus

/-! # Restriction of the actual rank-one locus -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y S : Scheme.{u}}

/-- A trivialization on an open of the source of an open immersion gives a
trivialization of the original module on the corresponding image open. -/
def imageOpenTrivialization (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (U : X.Opens)
    (e : (M.restrict f).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.restrict (f ''ᵁ U).ι ≅ SheafOfModules.unit (f ''ᵁ U).toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr (f.isoImage_inv_ι U).symm).app M) ≪≫
    (Scheme.Modules.restrictFunctorComp (f.isoImage U).inv (U.ι ≫ f)).app M ≪≫
      (Scheme.Modules.restrictFunctor (f.isoImage U).inv).mapIso
        ((Scheme.Modules.restrictFunctorComp U.ι f).app M ≪≫ e) ≪≫
          Scheme.Modules.restrictUnitIso (f.isoImage U).inv

/-- Along an open immersion, formation of the rank-one locus commutes with
restriction in both directions, without a finiteness hypothesis. -/
lemma rankOneLocus_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    rankOneLocus (M.restrict f) = f ⁻¹ᵁ rankOneLocus M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, ⟨e⟩⟩ := (mem_rankOneLocus _ x).mp hx
    exact (mem_rankOneLocus M (f x)).mpr
      ⟨f ''ᵁ U, ⟨x, hxU, rfl⟩, ⟨imageOpenTrivialization f M U e⟩⟩
  · rw [rankOneLocus_eq_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M)]
    exact preimage_rankOneLocus_le f M

/-- An actual restriction is a line bundle exactly when its open lies in the
rank-one locus. -/
lemma isLocallyFreeRankOne_restrict_iff (M : X.Modules) (U : X.Opens) :
    IsLocallyFreeRankOne (M.restrict U.ι) ↔ U ≤ rankOneLocus M := by
  constructor
  · intro h x hx
    have h' : (⟨x, hx⟩ : U.toScheme) ∈ rankOneLocus (M.restrict U.ι) :=
      (mem_rankOneLocus _ _).mpr (h ⟨x, hx⟩)
    rw [rankOneLocus_restrict] at h'
    exact h'
  · exact isLocallyFreeRankOne_restrict_of_le M U

/-- The full-fibre base open classifies exactly those open restrictions of the
base above which the original module is a line bundle. -/
lemma le_rankOneBaseOpen_iff_isLocallyFreeRankOne (f : X ⟶ S) [UniversallyClosed f]
    (M : X.Modules) (V : S.Opens) :
    V ≤ rankOneBaseOpen f M ↔
      IsLocallyFreeRankOne (M.restrict (f ⁻¹ᵁ V).ι) := by
  rw [le_rankOneBaseOpen_iff, isLocallyFreeRankOne_restrict_iff]

/-- A line bundle over an open of the base contained in the full-fibre base open. -/
def lineBundleOverBaseOpenOfLE (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules)
    (V : S.Opens) (h : V ≤ rankOneBaseOpen f M) :
    LineBundle (f ⁻¹ᵁ V).toScheme :=
  ⟨M.restrict (f ⁻¹ᵁ V).ι,
    (le_rankOneBaseOpen_iff_isLocallyFreeRankOne f M V).mp h⟩

end Langlands.AlgebraicGeometry.Picard
