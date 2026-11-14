import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof

/-! # Actual big cells over arbitrary local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.LocalSplitBigCell

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {I : Type u} [Fintype I] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A family of actual root parametrizations over an arbitrary local ring. -/
def rootFamily [IsLocalRing R] (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) : Ga R ⟶ G :=
  (LocalRootGroup.exists_rootParametrization_of_flat i hG hmax hP α).choose

/-- Each member of the chosen family parametrizes its prescribed root subgroup. -/
theorem isRootParametrization_rootFamily [IsLocalRing R] (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    IsRootParametrization i (P.root α) (rootFamily hG hmax hP α) :=
  (LocalRootGroup.exists_rootParametrization_of_flat i hG hmax hP α).choose_spec

/-- With actual root parametrizations supplied, the big-cell map is an open immersion
for every commutative base ring. -/
theorem isOpenImmersion_cellMap (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) (fam : J → (Ga R ⟶ G))
    (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α)) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}) :
    IsOpenImmersion (cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))).left := by
  have := hG.smooth
  have : Fintype J := @Fintype.ofFinite J hP.finite
  have hV (d : ℕ) : Smooth (VectorGroup.groupScheme (CommRingCat.of R) d).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  have : Smooth (cellObj R I m n).hom :=
    GroupScheme.smooth_tensor _ _
      (GroupScheme.smooth_tensor _ _ (hV m) (smooth_splitTorus I)) (hV n)
  apply Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise
  intro s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  have h := isOpenImmersion_fibre hG hmax hP b fam hfam neg pos
    ((Spec (CommRingCat.of R)).residueField s)
  rw [hb] at h
  exact h

/-- The chosen actual root family gives a big cell over every commutative local ring. -/
theorem isOpenImmersion_rootFamily [IsLocalRing R] (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}) :
    IsOpenImmersion (cellMap i (rootFamily hG hmax hP)
      (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
  isOpenImmersion_cellMap hG hmax hP b (rootFamily hG hmax hP)
    (isRootParametrization_rootFamily hG hmax hP) neg pos

end Langlands.GroupScheme.LocalSplitBigCell
