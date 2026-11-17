import Langlands.GroupScheme.RelativeLevi.SplitBorelPositiveFactors
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Detecting root signs by actual contracting subgroup ranges -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A zero-pairing actual root point has constant conjugation orbit on
every scheme test. -/
theorem rootPoint_mem_centralizer_of_zero
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (ha : coPairing (ch a) wt = 0)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (fam a) Z c ∈
      (Dynamic.centralizer (AffineRegularBorel.cocharacter i wt)).carrier Z := by
  let W := Z ⊗ (Gm (Spec (CommRingCat.of R))).X
  let q := snd Z (Gm (Spec (CommRingCat.of R))).X
  let v := Gm.pointsEquiv _ W q
  have hchi : q ≫ (AffineRegularBorel.cocharacter i wt).hom.hom =
      cocharPoint wt W v ≫ i.hom.hom := by
    rw [cocharPoint_eq_comp, MulEquiv.symm_apply_apply, Category.assoc]
    rfl
  change Dynamic.orbit (AffineRegularBorel.cocharacter i wt) (rootPoint (fam a) Z c) = _
  rw [Dynamic.orbit, hchi]
  simp only [comp_rootPoint]
  rw [hu a, torusChar_cocharPoint, ha]
  simp [W]

/-- Every all-test point of a zero-pairing root map lies in the actual
centralizer functor. -/
theorem range_root_le_centralizer_of_zero
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (ha : coPairing (ch a) wt = 0) :
    SubgroupFunctor.range (fam a) ≤
      Dynamic.centralizer (AffineRegularBorel.cocharacter i wt) := by
  rintro Z _ ⟨x, rfl⟩
  change x ≫ (fam a).hom.hom ∈ _
  simpa only [rootPoint, VectorGroup.scalarPoint_coordinate] using
    rootPoint_mem_centralizer_of_zero hu wt a ha Z
      ((VectorGroup.coordinates (CommRingCat.of R) 1 Z x).toAdd 0)

/-- An actual zero-weight root map into the affine centralizer representative. -/
def rootToAffineCentralizer
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (ha : coPairing (ch a) wt = 0) :
    Ga R ⟶ Dynamic.Affine.centralizerScheme (AffineRegularBorel.cocharacter i wt) :=
  (Dynamic.Affine.isRepresentedBy_centralizerHom
    (AffineRegularBorel.cocharacter i wt)).factorHom (fam a)
      (range_root_le_centralizer_of_zero hu wt a ha)

/-- The zero-weight root factor retains its exact original ambient map. -/
theorem rootToAffineCentralizer_comp
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (ha : coPairing (ch a) wt = 0) :
    rootToAffineCentralizer hu wt a ha ≫
      Dynamic.Affine.centralizerHom (AffineRegularBorel.cocharacter i wt) = fam a :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- Nonnegative root pairings give parabolic membership, including zero roots. -/
theorem rootPoint_mem_parabolic_of_nonneg
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (ha : 0 ≤ coPairing (ch a) wt)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (fam a) Z c ∈
      (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).carrier Z := by
  by_cases hp : 0 < coPairing (ch a) wt
  · exact Dynamic.unipotent_le_parabolic _ Z (rootPoint_mem_unipotent hu wt a hp Z c)
  · exact Dynamic.centralizer_le_parabolic _ Z
      (rootPoint_mem_centralizer_of_zero hu wt a (by omega) Z c)

/-- Negating coordinate exponents is the actual opposite cocharacter. -/
theorem cocharacter_neg_eq_opposite (wt : I → ℤ) :
    AffineRegularBorel.cocharacter i (-wt) =
      Dynamic.oppositeCocharacter (AffineRegularBorel.cocharacter i wt) := by
  have hneg : splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-wt) =
      - splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I wt := by
    simp only [splitTorus.exponentCocharacter, Pi.neg_apply, neg_smul,
      Finset.sum_neg_distrib]
  change CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-wt)) ≫ i =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I wt) ≫ i)
  rw [← Category.assoc]
  change CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-wt)) ≫ i =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫
      splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I wt) ≫ i
  rw [hneg]
  simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]

/-- A genuine root parametrization over a nontrivial ring has a nonidentity
point at the global function one on the original base. -/
theorem rootPoint_one_ne_one [Nontrivial R] (a : J)
    (hfam : IsRootParametrization i (ch a) (fam a)) :
    rootPoint (fam a) (Over.mk (𝟙 (Spec (CommRingCat.of R)))) 1 ≠ 1 := by
  intro h
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 (Spec (CommRingCat.of R)))
  let : Mono (fam a).hom.hom := hfam.represents.1
  have hs : VectorGroup.scalarPoint (CommRingCat.of R) Z 1 =
      VectorGroup.scalarPoint (CommRingCat.of R) Z 0 := by
    apply (cancel_mono (fam a).hom.hom).mp
    exact h.trans (rootPoint_zero (fam a) Z).symm
  have hc := congrArg (fun x => (VectorGroup.coordinates (CommRingCat.of R) 1 Z x).toAdd 0) hs
  simp only [VectorGroup.coordinates_scalarPoint] at hc
  have hR : (1 : R) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of R)).hom c) hc
  exact one_ne_zero hR

/-- Positive pairing is detected by the actual all-test root range inside
the contracting functor, without passing to geometric fibres. -/
theorem coPairing_pos_iff_range_root_le_unipotent [Nontrivial R]
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ) (a : J)
    (hfam : IsRootParametrization i (ch a) (fam a)) :
    0 < coPairing (ch a) wt ↔
      SubgroupFunctor.range (fam a) ≤
        Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) := by
  constructor
  · exact range_root_le_unipotent hu wt a
  · intro hroot
    by_contra hn
    let Z : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 (Spec (CommRingCat.of R)))
    let g := rootPoint (fam a) Z 1
    have hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).carrier Z :=
      hroot Z (SubgroupFunctor.mem_range.mpr
        ⟨VectorGroup.scalarPoint (CommRingCat.of R) Z 1, rfl⟩)
    have hp : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter i (-wt))).carrier Z :=
      rootPoint_mem_parabolic_of_nonneg hu (-wt) a
        (by simpa only [coPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] using
          neg_nonneg.mpr (le_of_not_gt hn)) Z 1
    have hm : g ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (AffineRegularBorel.cocharacter i (-wt)))).carrier Z := by
      rw [← cocharacter_neg_eq_opposite]
      simpa only [neg_neg] using hg
    exact rootPoint_one_ne_one a hfam
      (Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic _ hm hp)

/-- Equal actual contracting functors give the same strictly positive root
pairings for every genuine root parametrization. -/
theorem coPairing_pos_iff_of_unipotent_eq [Nontrivial R]
    (hu : TorusEquivariant i ch fam) (wt wt' : I → ℤ)
    (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
      Dynamic.unipotent (AffineRegularBorel.cocharacter i wt'))
    (a : J) (hfam : IsRootParametrization i (ch a) (fam a)) :
    0 < coPairing (ch a) wt ↔ 0 < coPairing (ch a) wt' := by
  rw [coPairing_pos_iff_range_root_le_unipotent hu wt a hfam,
    coPairing_pos_iff_range_root_le_unipotent hu wt' a hfam, hU]

end Langlands.GroupScheme.LocalSplitCell
