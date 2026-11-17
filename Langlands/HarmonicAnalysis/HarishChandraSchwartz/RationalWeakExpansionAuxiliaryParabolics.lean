import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLowerGeometry
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.Dynamic.NestedParabolic
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison
import Langlands.GroupScheme.Rational.NestedStandardTransport

/-! # The auxiliary ambient parabolics in the weak-expansion c-family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz.WeakExpansion

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem torusCocharacter_commutes (α β : cocharacterLattice T) :
    SubgroupFunctor.range (CommGroupScheme.groupHom β ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) := by
  intro X g hg
  apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom α) X
  apply range_le_torusCentralizer i X
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact SubgroupFunctor.mem_range.mpr
    ⟨t ≫ (CommGroupScheme.groupHom β).hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩

/-- A coefficient for a dominant combination, chosen from the published
finite-type coordinate-algebra construction. -/
def auxiliaryMultiplicity (α β : cocharacterLattice T) : ℕ :=
  (Dynamic.exists_dominant_inclusions
    (CommGroupScheme.groupHom α ≫ i) (CommGroupScheme.groupHom β ≫ i)
    (torusCocharacter_commutes i α β)).choose

/-- A cocharacter refining the outer parabolic while retaining the inner
cocharacter's action on the outer Levi. -/
def auxiliaryCocharacter (α β : cocharacterLattice T) : cocharacterLattice T :=
  (auxiliaryMultiplicity i α β : ℤ) • α + β

private theorem auxiliaryCocharacter_inclusions (α β : cocharacterLattice T) :
    Dynamic.parabolic (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i) ∧
    Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) ∧
    Dynamic.centralizer (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) ≤
        Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) := by
  have hN := (Dynamic.exists_dominant_inclusions
    (CommGroupScheme.groupHom α ≫ i) (CommGroupScheme.groupHom β ≫ i)
    (torusCocharacter_commutes i α β)).choose_spec
  refine hN (auxiliaryMultiplicity i α β : ℤ) le_rfl
    (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) ?_
  intro X t
  simp only [auxiliaryCocharacter, Grp.comp_hom_hom, ← Category.assoc,
    comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp, GrpObj.zpow_comp]

/-- The centralizer is the intersection of the two original centralizers;
the parabolic and radical have the dominant inclusions on every test scheme. -/
theorem auxiliaryCocharacter_spec (α β : cocharacterLattice T) :
    Dynamic.centralizer (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) =
        Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) ⊓
          Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) ∧
    Dynamic.parabolic (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i) ∧
    Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) := by
  obtain ⟨hP, hU, hZ⟩ := auxiliaryCocharacter_inclusions i α β
  refine ⟨le_antisymm ?_ ?_, hP, hU⟩
  · intro X g hg
    have hα := hZ X hg
    refine ⟨hα, ?_⟩
    have hsum : auxiliaryCocharacter i α β ∈ Dynamic.centralizingCocharacters i g := hg
    have hmul := (Dynamic.centralizingCocharacters i g).smul_mem
      (auxiliaryMultiplicity i α β : ℤ) hα
    have hsub := (Dynamic.centralizingCocharacters i g).sub_mem hsum hmul
    change β ∈ Dynamic.centralizingCocharacters i g
    simpa only [auxiliaryCocharacter, add_sub_cancel_left] using hsub
  · intro X g hg
    exact (Dynamic.centralizingCocharacters i g).add_mem
      ((Dynamic.centralizingCocharacters i g).smul_mem
        (auxiliaryMultiplicity i α β : ℤ) hg.1) hg.2

/-- On the outer Levi, the auxiliary and inner cocharacters act identically. -/
theorem auxiliaryCocharacter_orbit (α β : cocharacterLattice T)
    {X : Over (Spec (CommRingCat.of F))} {g : X ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).carrier X) :
    Dynamic.orbit (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i) g =
      Dynamic.orbit (CommGroupScheme.groupHom β ≫ i) g := by
  rw [auxiliaryCocharacter, add_comm]
  exact Dynamic.orbit_add_zsmul_of_mem_centralizer i β α _ hg

variable (ν : cocharacterLattice T) (I I' : Set (characterLattice T))

/-- The torus cocharacter defining `P_s = (M' ∩ sP) U'`. -/
def cParabolicCocharacter (ζ' ζ : cocharacterLattice T) (n : normalizerPoints i) :
    cocharacterLattice T :=
  auxiliaryCocharacter i ζ' (conjugatedCocharacter i ζ n)

/-- The torus cocharacter defining `P̃_s = (M' ∩ sP) Ū'`. -/
def cOppositeParabolicCocharacter (ζ' ζ : cocharacterLattice T)
    (n : normalizerPoints i) : cocharacterLattice T :=
  auxiliaryCocharacter i (-ζ') (conjugatedCocharacter i ζ n)

/-- Both signs of an outer cocharacter give the same inner centralizer and
the actual lower parabolic after pullback. The full ambient product formulas
are retained through `extendFromCentralizer`. -/
theorem auxiliaryParabolic_geometry (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν I ζ)
    (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I')
    (α : cocharacterLattice T)
    (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) =
      standardLevi i ν I') :
    let β := conjugatedCocharacter i ζ n
    let ψ := CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i
    let χ' := CommGroupScheme.groupHom α ≫ i
    let j := Standard.leviHom i ν I'
    let hj : (Dynamic.centralizer χ').IsRepresentedBy j :=
      hα.symm ▸ Standard.isRepresentedBy_leviHom i ν I'
    Dynamic.centralizer ψ = Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) ∧
    Dynamic.IsCompatibleNestedPair ψ χ' ∧
    (Dynamic.parabolic ψ).comap j = lowerParabolic i ν I I' n ∧
    Dynamic.parabolic ψ =
      Dynamic.extendFromCentralizer χ' j hj (lowerParabolic i ν I I' n) ∧
    Dynamic.unipotent ψ =
      Dynamic.extendFromCentralizer χ' j hj (lowerUnipotent i ν I I' n) := by
  dsimp only
  let β := conjugatedCocharacter i ζ n
  let ψ := CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i
  let χ' := CommGroupScheme.groupHom α ≫ i
  let j := Standard.leviHom i ν I'
  have hj : (Dynamic.centralizer χ').IsRepresentedBy j := by
    rw [show χ' = CommGroupScheme.groupHom α ≫ i from rfl, hα]
    exact Standard.isRepresentedBy_leviHom i ν I'
  have hβ := conjugatedCocharacter_dynamic i ν I hG hi hν hI ζ hζ n
  have hβle : Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) ≤
      Dynamic.centralizer χ' := by
    rw [show χ' = CommGroupScheme.groupHom α ≫ i from rfl, hα, hβ.2.1]
    exact hn
  have haux := auxiliaryCocharacter_spec i α β
  have hsame : Dynamic.centralizer ψ =
      Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) := by
    refine haux.1.trans ?_
    apply SubgroupFunctor.ext
    intro X
    exact inf_eq_right.mpr (hβle X)
  have hOrbit : ∀ (X : Over (Spec (CommRingCat.of F)))
      (l : X ⟶ (lowerAmbient i ν I').X),
      Dynamic.orbit ψ (l ≫ j.hom.hom) =
        Dynamic.orbit (lowerCocharacter i ν I' ζ n ≫ j) (l ≫ j.hom.hom) := by
    intro X l
    have hl : l ≫ j.hom.hom ∈ (Dynamic.centralizer χ').carrier X := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨l, rfl⟩
    have hc : lowerCocharacter i ν I' ζ n ≫ j =
        CommGroupScheme.groupHom β ≫ i := by
      change (CommGroupScheme.groupHom β ≫ Standard.leviTorusHom i ν I') ≫ j = _
      rw [Category.assoc, Standard.leviTorusHom_comp]
    rw [hc]
    exact auxiliaryCocharacter_orbit i α β hl
  have hlow := lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n
  have hprod := Dynamic.realization_of_inclusions χ' j hj
    (lowerCocharacter i ν I' ζ n) ψ hOrbit
    (Standard.isClosedSubgroup_leviHom i ν I') haux.2.1 haux.2.2
    (hsame.le.trans hβle)
  refine ⟨hsame, ?_, ?_, ?_, ?_⟩
  · exact Dynamic.isCompatibleNestedPair_of_torus i hi _ _ haux.2.1
      (hsame.le.trans hβle)
  · exact (Dynamic.parabolic_comap_eq_of_orbit j
      (lowerCocharacter i ν I' ζ n) ψ hOrbit
      (Standard.isClosedSubgroup_leviHom i ν I')).trans hlow.1
  · exact hprod.1.trans (congrArg (Dynamic.extendFromCentralizer χ' j hj) hlow.1)
  · exact hprod.2.2.trans
      (congrArg (Dynamic.extendFromCentralizer χ' j hj) hlow.2.2)

/-- The positive auxiliary parabolic has inducing Levi `sM`, restricts to the
actual lower parabolic in `M'`, and is compatible with the outer parabolic. -/
theorem cParabolicCocharacter_spec (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (hI' : I' ⊆ simpleRelativeRoots i ν)
    (ζ ζ' : cocharacterLattice T) (hζ : IsStandardCocharacter i ν I ζ)
    (hζ' : IsStandardCocharacter i ν I' ζ') (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I') :
    let ψ := CommGroupScheme.groupHom (cParabolicCocharacter i ζ' ζ n) ≫ i
    Dynamic.centralizer ψ =
        Dynamic.centralizer (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) ∧
    Dynamic.IsCompatibleNestedPair ψ (CommGroupScheme.groupHom ζ' ≫ i) ∧
    (Dynamic.parabolic ψ).comap (Standard.leviHom i ν I') =
      lowerParabolic i ν I I' n := by
  have hα := ((standardCocharacter F G hG T i hi ν hν I' hI').2 ζ' hζ').2.1.symm
  have h := auxiliaryParabolic_geometry i ν I I' hG hi hν hI ζ hζ n hn ζ' hα
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The negative auxiliary parabolic has the same inducing Levi and lower
pullback and is compatible with the opposite outer parabolic. -/
theorem cOppositeParabolicCocharacter_spec (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (hI' : I' ⊆ simpleRelativeRoots i ν)
    (ζ ζ' : cocharacterLattice T) (hζ : IsStandardCocharacter i ν I ζ)
    (hζ' : IsStandardCocharacter i ν I' ζ') (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I') :
    let ψ := CommGroupScheme.groupHom (cOppositeParabolicCocharacter i ζ' ζ n) ≫ i
    Dynamic.centralizer ψ =
        Dynamic.centralizer (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) ∧
    Dynamic.IsCompatibleNestedPair ψ (CommGroupScheme.groupHom (-ζ') ≫ i) ∧
    (Dynamic.parabolic ψ).comap (Standard.leviHom i ν I') =
      lowerParabolic i ν I I' n := by
  have hα : Dynamic.centralizer (CommGroupScheme.groupHom (-ζ') ≫ i) =
      standardLevi i ν I' := by
    rw [Dynamic.centralizer_groupHom_neg]
    exact ((standardCocharacter F G hG T i hi ν hν I' hI').2 ζ' hζ').2.1.symm
  have h := auxiliaryParabolic_geometry i ν I I' hG hi hν hI ζ hζ n hn (-ζ') hα
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
