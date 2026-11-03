import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Elementary reductions for the endpoints of standard parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Zero

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- The zero cocharacter stays trivial after any group homomorphism. -/
theorem groupHom_zero_comp_eq_trivialCocharacter (i : T.toGrp ⟶ G) :
    CommGroupScheme.groupHom (0 : cocharacterLattice T) ≫ i =
      Dynamic.trivialCocharacter G := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero,
    MonObj.one_comp, Dynamic.comp_trivialCocharacter]

/-- A central cocharacter has trivial dynamic unipotent subgroup when limits are unique. -/
theorem Dynamic.unipotent_eq_bot_of_centralizer_eq_top [IsSeparated G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (hχ : Dynamic.centralizer χ = ⊤) :
    Dynamic.unipotent χ = ⊥ := by
  apply SubgroupFunctor.ext
  intro U
  change (Dynamic.unipotent χ).carrier U = ⊥
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  have hz : g ∈ (Dynamic.centralizer χ).carrier U := by
    rw [hχ]
    exact Subgroup.mem_top g
  exact (Dynamic.hasLimit_of_mem_centralizer χ hz).unique χ hg

@[simp] theorem Dynamic.unipotent_trivialCocharacter [IsSeparated G.X.hom] :
    Dynamic.unipotent (Dynamic.trivialCocharacter G) = ⊥ :=
  Dynamic.unipotent_eq_bot_of_centralizer_eq_top _
    (Dynamic.centralizer_trivialCocharacter G)

end Zero

section Endpoints

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The cocharacter specifying positivity is standard for the empty index. -/
theorem isStandardCocharacter_empty_self : IsStandardCocharacter i ν ∅ ν := by
  refine ⟨Set.empty_subset _, ?_, ?_⟩
  · simp
  · intro α hα _
    exact hα.1.2

/-- The zero cocharacter is standard for the full simple-root index. -/
theorem isStandardCocharacter_simple_zero :
    IsStandardCocharacter i ν (simpleRelativeRoots i ν) 0 := by
  refine ⟨Set.Subset.rfl, ?_, ?_⟩
  · intro α _
    exact map_zero (latticePairing T α)
  · intro α hα hnot
    exact False.elim (hnot hα)

/-- The canonical standard-cocharacter witness at the empty index. -/
def standardEmptyCocharacter :
    Subtype (fun m : cocharacterLattice T => IsStandardCocharacter i ν ∅ m) :=
  ⟨ν, isStandardCocharacter_empty_self i ν⟩

/-- The canonical standard-cocharacter witness at the full simple-root index. -/
def standardFullCocharacter :
    Subtype (fun m : cocharacterLattice T =>
      IsStandardCocharacter i ν (simpleRelativeRoots i ν) m) :=
  ⟨0, isStandardCocharacter_simple_zero i ν⟩

@[simp] theorem standardEmptyCocharacter_val : (standardEmptyCocharacter i ν).val = ν := rfl

@[simp] theorem standardFullCocharacter_val : (standardFullCocharacter i ν).val = 0 := rfl

/-- The empty-index parabolic is contained in the specified dynamic parabolic. -/
theorem standardParabolic_empty_le :
    standardParabolic i ν ∅ ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
  standardParabolic_le_dynamicParabolic i ν (standardEmptyCocharacter i ν).property

/-- The empty-index Levi is contained in the specified dynamic centralizer. -/
theorem standardLevi_empty_le :
    standardLevi i ν ∅ ≤ Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) :=
  standardLevi_le_dynamicCentralizer i ν (standardEmptyCocharacter i ν).property

/-- Identification of the specified dynamic centralizer gives the empty-index Levi. -/
theorem standardLevi_empty_of_genericCentralizer
    (hν : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i) :
    standardLevi i ν ∅ = torusCentralizer i := by
  apply le_antisymm
  · rw [← hν]
    exact standardLevi_empty_le i ν
  · exact torusCentralizer_le_standardLevi i ν ∅

/-- The full-index unipotent intersection is trivial, already for an affine group scheme. -/
theorem standardUnipotent_simple_eq_bot :
    standardUnipotent i ν (simpleRelativeRoots i ν) = ⊥ := by
  apply SubgroupFunctor.ext
  intro U
  change (standardUnipotent i ν (simpleRelativeRoots i ν)).carrier U = ⊥
  apply le_antisymm _ bot_le
  have h := standardUnipotent_le_dynamicUnipotent i ν
    (standardFullCocharacter i ν).property
  rw [standardFullCocharacter_val, groupHom_zero_comp_eq_trivialCocharacter,
    Dynamic.unipotent_trivialCocharacter] at h
  exact h U

end Endpoints

/-- The two structural statement families imply all five exact endpoint clauses.
The structural arguments remain explicit premises of this reduction. -/
theorem standardParabolicEndpoints_of_genericCentralizer_of_standardCocharacter
    (hcentralizer : GenericCentralizerStatement.{u})
    (hstandard : StandardCocharacterStatement.{u}) :
    StandardParabolicEndpointsStatement.{u} := by
  intro k _ G hG T i hi ν hν
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  have hempty := (hstandard k G hG T i hi ν hν ∅ (Set.empty_subset _)).2
    ν (isStandardCocharacter_empty_self i ν)
  have hfull := (hstandard k G hG T i hi ν hν _ Set.Subset.rfl).2
    0 (isStandardCocharacter_simple_zero i ν)
  refine ⟨hempty.1, ?_, ?_, ?_, standardUnipotent_simple_eq_bot i ν⟩
  · exact standardLevi_empty_of_genericCentralizer i ν (hcentralizer k G hG T i hi ν hν)
  · simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.parabolic_trivialCocharacter] using hfull.1
  · simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.centralizer_trivialCocharacter] using hfull.2.1

end Langlands.GroupScheme
