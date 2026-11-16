import Langlands.GroupScheme.Reductive.RootFactorCellOpen
import Langlands.GroupScheme.Reductive.RelativeRootGroupFibre
import Langlands.GroupScheme.Reductive.RelativeTorusCommutator
import Langlands.GroupScheme.Reductive.OpenCellFppfGeneration
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # The open cell from actual relative dynamic root groups -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.RelativeRootDynamicCell

open LocalRootGroup LocalSplitCell RootFactorCell RelativeDerived

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A fixed integral cocharacter isolating the specified pair of opposite roots. -/
def isolatingExponent (hP : IsFibrewiseRootDatumOf I G i P) (a : J) :
    {mu : I → ℤ // ∑ j, P.root a j * mu j = 0 ∧
      ∀ b : J, ∑ j, P.root b j * mu j = 0 →
        P.root b = P.root a ∨ P.root b = -P.root a} := by
  let : Finite J := hP.finite
  let : P.IsReduced := hP.isReduced
  exact ⟨(exists_kernel_exponent P (ULift.{u} ℚ) a).choose,
    (exists_kernel_exponent P (ULift.{u} ℚ) a).choose_spec⟩

/-- The actual smooth dynamic root group for the chosen isolated root. -/
abbrev rootFactor (hP : IsFibrewiseRootDatumOf I G i P) (a : J) :
    GroupScheme (Spec (CommRingCat.of R)) :=
  Uc i (isolatingExponent hP a).val (P.coroot a)

/-- Its actual homomorphism into the original group. -/
def rootInclusion (hP : IsFibrewiseRootDatumOf I G i P) (a : J) : rootFactor hP a ⟶ G :=
  incl i (isolatingExponent hP a).val (P.coroot a)

omit [DecidableEq I] in
/-- Every chosen factor is smooth, including over nonreduced rings. -/
theorem smooth_rootFactor (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J) : Smooth (rootFactor hP a).X.hom := by
  have : Smooth G.X.hom := hG.smooth
  exact smooth_Uc i (isolatingExponent hP a).val (P.coroot a)

omit [DecidableEq I] in
/-- On every supplied field fibre, the actual factors have additive coordinates
whose ambient maps are exactly the prescribed root parametrizations. -/
theorem exists_fieldRootCoordinates (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (K : Type u) [Field K] [Algebra R K] :
    ∃ e : ∀ a, Ga K ≅ (GroupScheme.baseChange (algebraBaseMap R K)).obj (rootFactor hP a),
      ∀ a, IsRootParametrization (splitTorus.baseChangeHom (K := K) G I i) (P.root a)
        ((e a).hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (rootInclusion hP a)) := by
  classical
  choose e he using fun a => exists_rootFibreParametrization i (isolatingExponent hP a).val K
    hG hmax hP a (isolatingExponent hP a).property.1 (isolatingExponent hP a).property.2
  refine ⟨e, fun a => ?_⟩
  have h := he a
  rw [fibreRootMap_eq] at h
  exact h

variable {m n : ℕ} (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base)
    (neg : Fin m ≃ {a // ¬ bs.IsPos a}) (pos : Fin n ≃ {a // bs.IsPos a})

/-- The actual dynamic-factor cell source, with the coordinate torus in the middle. -/
abbrev cellGroup : GroupScheme (Spec (CommRingCat.of R)) :=
  sourceGroup (fun r => rootFactor hP (neg r : J))
    (splitTorus (Spec (CommRingCat.of R)) I) (fun r => rootFactor hP (pos r : J))

/-- Its ordered multiplication into the original ambient group. -/
def cell : (cellGroup hP bs neg pos).X ⟶ G.X :=
  RootFactorCell.multiplication _ _ _ (fun r => rootInclusion hP (neg r : J)) i
    (fun r => rootInclusion hP (pos r : J))

omit [DecidableEq I] in
/-- The actual dynamic root-factor cell is open over every affine base ring. -/
theorem isOpenImmersion_cell (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    IsOpenImmersion (cell hP bs neg pos).left := by
  apply isOpenImmersion_multiplication_of_fieldCoordinates hG hmax hP bs neg pos
    (fun r => rootFactor hP (neg r : J)) (fun r => rootFactor hP (pos r : J))
    (fun r => rootInclusion hP (neg r : J)) (fun r => rootInclusion hP (pos r : J))
    (fun r => smooth_rootFactor hG hP (neg r : J))
    (fun r => smooth_rootFactor hG hP (pos r : J))
  intro K _ _
  obtain ⟨e, he⟩ := exists_fieldRootCoordinates hG hmax hP K
  exact ⟨(fun a => (e a).hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
      (rootInclusion hP a)), (fun r => e (neg r : J)), (fun r => e (pos r : J)),
    he, fun _ => rfl, fun _ => rfl⟩

end Langlands.GroupScheme.RelativeRootDynamicCell

namespace Langlands.GroupScheme.RelativeRootDynamicCell

open LocalRootGroup LocalSplitCell RootFactorCell RelativeDerived

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Local commutator membership of the actual dynamic root-factor values
suffices for all points of the split relative semisimple group. -/
theorem locallyCommutator_of_rootValues (hG : IsReductive G)
    (hss : ∀ s, IsSemisimple (geometricFiber G s)) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hroot : ∀ a (Z : Over (Spec (CommRingCat.of R))) (p : Z ⟶ (rootFactor hP a).X),
      LocallyCommutator (p ≫ (rootInclusion hP a).hom.hom))
    (Z : Over (Spec (CommRingCat.of R))) (x : Z ⟶ G.X) : LocallyCommutator x := by
  classical
  have : Finite J := hP.finite
  have : P.IsReduced := hP.isReduced
  let bs : P.Base := Langlands.LinearAlgebra.RootDatumBase.base P
  let neg := (Finite.equivFin {a // ¬ bs.IsPos a}).symm
  let pos := (Finite.equivFin {a // bs.IsPos a}).symm
  let Ω := cell hP bs neg pos
  have : IsOpenImmersion Ω.left := isOpenImmersion_cell hP bs neg pos hG hmax
  apply locallyCommutator_of_open_unit_cell hG Ω
    (range_unit_subset_multiplication
      (fun r => rootInclusion hP (neg r : J)) i (fun r => rootInclusion hP (pos r : J)))
  · intro W p
    exact locallyCommutator_multiplication
      (fun r => rootInclusion hP (neg r : J)) i (fun r => rootInclusion hP (pos r : J))
      (fun r => hroot (neg r : J)) (locallyCommutator_torus hG hss hi hP)
      (fun r => hroot (pos r : J)) W p

end Langlands.GroupScheme.RelativeRootDynamicCell
