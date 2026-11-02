import Langlands.Geometry.Building.SplitTorusValuation
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Renard's uniformizer subgroup and its positive part -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Evaluate actual cocharacters at the existing order-one uniformizer. -/
def uniformizerSection :
    Multiplicative (cocharacterLattice T) →* rationalPoints T.toGrp where
  toFun c := rationalPoints.map (CommGroupScheme.groupHom c.toAdd)
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
      (SplitTorusValuation.uniformizerUnit F))
  map_one' := comp_groupHom_zero _
  map_mul' c d := comp_groupHom_add _ c.toAdd d.toAdd

/-- Renard's subgroup `C_A`, mapped into an actual ambient algebraic group.
For the minimal Levi, take the map from the chosen maximal split torus into
its actual algebraic centralizer. -/
def C0 {H : GroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ H) :
    Subgroup (rationalPoints H) :=
  ((rationalPoints.map i).comp (uniformizerSection T)).range

/-- Nonnegative cocharacters for the specified set of actual torus characters. -/
def nonnegativeCocharacters (positiveRoots : Set (characterLattice T)) :
    Set (cocharacterLattice T) :=
  {c | ∀ a ∈ positiveRoots, 0 ≤ latticePairing T a c}

/-- Renard's `C_0^+`: uniformizer powers with nonnegative positive-root orders.
The ambient Cartan application uses the actual positive relative roots. -/
def C0Plus {H : GroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ H)
    (positiveRoots : Set (characterLattice T)) : Set (rationalPoints H) :=
  (fun c : cocharacterLattice T =>
    rationalPoints.map i (uniformizerSection T (Multiplicative.ofAdd c))) ''
      nonnegativeCocharacters T positiveRoots

theorem mem_C0 {H : GroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ H)
    (h : rationalPoints H) :
    h ∈ C0 T i ↔ ∃ c : cocharacterLattice T,
      rationalPoints.map i (uniformizerSection T (Multiplicative.ofAdd c)) = h := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.toAdd, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨Multiplicative.ofAdd c, hc⟩

theorem mem_C0Plus {H : GroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ H)
    (positiveRoots : Set (characterLattice T)) (h : rationalPoints H) :
    h ∈ C0Plus T i positiveRoots ↔ ∃ c : cocharacterLattice T,
      (∀ a ∈ positiveRoots, 0 ≤ latticePairing T a c) ∧
      rationalPoints.map i (uniformizerSection T (Multiplicative.ofAdd c)) = h :=
  Iff.rfl

theorem C0Plus_subset_C0 {H : GroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ H) (positiveRoots : Set (characterLattice T)) :
    C0Plus T i positiveRoots ⊆ (C0 T i : Set (rationalPoints H)) := by
  rintro h ⟨c, _, hc⟩
  exact (mem_C0 T i h).mpr ⟨c, hc⟩

/-- The generic evaluation specializes definitionally to the published
cocharacter evaluation for a coordinate split torus. -/
theorem uniformizerSection_splitTorus (I : Type u) [Finite I]
    (c : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I)) :
    uniformizerSection (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I)
        (Multiplicative.ofAdd c) =
      SplitTorusValuation.cocharacterPoints F I c (SplitTorusValuation.uniformizerUnit F) :=
  rfl

end Langlands.Plancherel.RenardCartan
