import Langlands.GroupScheme.RelativeLevi.SplitBorelDynamicProjection
import Langlands.GroupScheme.RelativeLevi.SplitBorelUnipotentCommutator
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # Positive-root chart data for the actual contracting group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Actual positive-root coordinates and height bounds on one regular contracting group. -/
structure SplitBorelPositiveChart where
  cocharacter : I → ℤ
  regular : ∀ a : J, coPairing (P.root a) cocharacter ≠ 0
  dimension : ℕ
  roots : ULift.{u} (Fin dimension) →
    (Ga R ⟶ AffineRegularBorel.contractingGroup i cocharacter)
  height : Fin dimension → ℕ
  height_pos : ∀ k, 0 < height k
  chart : (VectorGroup.groupScheme (CommRingCat.of R) dimension).X ≅
    (AffineRegularBorel.contractingGroup i cocharacter).X
  formula : ∀ (Z : Over (Spec (CommRingCat.of R)))
    (x : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of R) dimension).X),
    x ≫ chart.hom = (List.ofFn fun k =>
      rootPoint (roots (ULift.up k)) Z
        ((VectorGroup.coordinates (CommRingCat.of R) dimension Z x).toAdd k)).prod
  commutator : ∀ (Z : Over (Spec (CommRingCat.of R))) (k l : Fin dimension),
    ⁅rootFactor roots ULift.up Z k, rootFactor roots ULift.up Z l⁆ ≤
      HeightFiltration.level (rootFactor roots ULift.up Z) height (height k + height l)

variable {i P}

set_option maxHeartbeats 800000 in
/-- Supplied actual root parametrizations give positive chart data over every
commutative ring, with no choice of a Borel or series as input. -/
theorem nonempty_splitBorelPositiveChart
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (fam : J → (Ga R ⟶ G))
    (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a)) :
    Nonempty (SplitBorelPositiveChart i P) := by
  classical
  let : Finite J := hP.finite
  let : P.IsReduced := hP.isReduced
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  let neg := (Finite.equivFin {a // ¬ b.IsPos a}).symm
  let pos := (Finite.equivFin {a // b.IsPos a}).symm
  let n := Nat.card {a // b.IsPos a}
  let hTE : TorusEquivariant i (fun a => P.root a) fam :=
    fun a Z t c => (hfam a).equivariant Z t c
  let := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  have hpos (k : Fin n) : 0 < coPairing (P.root (pos k)) ν :=
    hνpos _ (pos k).property
  have hneg (k : Fin (Nat.card {a // ¬ b.IsPos a})) :
      coPairing (P.root (neg k)) ν < 0 :=
    hνneg _ (neg k).property
  let w : Fin n → ℕ := fun k => (coPairing (P.root (pos k)) ν).toNat
  have hw (k : Fin n) : coPairing (P.root (pos k)) ν = (w k : ℤ) :=
    (Int.toNat_of_nonneg (hpos k).le).symm
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom (AffineRegularBorel.contractingGroup i ν).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i ν
  let : IsAffine (AffineRegularBorel.contractingGroup i ν).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i ν).X.hom
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i ν)
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom
    (AffineRegularBorel.cocharacter i ν)
  refine ⟨{
    cocharacter := ν
    regular := ?_
    dimension := n
    roots := liftedPositiveRootToUnipotent j hTE ν hU hpos
    height := w
    height_pos := ?_
    chart := positiveProductIso j hTE ν hU hneg hpos
    formula := ?_
    commutator := commutator_unipotent_rootFactor_le j hTE ν hU hpos hneg w hw
  }⟩
  · intro a
    by_cases ha : b.IsPos a
    · exact ne_of_gt (hνpos a ha)
    · exact ne_of_lt (hνneg a ha)
  · intro k
    have hk := hpos k
    rw [hw k] at hk
    exact_mod_cast hk
  · intro Z x
    exact comp_positiveProductIso_hom j hTE ν hU hneg hpos x

end Langlands.GroupScheme
