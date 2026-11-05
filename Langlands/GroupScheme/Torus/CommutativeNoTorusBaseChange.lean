import Langlands.GroupScheme.Torus.GeometricCocharacterVanishing
import Langlands.GroupScheme.Torus.CocharacterSpecialization
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Absence of tori in commutative groups under arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CocharacterDatum

variable {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥)

include hZ

/-- If all base-field torus maps into an affine finite type commutative group vanish,
all its cocharacters over every extension field vanish. -/
theorem gm_hom_eq_zero_of_no_torus
    (K : Type u) [Field K] [Algebra k K]
    (f : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z).toGrp) : f = 0 := by
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  let Zbar := (CommGroupScheme.baseChange (toAlgebraicClosure k)).obj Z
  have : IsAffine Zbar.toGrp.X.left := by
    change IsAffine (pullback Z.toGrp.X.hom (toAlgebraicClosure k))
    infer_instance
  have : LocallyOfFiniteType Zbar.toGrp.X.hom := by
    change LocallyOfFiniteType (pullback.snd Z.toGrp.X.hom (toAlgebraicClosure k))
    infer_instance
  have hbar : ∀ g : (Gm (Spec (CommRingCat.of (AlgebraicClosure k)))).toGrp ⟶
      Zbar.toGrp, g = 0 :=
    gm_hom_eq_zero_over_algebraicClosure hZ
  let e := (algebraicClosureBaseChangeIso k K).app Z.toGrp
  let fbar := (Gm.baseChangeIso (toAlgebraicClosure K)).inv ≫
    (GroupScheme.baseChange (toAlgebraicClosure K)).map f
  have hzero : fbar ≫ e.inv = 0 :=
    CocharacterSpecialization.gm_hom_eq_zero_of_baseField
      (G := Zbar.toGrp) (AlgebraicClosure K) hbar (fbar ≫ e.inv)
  have hfbar : fbar = 0 := by
    apply (cancel_mono e.inv).mp
    simpa only [zero_comp] using hzero
  apply GaloisCocharacterDescent.baseChangeCocharacter_injective K (AlgebraicClosure K) _
  simpa only [GaloisCocharacterDescent.baseChangeCocharacter, Functor.map_zero, comp_zero]
    using hfbar

/-- The absence of homomorphisms from tori to an affine finite type commutative group
is preserved by every field extension. -/
theorem torus_hom_eq_zero_of_no_torus
    (K : Type u) [Field K] [Algebra k K]
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (hT : IsTorus T.toGrp)
    (f : T.toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z).toGrp) : f = 0 := by
  classical
  obtain ⟨L, _, _, hTL⟩ := hT
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let b := algebraBaseMap K L
  let eZ := baseChangeFieldTowerIso k K L Z.toGrp
  obtain ⟨I, _, ⟨eT⟩⟩ := hTL
  let : Fintype I := Fintype.ofFinite I
  let g : splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj Z :=
    Additive.ofMul (eT.inv ≫ (GroupScheme.baseChange b).map f ≫ eZ.inv)
  have hcoord (i : I) :
      splitTorus.single (Spec (CommRingCat.of L)) I i ≫ g = 0 := by
    change CommGroupScheme.groupHom
      (splitTorus.single (Spec (CommRingCat.of L)) I i ≫ g) = 0
    exact gm_hom_eq_zero_of_no_torus hZ L _
  have hg : g = 0 := by
    calc
      g = (𝟙 _) ≫ g := (Category.id_comp g).symm
      _ = (∑ i, splitTorus.proj (Spec (CommRingCat.of L)) I i ≫
          splitTorus.single (Spec (CommRingCat.of L)) I i) ≫ g := by
        rw [splitTorus.sum_proj_comp_single]
      _ = 0 := by
        rw [Preadditive.sum_comp]
        simp only [Category.assoc, hcoord, comp_zero, Finset.sum_const_zero]
  have hfL : (GroupScheme.baseChange b).map f = 0 := by
    have hg' := congrArg CommGroupScheme.groupHom hg
    change eT.inv ≫ (GroupScheme.baseChange b).map f ≫ eZ.inv = 0 at hg'
    apply (cancel_mono eZ.inv).mp
    apply (cancel_epi eT.inv).mp
    simpa only [Category.assoc, zero_comp, comp_zero] using hg'
  let := GaloisCocharacterDescent.faithful_algebraPullback K L
  apply (GroupScheme.baseChange b).map_injective
  simpa only [Functor.map_zero] using hfL

/-- Every torus map to the base change has bottom image on every test scheme. -/
theorem range_eq_bot_of_no_torus
    (K : Type u) [Field K] [Algebra k K]
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (hT : IsTorus T.toGrp)
    (f : T.toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z).toGrp) :
    SubgroupFunctor.range f = ⊥ := by
  rw [torus_hom_eq_zero_of_no_torus hZ K T hT f, SubgroupFunctor.range_zero]

end CocharacterDatum

end Langlands.GroupScheme
