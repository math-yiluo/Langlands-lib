import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.Geometry
import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.PointRigidity
import Langlands.GroupScheme.Absolute.TriangularCharacterKernelDescent
import Langlands.GroupScheme.Reductive.RelativeRootCommutatorMap
import Langlands.GroupScheme.SemidirectProduct
import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.AutomorphicAction.SectionCoordinateModel
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.NoetherianSpace

/-! # The commutator and fixed subgroup of semisimple conjugation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.SemisimpleCentralizer

section Stabilization

variable {k : Type u} [Field k] {N : GroupScheme (Spec (CommRingCat.of k))}

private def iterateHom (d : N ⟶ N) : ℕ → (N ⟶ N)
  | 0 => 𝟙 N
  | n + 1 => iterateHom d n ≫ d

private theorem iterateHom_succ (d : N ⟶ N) (m : ℕ) :
    iterateHom d (m + 1) = d ≫ iterateHom d m := by
  induction m with
  | zero => simp [iterateHom]
  | succ m ih =>
      change (iterateHom d (m + 1) ≫ d) = d ≫ (iterateHom d m ≫ d)
      rw [ih, Category.assoc]

private theorem point_iterateHom (d : N ⟶ N) (m : ℕ) (x : rationalPoints N) :
    rationalPoints.map (iterateHom d m) x = (rationalPoints.map d)^[m] x := by
  induction m with
  | zero => simp [iterateHom, rationalPoints.map_apply]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ← ih]
      simp only [iterateHom, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

variable [IsAlgClosed k] [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]

/-- A group endomorphism whose square has the same rational kernel as itself
splits every rational point as an image point times a kernel point. -/
theorem exists_image_mul_kernel (d : N ⟶ N)
    (hsep : ∀ x : rationalPoints N, rationalPoints.map d (rationalPoints.map d x) = 1 →
      rationalPoints.map d x = 1) (x : rationalPoints N) :
    ∃ y v : rationalPoints N, rationalPoints.map d v = 1 ∧ rationalPoints.map d y * v = x := by
  have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  have : IsLocallyNoetherian N.X.left := LocallyOfFiniteType.isLocallyNoetherian N.X.hom
  have : NoetherianSpace N.X.left := noetherianSpace_of_isAffine
  let images : ℕ → Closeds N.X.left := fun n =>
    ⟨Set.range (iterateHom d n).hom.hom.left, isClosed_range (iterateHom d n)⟩
  have himages : Antitone images := antitone_nat_of_succ_le fun m => by
    change Set.range (iterateHom d (m + 1)).hom.hom.left ⊆
      Set.range (iterateHom d m).hom.hom.left
    rw [iterateHom_succ]
    rintro _ ⟨z, rfl⟩
    exact ⟨d.hom.hom.left z, rfl⟩
  obtain ⟨m, hm⟩ := WellFoundedLT.antitone_chain_condition himages
  have heq : images (m + 1) = images (m + 2) :=
    (hm (m + 1) (by omega)).symm.trans (hm (m + 2) (by omega))
  have hx : (rationalPoints.map (iterateHom d (m + 1)) x).left (IsLocalRing.closedPoint k) ∈
      images (m + 2) := by
    rw [← heq]
    exact ⟨x.left (IsLocalRing.closedPoint k), rfl⟩
  obtain ⟨y, hy⟩ := DominantHom.rational_lift (iterateHom d (m + 2))
    (rationalPoints.map (iterateHom d (m + 1)) x) hx
  let f := rationalPoints.map d
  have hkill (n : ℕ) (z : rationalPoints N) (hz : f^[n + 1] z = 1) : f z = 1 := by
    induction n generalizing z with
    | zero => exact hz
    | succ n ih =>
        apply hsep z
        apply ih (f z)
        rwa [← Function.iterate_succ_apply]
  let v := (f y)⁻¹ * x
  have hv : f^[m + 1] v = 1 := by
    rw [← point_iterateHom, map_mul, map_inv, point_iterateHom, point_iterateHom,
      ← Function.iterate_succ_apply]
    have hy' : (rationalPoints.map (iterateHom d (m + 2))) y =
        (rationalPoints.map (iterateHom d (m + 1))) x := hy
    rw [point_iterateHom, point_iterateHom] at hy'
    rw [hy', inv_mul_cancel]
  exact ⟨y, v, hkill m v hv, mul_inv_cancel_left _ _⟩

end Stabilization

section Commutator

variable {S : Scheme.{u}} {N G : GroupScheme S} [IsCommMonObj N.X]
  (i : N ⟶ G) [Mono i.hom.hom] (hi : (SubgroupFunctor.range i).IsNormal)
  (s : Over.mk (𝟙 S) ⟶ G.X)

/-- The section commutator on a normal commutative subgroup is a group endomorphism. -/
def commutatorHom : N ⟶ N := by
  let a := LinearKernelTower.normalConjugation i hi
  have : IsMonHom (a.commutatorMap s) := by
    apply Semidirect.isMonHom_of_mul_comp
    intro T x y
    rw [AutomorphicAction.commutatorMap_apply, AutomorphicAction.commutatorMap_apply,
      AutomorphicAction.commutatorMap_apply, a.act_mul_right, mul_inv_rev]
    ac_rfl
  exact Grp.homMk (a.commutatorMap s)

/-- Applying the inclusion to the commutator endomorphism computes the ambient commutator. -/
theorem commutatorHom_apply {T : Over S} (x : T ⟶ N.X) :
    (x ≫ (commutatorHom i hi s).hom.hom) ≫ i.hom.hom = ⁅toUnit T ≫ s, x ≫ i.hom.hom⁆ := by
  change (x ≫ (LinearKernelTower.normalConjugation i hi).commutatorMap s) ≫ i.hom.hom = _
  rw [AutomorphicAction.commutatorMap_apply, MonObj.mul_comp, GrpObj.inv_comp,
    LinearKernelTower.normalConjugation_comp, commutatorElement_def]
  rfl

/-- The full scheme kernel of the endomorphism is the centralizer in the normal subgroup. -/
theorem range_kernel_commutatorHom :
    SubgroupFunctor.range (kernelι (commutatorHom i hi s)) = (G.pointCentralizer s).comap i := by
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap, G.mem_pointCentralizer]
  have he := commutatorHom_apply i hi s x
  constructor
  · intro h
    have hcomm : ⁅toUnit T ≫ s, x ≫ i.hom.hom⁆ = 1 := by
      rw [← he, h, MonObj.one_comp]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  · intro h
    apply (cancel_mono i.hom.hom).mp
    rw [he, MonObj.one_comp, commutatorElement_eq_one_iff_mul_comm]
    exact h.symm

end Commutator

section FixedKernel

variable {k : Type u} [Field k] [IsAlgClosed k]
  {N G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom] [IsCommMonObj N.X]
  (i : N ⟶ G) [Mono i.hom.hom] (hi : (SubgroupFunctor.range i).IsNormal)
  (s : rationalPoints G)

omit [IsAlgClosed k] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom] in
/-- On rational points, the ambient commutator is the usual group commutator. -/
theorem commutator_point_map (x : rationalPoints N) :
    rationalPoints.map i (rationalPoints.map (commutatorHom i hi s) x) =
      ⁅s, rationalPoints.map i x⁆ := by
  have h := commutatorHom_apply i hi s x
  rw [toUnit_unique (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (𝟙 _), Category.id_comp] at h
  exact h

private theorem commutator_image_eq_one_of_fixed (hN : IsUnipotent N)
    (hs : SemisimplePoint.IsSemisimple s) (x : rationalPoints N)
    (hx : rationalPoints.map (commutatorHom i hi s)
      (rationalPoints.map (commutatorHom i hi s) x) = 1) :
    rationalPoints.map (commutatorHom i hi s) x = 1 := by
  let v := rationalPoints.map (commutatorHom i hi s) x
  let X := rationalPoints.map i x
  let V := rationalPoints.map i v
  have hxv : ⁅s, X⁆ = V := (commutator_point_map i hi s x).symm
  have hcomm : Commute s V := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← commutator_point_map i hi s v, hx, map_one]
  have hvx : Commute V X := (Commute.all v x).map (rationalPoints.map i)
  have he : s * V = X⁻¹ * s * (X⁻¹)⁻¹ := by
    calc
      s * V = V * s := hcomm.eq
      _ = X⁻¹ * V * X * s := by rw [mul_assoc X⁻¹ V X, hvx.eq, inv_mul_cancel_left]
      _ = X⁻¹ * s * (X⁻¹)⁻¹ := by rw [← hxv, commutatorElement_def]; group
  have hprod : SemisimplePoint.IsSemisimple (s * V) := by
    rw [he]
    exact SemisimplePoint.conj hs X⁻¹
  have hV : V = 1 := SemisimplePoint.eq_one_of_commute_of_mul i hN v hs hcomm hprod
  apply (cancel_mono i.hom.hom).mp
  change v ≫ i.hom.hom = 1 ≫ i.hom.hom
  rw [MonObj.one_comp]
  exact hV

/-- Over an algebraically closed field a commutator with a semisimple point has enough
image to cover every point of a normal commutative unipotent subgroup with its kernel. -/
theorem commutator_point_cover (hN : IsUnipotent N) (hs : SemisimplePoint.IsSemisimple s)
    (x : rationalPoints N) : ∃ y v : rationalPoints N,
      rationalPoints.map (commutatorHom i hi s) v = 1 ∧
        rationalPoints.map (commutatorHom i hi s) y * v = x :=
  exists_image_mul_kernel _ (commutator_image_eq_one_of_fixed i hi s hN hs) x

private def commutativeProductHom {M F : GroupScheme (Spec (CommRingCat.of k))}
    (j : M ⟶ N) (l : F ⟶ N) : (Grp.mk (M.X ⊗ F.X) : GroupScheme _) ⟶ N := by
  have : IsMonHom (subgroupMultiplication j l) := by
    apply Semidirect.isMonHom_of_mul_comp
    intro T x y
    simp only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc,
      MonObj.mul_comp]
    ac_rfl
  exact Grp.homMk (subgroupMultiplication j l)

/-- The full fixed subgroup in a connected normal commutative unipotent subgroup is connected. -/
theorem connectedSpace_kernel_commutatorHom [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hs : SemisimplePoint.IsSemisimple s) :
    ConnectedSpace (kernel (commutatorHom i hi s)).X.left := by
  let d := commutatorHom i hi s
  let F := kernel d
  let l := kernelι d
  have hl : IsClosedSubgroup l := kernelι_isClosedImmersion d
  have : LocallyOfFiniteType F.X.hom := hl.locallyOfFiniteType
  have : IsAffineHom F.X.hom := hl.isAffineHom
  obtain ⟨M, p, j, hMft, hMaff, hj, hpj, hp⟩ := affineHomImage k N N d
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom M.X.hom := hMaff
  have : LocallyOfFiniteType M.X.hom := hMft
  let P : GroupScheme (Spec (CommRingCat.of k)) := Grp.mk (M.X ⊗ F.X)
  let m : P ⟶ N := commutativeProductHom j l
  have : LocallyOfFiniteType P.X.hom := by
    change LocallyOfFiniteType (M.X ⊗ F.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsAffineHom P.X.hom :=
    AutomorphicAction.SectionCoordinateModel.isAffineHom_tensor M.X F.X
  have hm : Function.Surjective (rationalPoints.map m) := by
    intro x
    obtain ⟨y, v, hv, hyv⟩ := commutator_point_cover i hi s hN hs x
    obtain ⟨w, hw⟩ := (mem_range_kernelι_iff d v).2 hv
    change Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ F.X at w
    change w ≫ l.hom.hom = v at hw
    refine ⟨lift (rationalPoints.map p y) w, ?_⟩
    change lift (rationalPoints.map p y) w ≫ subgroupMultiplication j l = x
    rw [comp_subgroupMultiplication, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      hpj, hw]
    exact hyv
  have hker : ConnectedSpace (kernel m).X.left := by
    have hcl : IsClosedSubgroup (kernelι m) := kernelι_isClosedImmersion m
    have : LocallyOfFiniteType (kernel m).X.hom := hcl.locallyOfFiniteType
    apply connectedSpace_of_points_eq_one
    intro a
    let z := rationalPoints.map (kernelι m) a
    let t : rationalPoints M := z ≫ fst M.X F.X
    let w : rationalPoints F := z ≫ snd M.X F.X
    obtain ⟨y, hy⟩ := rationalPoints.map_surjective_of_surjective p hp.2.1 t
    have htz : t ≫ j.hom.hom = rationalPoints.map d y := by
      rw [← hy, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, hpj]
      rfl
    have hw : rationalPoints.map d (w ≫ l.hom.hom) = 1 :=
      (mem_range_kernelι_iff d _).mp ⟨w, rfl⟩
    have hz : rationalPoints.map m z = 1 := (mem_range_kernelι_iff m _).mp ⟨a, rfl⟩
    have hprod : rationalPoints.map d y * (w ≫ l.hom.hom) = 1 := by
      change z ≫ subgroupMultiplication j l = 1 at hz
      simp only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc] at hz
      change (t ≫ j.hom.hom) * (w ≫ l.hom.hom) = 1 at hz
      rwa [htz] at hz
    have hdd : rationalPoints.map d (rationalPoints.map d y) = 1 := by
      have h := congrArg (rationalPoints.map d) hprod
      rwa [map_mul, hw, mul_one, map_one] at h
    have hd : rationalPoints.map d y = 1 := commutator_image_eq_one_of_fixed i hi s hN hs y hdd
    have ht1 : t = 1 := by
      apply (cancel_mono j.hom.hom).1
      rw [htz, MonObj.one_comp, hd]
    have hw1 : w = 1 := by
      apply (cancel_mono l.hom.hom).1
      rw [hd, one_mul] at hprod
      rw [hprod, MonObj.one_comp]
    apply (cancel_mono (kernelι m).hom.hom).1
    rw [MonObj.one_comp]
    change z = 1
    apply CartesianMonoidalCategory.hom_ext
    · exact ht1.trans (MonObj.one_comp (fst M.X F.X)).symm
    · exact hw1.trans (MonObj.one_comp (snd M.X F.X)).symm
  have : ConnectedSpace P.X.left := connectedSpace_of_rational_surjective m hm hker
  let sectionMap : F.X ⟶ M.X ⊗ F.X := lift 1 (𝟙 _)
  have hsurj : Surjective (snd M.X F.X).left := by
    have hsec : sectionMap ≫ snd M.X F.X = 𝟙 F.X := lift_snd _ _
    have : Surjective (sectionMap.left ≫ (snd M.X F.X).left) := by
      rw [← Over.comp_left, hsec]
      infer_instance
    exact Surjective.of_comp sectionMap.left _
  exact hsurj.surj.connectedSpace (snd M.X F.X).left.continuous

end FixedKernel

end Langlands.GroupScheme.SemisimpleCentralizer
