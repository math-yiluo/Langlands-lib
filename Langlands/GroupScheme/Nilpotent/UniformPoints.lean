import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Uniform nilpotence from geometric nilpotence -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IteratedCommutator

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- If a later universal word vanishes, every earlier word value lies in
the corresponding upper central term of every point group. -/
theorem word_mem_upperCentralSeries_of_word_eq_one
    (m n : ℕ) (h : word G (n + m) = 1)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ source G n) :
    v ≫ word G n ∈ Subgroup.upperCentralSeries (T ⟶ G.X) m := by
  induction m generalizing n with
  | zero =>
    rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot]
    rw [Nat.add_zero] at h
    rw [h, MonObj.comp_one]
  | succ m ih =>
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    have hm : word G (n + 1 + m) = 1 := by
      rw [show n + 1 + m = n + (m + 1) by omega]
      exact h
    have hv := ih (n + 1) hm (lift v y)
    simpa only [word_succ_points, lift_fst, lift_snd] using hv

/-- A universal word identity gives a single lower central bound on every
relative test scheme, including nonreduced tests. -/
theorem hasUniformNilpotentPoints_of_word_eq_one
    {d : ℕ} (h : word G d = 1) : HasUniformNilpotentPoints G d := by
  intro T
  apply Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top.2
  apply top_unique
  intro x _
  have hx := word_mem_upperCentralSeries_of_word_eq_one d 0
    (by rw [Nat.zero_add]; exact h) x
  simpa only [word, Category.comp_id] using hx

end IteratedCommutator

section GeometricPoints

variable {k : Type u} [Field k]

private theorem hom_ext_geometricPoints
    {X Y : Over (Spec (CommRingCat.of k))}
    [GeometricallyReduced X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p :
      (Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ⟶ X,
      p ≫ f = p ≫ g) : f = g := by
  let b := toAlgebraicClosure k
  have hb := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Flat b := hb.2.1
  have : Surjective b := hb.1
  have : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of k)),
      Epi (pullback.fst z b) := fun Z z => by
    exact Flat.epi_of_flat_of_surjective _
  let F := Over.pullback b
  have : F.Faithful := inferInstance
  apply F.map_injective
  have hK : ∀ p : Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
      F.obj X, p ≫ F.map f = p ≫ F.map g := by
    intro p
    apply ((Over.mapPullbackAdj b).homEquiv _ Y).symm.injective
    change ((Over.mapPullbackAdj b).homEquiv _ Y).symm
        (p ≫ (Over.pullback b).map f) =
      ((Over.mapPullbackAdj b).homEquiv _ Y).symm
        (p ≫ (Over.pullback b).map g)
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_right_symm]
    exact h (((Over.mapPullbackAdj b).homEquiv _ X).symm p)
  have : IsReduced (F.obj X).left :=
    GeometricallyReduced.geometrically_isReduced b _ _ (.of_hasPullback X.hom b)
  have : LocallyOfFiniteType (F.obj X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom b)
    infer_instance
  have : IsSeparated (F.obj Y).hom := by
    change IsSeparated (pullback.snd Y.hom b)
    infer_instance
  have : JacobsonSpace (F.obj X).left :=
    LocallyOfFiniteType.jacobsonSpace (F.obj X).hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq (F.map f).left (F.map g).left
    (F.obj Y).hom (closedPoints (F.obj X).left) ?_ ?_ ?_
  · rw [dense_iff_closure_eq]
    exact closure_closedPoints
  · intro x hx
    let p : Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ F.obj X :=
      Over.homMk (pointOfClosedPoint (F.obj X).hom x hx)
        (pointOfClosedPoint_comp (F.obj X).hom x hx)
    have hp := congrArg (fun q => q.left) (hK p)
    change (Spec.map (residueFieldIsoBase (F.obj X).hom x hx).hom ≫
        (F.obj X).left.fromSpecResidueField x) ≫ (F.map f).left =
      (Spec.map (residueFieldIsoBase (F.obj X).hom x hx).hom ≫
        (F.obj X).left.fromSpecResidueField x) ≫ (F.map g).left at hp
    apply (cancel_epi (Spec.map (residueFieldIsoBase (F.obj X).hom x hx).hom)).mp
    simpa only [Category.assoc] using hp
  · exact (Over.w (F.map f)).trans (Over.w (F.map g)).symm

end GeometricPoints

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- For a smooth connected affine group, nilpotence of geometric points
gives a nilpotence bound uniform over all relative scheme tests. -/
theorem IsNilpotentGroupScheme.exists_hasUniformNilpotentPoints
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) : ∃ d, HasUniformNilpotentPoints G d := by
  let P := (Over.map (toAlgebraicClosure k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  let e := baseChangePointsEquiv (toAlgebraicClosure k) G
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  have hP : Group.IsNilpotent (P ⟶ G.X) := (Group.isNilpotent_congr e).1 hG
  obtain ⟨d, hd⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hP
  refine ⟨d, IteratedCommutator.hasUniformNilpotentPoints_of_word_eq_one ?_⟩
  have hgood := IteratedCommutator.source_good (G := G) d
  have : GeometricallyReduced (IteratedCommutator.source G d).hom := hgood.2.2.1
  have : LocallyOfFiniteType (IteratedCommutator.source G d).hom := hgood.2.1
  apply hom_ext_geometricPoints
  intro p
  have hp := IteratedCommutator.word_mem_lowerCentralSeries G d p
  rw [hd, Subgroup.mem_bot] at hp
  simpa only [MonObj.comp_one] using hp

/-- A chosen finite lower-central bound, valid uniformly on all relative
scheme tests of a smooth connected affine geometrically nilpotent group. -/
def IsNilpotentGroupScheme.uniformNilpotenceBound
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) : ℕ :=
  Classical.choose hG.exists_hasUniformNilpotentPoints

/-- The chosen bound applies also to nonreduced relative test schemes. -/
theorem IsNilpotentGroupScheme.uniformNilpotenceBound_spec
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) :
    HasUniformNilpotentPoints G hG.uniformNilpotenceBound :=
  Classical.choose_spec hG.exists_hasUniformNilpotentPoints

end Langlands.GroupScheme
