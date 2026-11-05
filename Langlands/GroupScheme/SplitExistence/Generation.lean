import Langlands.GroupScheme.SplitExistence.SchemeGroup
import Langlands.GroupScheme.SplitExistence.RationalProducts
import Langlands.GroupScheme.SplitExistence.Subgroups
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.GroupScheme.Rational.VectorGroupDimension

/-! # The Chevalley group as a smooth connected closed subgroup of `GL_n`

Starting from the torus `D(X) ⊆ GL_n`, we adjoin the root groups one at a time with the
Library's pointed image generation. Every stage is a smooth, affine, connected closed subgroup
of `GL_n`, and its points with values in any algebraically closed extension of `k` lie in the
abstract Chevalley group `Γ`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) (k : Type u) [Field k]

/-- The points of `GL_n` on a test scheme whose matrix lies in the abstract Chevalley group
over the global sections. -/
def chevPoints (T : Over (Spec (CommRingCat.of k))) : Subgroup (T ⟶ (D.GLk k).X) :=
  (D.chevSub Γ(T.left, ⊤)).comap
    (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T).toMonoidHom

theorem mem_chevPoints {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ (D.GLk k).X} :
    x ∈ D.chevPoints k T ↔
      GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T x ∈ D.chevSub Γ(T.left, ⊤) :=
  Iff.rfl

theorem torus_mem_chevPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    x ≫ (D.torusToGL k).hom.hom ∈ D.chevPoints k T := by
  rw [mem_chevPoints, pointsEquiv_torusToGL]
  exact Subgroup.mem_sup_left (torusHom_mem_torusSub _)

theorem root_mem_chevPoints (j : J) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gak k).X) :
    x ≫ (D.rootToGL k j).hom.hom ∈ D.chevPoints k T := by
  rw [mem_chevPoints, pointsEquiv_rootToGL]
  exact Subgroup.mem_sup_right (rootSub_le_rootsSub (Set.mem_univ j) (x_mem_rootSub j _))

/-- A stage of the construction: a smooth, affine, connected closed subgroup of `GL_n` whose
points with values in every algebraically closed extension of `k` lie in `Γ`. -/
structure Stage where
  /-- The group. -/
  H : GroupScheme (Spec (CommRingCat.of k))
  /-- The closed embedding into `GL_n`. -/
  i : H ⟶ D.GLk k
  smooth : Smooth H.X.hom
  affine : IsAffineHom H.X.hom
  connected : ConnectedSpace H.X.left
  closed : IsClosedSubgroup i
  points : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (x : extPoint K ⟶ H.X),
    x ≫ i.hom.hom ∈ D.chevPoints k (extPoint K)

/-- The initial stage: the torus. -/
def baseStage (hT : IsSplitTorus (Tk (X := X) k).toGrp) : D.Stage k where
  H := (Tk (X := X) k).toGrp
  i := D.torusToGL k
  smooth := hT.smooth
  affine := Langlands.GroupScheme.Diagonalizable.isAffineHom _ _
  connected := hT.connectedSpace
  closed := D.isClosedSubgroup_torusToGL k hT
  points _ _ _ _ x := D.torus_mem_chevPoints k _ x

theorem gak_geometry : Smooth (Gak k).X.hom ∧ IsAffineHom (Gak k).X.hom ∧
    ConnectedSpace (Gak k).X.left := by
  refine ⟨?_, ?_, ?_⟩
  · have : SmoothOfRelativeDimension 1 (Gak k).X.hom := VectorGroup.smoothOfRelativeDimension _ _
    exact SmoothOfRelativeDimension.smooth 1 _
  · change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
    infer_instance

/-- Adjoining one root group to a stage. -/
theorem Stage.exists_step (s : D.Stage k) (j : J) :
    ∃ s' : D.Stage k, FactorsThrough s.i.hom.hom s'.i ∧
      FactorsThrough (D.rootToGL k j).hom.hom s'.i := by
  have := s.smooth
  have := s.affine
  have := s.connected
  have hGL : Smooth (D.GLk k).X.hom := Langlands.GroupScheme.GeneralLinear.smoothStatement _ _
  have hGLa : IsAffineHom (D.GLk k).X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  obtain ⟨hGa, hGaa, hGac⟩ := gak_geometry k
  have hgeom := smoothConnectedAffineGeometry.2 k s.H (Gak k) s.smooth s.affine s.connected
    hGa hGaa hGac
  let f : s.H.X ⊗ (Gak k).X ⟶ (D.GLk k).X :=
    (fst s.H.X (Gak k).X ≫ s.i.hom.hom) * (snd s.H.X (Gak k).X ≫ (D.rootToGL k j).hom.hom)
  let v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ s.H.X ⊗ (Gak k).X := lift 1 1
  have hv₀ : v₀ ≫ f = 1 := by
    simp only [v₀, f]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, MonObj.one_comp,
      MonObj.one_comp, mul_one]
  obtain ⟨E, hEs, hEa, hEc, n, -, hdom⟩ := ImageGeneration.pointedImageGeneration k (D.GLk k)
    hGL hGLa (s.H.X ⊗ (Gak k).X) hgeom.1 hgeom.2.1 hgeom.2.2.2 v₀ f hv₀
  have hEconn : ConnectedSpace E.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := E.group.X.hom)
  refine ⟨⟨E.group, E.inclusion, hEs, hEa, hEconn, E.closed, ?_⟩, ?_, ?_⟩
  · intro K _ _ _ x
    have := hEs
    have := hEa
    have : GeometricallyIntegral E.group.X.hom :=
      Langlands.AbelianScheme.smoothGeometricIntegrality k _ _ hEs hEc
    have hV := ImageGeneration.finitePowerGood_finitePower _
      (ImageGeneration.finitePowerGood_of_geometricallyIntegral _ hgeom.1 hgeom.2.1
        hgeom.2.2.2) n
    have : IsAffineHom (finitePower (s.H.X ⊗ (Gak k).X) n).hom := hV.1
    have : LocallyOfFiniteType (finitePower (s.H.X ⊗ (Gak k).X) n).hom := hV.2.1
    have : IsDominant (E.powerMap n).left := hdom
    obtain ⟨a, b, hab⟩ := exists_mul_of_isDominant K (E.powerMap n) x
    have hfac : ∀ c : extPoint K ⟶ s.H.X ⊗ (Gak k).X, c ≫ f ∈ D.chevPoints k (extPoint K) := by
      intro c
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
      exact Subgroup.mul_mem _ (s.points K _) (D.root_mem_chevPoints k j _ _)
    have hprod : ∀ c : extPoint K ⟶ finitePower (s.H.X ⊗ (Gak k).X) n,
        (c ≫ E.powerMap n) ≫ E.inclusion.hom.hom ∈ D.chevPoints k (extPoint K) := by
      intro c
      rw [E.powerMap_comp_points, orderedPowerMap_points]
      refine Subgroup.list_prod_mem _ ?_
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact hfac _
    rw [hab, MonObj.mul_comp]
    exact Subgroup.mul_mem _ (hprod a) (hprod b)
  · refine ⟨lift (𝟙 s.H.X) 1 ≫ E.factor, ?_⟩
    rw [Category.assoc, E.factor_comp]
    simp only [f]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, MonObj.one_comp,
      Category.id_comp, mul_one]
  · refine ⟨lift 1 (𝟙 (Gak k).X) ≫ E.factor, ?_⟩
    rw [Category.assoc, E.factor_comp]
    simp only [f]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, MonObj.one_comp,
      Category.id_comp, one_mul]

/-- Adjoining a list of root groups to a stage. -/
theorem Stage.exists_steps (s : D.Stage k) (l : List J) :
    ∃ s' : D.Stage k, FactorsThrough s.i.hom.hom s'.i ∧
      ∀ j ∈ l, FactorsThrough (D.rootToGL k j).hom.hom s'.i := by
  induction l generalizing s with
  | nil => exact ⟨s, ⟨𝟙 _, Category.id_comp _⟩, by simp⟩
  | cons j l ih =>
    obtain ⟨s₁, h₁, hj⟩ := s.exists_step D k j
    obtain ⟨s₂, h₂, hl⟩ := ih s₁
    have htrans : ∀ {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ (D.GLk k).X),
        FactorsThrough g s₁.i → FactorsThrough g s₂.i := by
      intro W g ⟨c, hc⟩
      obtain ⟨d, hd⟩ := h₂
      exact ⟨c ≫ d, by rw [Category.assoc, hd, hc]⟩
    refine ⟨s₂, htrans _ h₁, ?_⟩
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact htrans _ hj
    · exact hl j' hj'

/-- **The Chevalley group.** A smooth, affine, connected closed subgroup of `GL_n` containing the
torus and all root groups, whose geometric points lie in the abstract Chevalley group. -/
theorem exists_chevalley_stage [Finite J] (hT : IsSplitTorus (Tk (X := X) k).toGrp) :
    ∃ s : D.Stage k, FactorsThrough (D.torusToGL k).hom.hom s.i ∧
      ∀ j, FactorsThrough (D.rootToGL k j).hom.hom s.i := by
  have := Fintype.ofFinite J
  obtain ⟨s, hs, hl⟩ := (D.baseStage k hT).exists_steps D k Finset.univ.toList
  exact ⟨s, hs, fun j => hl j (Finset.mem_toList.2 (Finset.mem_univ j))⟩

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
