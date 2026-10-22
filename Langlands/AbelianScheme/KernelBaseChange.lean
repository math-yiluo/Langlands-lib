import Langlands.AbelianScheme.Kernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme
universe u
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : Grp (Over S)}

private instance baseChange_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (Over.pullback b).mapGrp := by
  have : PreservesLimitsOfShape WalkingCospan
      ((Over.pullback b).mapGrp ⋙ Grp.forget (Over S')) :=
    (inferInstance : PreservesLimitsOfShape WalkingCospan
      (Grp.forget (Over S) ⋙ Over.pullback b))
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (Over.pullback b).mapGrp (Grp.forget (Over S'))

private def baseChangeTrivialIso :
    (Over.pullback b).mapGrp.obj (Grp.trivial (Over S)) ≅ Grp.trivial (Over S') :=
  (Functor.Monoidal.εIso (Over.pullback b).mapGrp).symm

private lemma baseChange_kernelUnit :
    (Over.pullback b).mapGrp.map (kernelUnit H) =
      (baseChangeTrivialIso b).hom ≫ kernelUnit ((Over.pullback b).mapGrp.obj H) := by
  apply (cancel_epi (baseChangeTrivialIso b).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  exact Subsingleton.elim _ _

/-- The canonical comparison between base change of a kernel and the kernel after base change. -/
def kernelBaseChangeIso (f : G ⟶ H) :
    (Over.pullback b).mapGrp.obj (kernel f) ≅
      kernel ((Over.pullback b).mapGrp.map f) :=
  PreservesPullback.iso (Over.pullback b).mapGrp f (kernelUnit H) ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) (baseChangeTrivialIso b).hom (𝟙 _)
      (by simp) (by simpa using baseChange_kernelUnit (H := H) b))

@[reassoc (attr := simp)]
lemma kernelBaseChangeIso_hom_ι (f : G ⟶ H) :
    (kernelBaseChangeIso b f).hom ≫ kernelι ((Over.pullback b).mapGrp.map f) =
      (Over.pullback b).mapGrp.map (kernelι f) := by
  simp [kernelBaseChangeIso, kernelι, Category.assoc]

@[reassoc (attr := simp)]
lemma kernelBaseChangeIso_inv_ι (f : G ⟶ H) :
    (kernelBaseChangeIso b f).inv ≫ (Over.pullback b).mapGrp.map (kernelι f) =
      kernelι ((Over.pullback b).mapGrp.map f) := by
  rw [← kernelBaseChangeIso_hom_ι b f, Iso.inv_hom_id_assoc]

/-- Compatibility with inclusion uniquely characterizes the comparison morphism. -/
lemma kernelBaseChangeIso_hom_unique (f : G ⟶ H)
    (g : (Over.pullback b).mapGrp.obj (kernel f) ⟶
      kernel ((Over.pullback b).mapGrp.map f))
    (hg : g ≫ kernelι ((Over.pullback b).mapGrp.map f) =
      (Over.pullback b).mapGrp.map (kernelι f)) :
    g = (kernelBaseChangeIso b f).hom := by
  apply Grp.hom_ext
  apply (cancel_mono (kernelι ((Over.pullback b).mapGrp.map f)).hom.hom).mp
  change (g ≫ kernelι ((Over.pullback b).mapGrp.map f)).hom.hom =
    ((kernelBaseChangeIso b f).hom ≫
      kernelι ((Over.pullback b).mapGrp.map f)).hom.hom
  rw [hg, kernelBaseChangeIso_hom_ι]

/-- The usual pullback adjunction on points, with its multiplicative structure. -/
def baseChangePointsEquiv (G : Grp (Over S)) (T : Over S') :
    (T ⟶ ((Over.pullback b).mapGrp.obj G).X) ≃*
      ((Over.map b).obj T ⟶ G.X) where
  __ := ((Over.mapPullbackAdj b).homEquiv T G.X).symm
  map_mul' x y := by
    change T ⟶ Over.mk (pullback.snd G.X.hom b) at x y
    have hx : x.left ≫ pullback.snd G.X.hom b = T.hom := x.w
    have hy : y.left ≫ pullback.snd G.X.hom b = T.hom := y.w
    apply Over.OverMorphism.ext
    change ((lift x y).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback b) G.X G.X).left ≫
        ((Over.pullback b).map μ[G.X]).left) ≫ pullback.fst G.X.hom b =
      pullback.lift (x.left ≫ pullback.fst G.X.hom b)
        (y.left ≫ pullback.fst G.X.hom b)
        (by
          calc
            (x.left ≫ pullback.fst G.X.hom b) ≫ G.X.hom = T.hom ≫ b := by
              rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
            _ = (y.left ≫ pullback.fst G.X.hom b) ≫ G.X.hom := by
              rw [Category.assoc, pullback.condition, ← Category.assoc, hy]) ≫
          μ[G.X].left
    simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · have h := Over.μ_pullback_left_fst_fst (f := b) G.X G.X
      simp only [Category.assoc] at h ⊢
      rw [h]
      simp
    · have h := Over.μ_pullback_left_fst_snd (f := b) G.X G.X
      simp only [Category.assoc] at h ⊢
      rw [h]
      simp

@[simp]
lemma baseChangePointsEquiv_left (G : Grp (Over S)) (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    (baseChangePointsEquiv b G T x).left = x.left ≫ pullback.fst G.X.hom b := rfl

lemma baseChangePointsEquiv_comp (f : G ⟶ H) (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    baseChangePointsEquiv b H T (x ≫ ((Over.pullback b).mapGrp.map f).hom.hom) =
      baseChangePointsEquiv b G T x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  change (x ≫ (Over.pullback b).map f.hom.hom).left ≫ pullback.fst H.X.hom b =
    (x.left ≫ pullback.fst G.X.hom b) ≫ f.hom.hom.left
  simp [Category.assoc]

/-- The pullback point equivalence is natural in the test scheme. -/
lemma baseChangePointsEquiv_naturality (G : Grp (Over S))
    {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    baseChangePointsEquiv b G T' (a ≫ x) =
      (Over.map b).map a ≫ baseChangePointsEquiv b G T x := by
  apply Over.OverMorphism.ext
  change (a.left ≫ x.left) ≫ pullback.fst G.X.hom b =
    a.left ≫ x.left ≫ pullback.fst G.X.hom b
  exact Category.assoc _ _ _

/-- Pullback adjunction restricted to the actual pointwise kernel subgroups. -/
def baseChangeKernelPointsEquiv (f : G ⟶ H) (T : Over S') :
    (((yonedaGrp.map ((Over.pullback b).mapGrp.map f)).app (.op T)).hom.ker) ≃*
      (((yonedaGrp.map f).app (.op ((Over.map b).obj T))).hom.ker) where
  toFun x := ⟨baseChangePointsEquiv b G T x.val, by
    change baseChangePointsEquiv b G T x.val ≫ f.hom.hom = 1
    rw [← baseChangePointsEquiv_comp b f T,
      show x.val ≫ ((Over.pullback b).mapGrp.map f).hom.hom = 1 from x.property,
      map_one]⟩
  invFun x := ⟨(baseChangePointsEquiv b G T).symm x.val, by
    change (baseChangePointsEquiv b G T).symm x.val ≫
      ((Over.pullback b).mapGrp.map f).hom.hom = 1
    apply (baseChangePointsEquiv b H T).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, map_one]
    exact x.property⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((baseChangePointsEquiv b G T).map_mul x.val y.val)

/-- The equivalence of pointwise kernel subgroups is natural in the test scheme. -/
lemma baseChangeKernelPointsEquiv_naturality (f : G ⟶ H)
    {T T' : Over S'} (a : T' ⟶ T)
    (x : (((yonedaGrp.map ((Over.pullback b).mapGrp.map f)).app (.op T)).hom.ker)) :
    baseChangeKernelPointsEquiv b f T'
      (kernelPointsRestrict ((Over.pullback b).mapGrp.map f) a x) =
      kernelPointsRestrict f ((Over.map b).map a) (baseChangeKernelPointsEquiv b f T x) :=
  Subtype.ext (baseChangePointsEquiv_naturality b G a x.val)

/-- The comparison respects the canonical kernel identification on every test scheme. -/
lemma kernelBaseChangeIso_points (f : G ⟶ H) (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (kernel f)).X) :
    baseChangeKernelPointsEquiv b f T
      (kernelPointsEquiv ((Over.pullback b).mapGrp.map f) T
        (x ≫ (kernelBaseChangeIso b f).hom.hom.hom)) =
      kernelPointsEquiv f ((Over.map b).obj T)
        (baseChangePointsEquiv b (kernel f) T x) := by
  apply Subtype.ext
  change baseChangePointsEquiv b G T
    ((x ≫ (kernelBaseChangeIso b f).hom.hom.hom) ≫
      (kernelι ((Over.pullback b).mapGrp.map f)).hom.hom) =
    baseChangePointsEquiv b (kernel f) T x ≫ (kernelι f).hom.hom
  rw [← baseChangePointsEquiv_comp b (kernelι f) T]
  congr 1
  rw [Category.assoc]
  congr 1
  exact congrArg (fun k => k.hom.hom) (kernelBaseChangeIso_hom_ι b f)

end Langlands.GroupScheme
