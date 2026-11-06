import Langlands.Global.AdelicRestrictionSplitCentreComparisonStatement
import Langlands.GroupScheme.AffineWeilTorusAdjunction
import Langlands.GroupScheme.SplitComponent.AffineTargetBridge
import Langlands.Global.PositiveRealTorusIntrinsic
import Langlands.Global.RealSplitTorusPositiveParameters
import Langlands.Global.RealSplitTorusAdelicComparison

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme Langlands.GroupScheme.SplitComponent
open Langlands.Global.AdelicWeilRestriction PositiveRealTorus

section Coordinates

variable {K : Type u} [Field K] (T : CommGroupScheme (Spec (CommRingCat.of K)))
  (J : Type u) [Fintype J] (eT : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) J)
  (A : Type u) [CommRing A] [Algebra K A]

/-- Splitting coordinates of a point coming from the lattice model of the split torus. -/
theorem coordinates_lattice
    (y : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A)) ⟶
      (Corepresented.groupScheme (latticeFunctor (CommRingCat.of K) (FreeAbelianGroup J))
        (latticeCorep (CommRingCat.of K) (FreeAbelianGroup J))).X) :
    coordinates K J T eT A (y ≫ (torusIso (CommRingCat.of K) J).hom.hom.hom ≫ eT.inv.hom.hom) =
      freeCharEquiv (CommRingCat.of K) J (CommAlgCat.of K A)
        (Corepresented.affinePointsEquiv _ _ _ y) := by
  have hy : eT.inv.hom.hom ≫ eT.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  change splitTorus.algebraPointsEquiv J A
      ((y ≫ (torusIso (CommRingCat.of K) J).hom.hom.hom ≫ eT.inv.hom.hom) ≫ eT.hom.hom.hom) = _
  rw [Category.assoc, Category.assoc, hy, Category.comp_id]
  exact algebraPointsEquiv_torusIso (CommRingCat.of K) J (CommAlgCat.of K A) y

/-- With the identity splitting, coordinates are the unit coordinates of the split torus. -/
theorem coordinates_refl (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of K)) J) A) :
    coordinates K J (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) J) (Iso.refl _) A x =
      splitTorus.algebraPointsEquiv J A x := by
  change splitTorus.algebraPointsEquiv J A (x ≫ 𝟙 _) = _
  rw [Category.comp_id]

end Coordinates

section Adelic

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem infinite_comp {H G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [IsAffine G.X.left] [NumberField F] (f : H ⟶ G) (g : AdelicGroupPoints F H) :
    AdelicGroupPoints.infinite F G (g ≫ f.hom.hom) =
      AdelicGroupPoints.infinite F H g ≫ f.hom.hom := by
  change (algSpec (CommRingCat.of F)).map _ ≫ (g ≫ f.hom.hom) =
    ((algSpec (CommRingCat.of F)).map _ ≫ g) ≫ f.hom.hom
  rw [Category.assoc]

omit [NumberField F] in
theorem finite_comp {H G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [IsAffine G.X.left] [NumberField F] (f : H ⟶ G) (g : AdelicGroupPoints F H) :
    AdelicGroupPoints.finite F G (g ≫ f.hom.hom) =
      AdelicGroupPoints.finite F H g ≫ f.hom.hom := by
  change (algSpec (CommRingCat.of F)).map _ ≫ (g ≫ f.hom.hom) =
    ((algSpec (CommRingCat.of F)).map _ ≫ g) ≫ f.hom.hom
  rw [Category.assoc]

/-- Inclusion at infinity commutes with homomorphisms of group schemes. -/
theorem ofInfinite_comp {H G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [IsAffine G.X.left] (f : H ⟶ G) (a : InfiniteAdelicGroupPoints F H) :
    AdelicGroupPoints.ofInfinite F G (a ≫ f.hom.hom) =
      AdelicGroupPoints.ofInfinite F H a ≫ f.hom.hom := by
  apply (AdelicGroupPoints.split F G).injective
  rw [AdelicGroupPoints.split_apply, AdelicGroupPoints.split_apply, infinite_comp, finite_comp,
    AdelicGroupPoints.infinite_ofInfinite, AdelicGroupPoints.finite_ofInfinite,
    AdelicGroupPoints.infinite_ofInfinite, AdelicGroupPoints.finite_ofInfinite]
  congr 1
  exact (map_one (pointMap F H G (FiniteAdeles F) f)).symm

variable {F} in
/-- The positive scalar units at infinity are the infinite components of positive ideles. -/
theorem units_fst_full (x : ℝ≥0ˣ) :
    Units.map (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom
      (PositiveRealIdeles.full F x) = PositiveRealIdeles.infinite F x := by
  apply Units.ext
  rfl

variable {F} in
theorem units_snd_full (x : ℝ≥0ˣ) :
    Units.map (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom
      (PositiveRealIdeles.full F x) = 1 := by
  apply Units.ext
  rfl

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.toGrp.X.left]
  (J : Type) [Fintype J] (eT : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J)

/-- A positive adelic torus point is its infinite component included with finite part one. -/
theorem full_eq_ofInfinite (s : J → ℝ≥0ˣ) (p : InfiniteAdelicGroupPoints F T.toGrp)
    (hp : coordinates F J T eT (InfiniteAdeles F) p =
      fun k => PositiveRealIdeles.infinite F (s k)) :
    full F J T eT s = AdelicGroupPoints.ofInfinite F T.toGrp p := by
  apply (AdelicGroupPoints.split F T.toGrp).injective
  rw [AdelicGroupPoints.split_apply, AdelicGroupPoints.split_apply,
    AdelicGroupPoints.infinite_ofInfinite, AdelicGroupPoints.finite_ofInfinite]
  apply Prod.ext
  · dsimp only
    apply (coordinates F J T eT (InfiniteAdeles F)).injective
    rw [hp]
    funext k
    have h := congrFun (coordinates_affineMap F T J eT
      (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F)) (full F J T eT s)) k
    have hf := congrFun (coordinates_full F J T eT s) k
    exact h.trans ((congrArg (Units.map
      (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom) hf).trans
        (units_fst_full _))
  · dsimp only
    apply (coordinates F J T eT (FiniteAdeles F)).injective
    funext k
    have h := congrFun (coordinates_affineMap F T J eT
      (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F)) (full F J T eT s)) k
    have hf := congrFun (coordinates_full F J T eT s) k
    refine h.trans ((congrArg (Units.map
      (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom) hf).trans
        ((units_snd_full _).trans ?_))
    exact (congrFun ((coordinates F J T eT (FiniteAdeles F)).map_one) k).symm

end Adelic

section Real

variable (F : Type) [Field F] [NumberField F]

/-- The diagonal real embedding into the infinite adeles, as a map of `ℚ`-algebras through `F`. -/
def realDiagonal : CommAlgCat.of (CommRingCat.of ℚ) ℝ ⟶
    (AffineWeil.restrictScalars ℚ F).obj (CommAlgCat.of (CommRingCat.of F) (InfiniteAdeles F)) :=
  letI : Algebra ℚ (InfiniteAdeles F) := Algebra.compHom _ (algebraMap ℚ F)
  CommAlgCat.ofHom
    { toRingHom := PositiveRealIdeles.infiniteRealEmbedding F
      commutes' := fun q => DFunLike.congr_fun (RingHom.ext_rat
        ((PositiveRealIdeles.infiniteRealEmbedding F).comp (algebraMap ℚ ℝ))
        ((algebraMap F (InfiniteAdeles F)).comp (algebraMap ℚ F))) q }

theorem realDiagonal_apply (r : ℝ) :
    (realDiagonal F).hom r = PositiveRealIdeles.infiniteRealEmbedding F r := rfl

/-- Multiplying `F` against the diagonal real embedding is the canonical real tensor comparison. -/
theorem tensorMap_realDiagonal_multiplication :
    (AffineWeil.tensorFunctor ℚ F).map (realDiagonal F) ≫
        AffineWeil.multiplication ℚ (CommAlgCat.of (CommRingCat.of F) (InfiniteAdeles F)) =
      CommAlgCat.ofHom (realTensorEquiv F).toAlgHom := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply]
  induction x using TensorProduct.inductionOn with
  | tmul f r =>
    rw [AffineWeil.multiplication_tensorMap_tmul]
    funext v
    change _ = realTensorEquiv F (f ⊗ₜ r) v
    rw [realTensorEquiv_tmul]
    rfl
  | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]

theorem realTensorEquiv_one_tmul (r : ℝ) :
    realTensorEquiv F ((1 : F) ⊗ₜ[ℚ] r) = PositiveRealIdeles.infiniteRealEmbedding F r := by
  funext v
  rw [realTensorEquiv_tmul, map_one, one_mul]
  rfl

end Real

section Comparison

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
  (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

/-- The image of the `F`-split component lies in the image of a split component of the
restriction. -/
theorem imageSubgroup_le_subgroup [IsAffine T.toGrp.X.left] (hj : IsSplitComponent j)
    (hi : IsCentralSplitTorus i) :
    imageSubgroup F T G i ≤ subgroup F G S j := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hi.1.1
  let _ : Fintype J := Fintype.ofFinite J
  rw [← subgroup_eq_intrinsicSubgroup F J T eT] at hw
  obtain ⟨s, rfl⟩ := hw
  let hT : Corepresented.groupScheme (latticeFunctor (CommRingCat.of F) (FreeAbelianGroup J))
      (latticeCorep (CommRingCat.of F) (FreeAbelianGroup J)) ⟶ G :=
    ((torusIso (CommRingCat.of F) J).hom ≫ eT.inv) ≫ i
  have hTc : IsCentral hT := hi.2.comp _
  let I := natToPoints (latticeCorep (CommRingCat.of F) (FreeAbelianGroup J)) hT
  let γ := AffineWeil.unitTrans ℚ G I
  let ψ := Corepresented.groupSchemeMap (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup J))
    (AffineWeil.corepresentableBy ℚ F G) γ
  have hψ : IsCentral ψ := isCentral_groupSchemeMap _ _
    (AffineWeil.isCentralNat_unitTrans ℚ G (isCentralNat_natToPoints _ hTc))
  obtain ⟨g, hg⟩ := hj.exists_comp_eq_of_isCentral (finiteType_coordinateAlgebra _)
    ((torusIso (CommRingCat.of ℚ) J).inv ≫ ψ) (isSplitTorus_splitTorus J) (hψ.comp _)
  let u : J → ℝˣ := fun k => Units.map NNReal.toRealHom.toMonoidHom (s k)
  let t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of ℚ)) J) ℝ :=
    (splitTorus.algebraPointsEquiv J ℝ).symm u
  have ht : t ∈ orderedCoefficientPositiveSubgroup ℚ
      (splitTorus.commGroupScheme (Spec (CommRingCat.of ℚ)) J) ℝ := by
    rw [mem_orderedCoefficientPositiveSubgroup_iff_coordinates ℚ _ ℝ J (Iso.refl _)]
    intro k
    rw [coordinates_refl, MulEquiv.apply_symm_apply]
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (s k).ne_zero)
  have ha := pointMap_mem_orderedCoefficientPositiveSubgroup ℚ
    (splitTorus.commGroupScheme (Spec (CommRingCat.of ℚ)) J) ℝ S (Additive.ofMul g) t ht
  refine ⟨⟨_, ha⟩, ?_⟩
  rw [positiveImageHom_apply]
  let x0 := t ≫ (torusIso (CommRingCat.of ℚ) J).inv.hom.hom
  have h1 : pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j
      (pointMap ℚ (splitTorus.commGroupScheme (Spec (CommRingCat.of ℚ)) J).toGrp S.toGrp ℝ
        (CommGroupScheme.groupHom
          (Additive.ofMul g : splitTorus.commGroupScheme (Spec (CommRingCat.of ℚ)) J ⟶ S)) t) =
        x0 ≫ ψ.hom.hom := by
    change (t ≫ g.hom.hom) ≫ j.hom.hom = (t ≫ _) ≫ ψ.hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hg, Grp.comp_hom_hom]
  have h2 : AffineWeil.pointsEquiv ℚ F G ℝ (x0 ≫ ψ.hom.hom) =
      γ.app _ (Corepresented.affinePointsEquiv _
        (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup J)) _ x0) :=
    Corepresented.groupSchemeMap_affinePoints _ _ γ x0
  set χ := Corepresented.affinePointsEquiv _
    (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup J)) (CommAlgCat.of ℚ ℝ) x0 with hχ_def
  have hχ : freeCharEquiv (CommRingCat.of ℚ) J (CommAlgCat.of ℚ ℝ) χ = u := by
    rw [hχ_def, ← algebraPointsEquiv_torusIso]
    have hc : x0 ≫ (torusIso (CommRingCat.of ℚ) J).hom.hom.hom = t := by
      change (t ≫ _) ≫ _ = t
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    rw [hc]
    exact MulEquiv.apply_symm_apply _ _
  let f := CommAlgCat.ofHom (realTensorEquiv F).toAlgHom
  let χ2 := (latticeFunctor (CommRingCat.of F) (FreeAbelianGroup J)).map f
    ((AffineWeil.latticeUnit ℚ F).app _ χ)
  have h3 : realPointsEquiv F G (x0 ≫ ψ.hom.hom) =
      I.app (CommAlgCat.of F (InfiniteAdeles F)) χ2 := by
    rw [realPointsEquiv_apply, h2]
    exact (ConcreteCategory.congr_hom (I.naturality f) _).symm
  let y2 := (Corepresented.affinePointsEquiv _
    (latticeCorep (CommRingCat.of F) (FreeAbelianGroup J))
    (CommAlgCat.of F (InfiniteAdeles F))).symm χ2
  let p : InfiniteAdelicGroupPoints F T.toGrp :=
    y2 ≫ (torusIso (CommRingCat.of F) J).hom.hom.hom ≫ eT.inv.hom.hom
  have h4 : I.app (CommAlgCat.of F (InfiniteAdeles F)) χ2 = p ≫ i.hom.hom := by
    rw [natToPoints_app]
    change y2 ≫ (((torusIso (CommRingCat.of F) J).hom ≫ eT.inv) ≫ i).hom.hom = _
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom]
    simp only [p, Category.assoc]
  have hp : coordinates F J T eT (InfiniteAdeles F) p =
      fun k => PositiveRealIdeles.infinite F (s k) := by
    rw [coordinates_lattice, MulEquiv.apply_symm_apply]
    funext k
    apply Units.ext
    have hk := congrFun hχ k
    change realTensorEquiv F ((1 : F) ⊗ₜ[ℚ]
      ((freeCharEquiv (CommRingCat.of ℚ) J (CommAlgCat.of ℚ ℝ) χ k : ℝˣ) : ℝ)) = _
    rw [hk, realTensorEquiv_one_tmul]
    rfl
  rw [h1, h3, h4, ofInfinite_comp, ← full_eq_ofInfinite F T J eT s p hp]
  rfl

/-- A split component of the restriction has image inside the image of the `F`-split
component. -/
theorem subgroup_le_imageSubgroup [IsAffine T.toGrp.X.left] (hj : IsCentralSplitTorus j)
    (hi : IsSplitComponent i) :
    subgroup F G S j ≤ imageSubgroup F T G i := by
  rintro _ ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨I0, hI0, ⟨eS⟩⟩ := hj.1.1
  let _ : Fintype I0 := Fintype.ofFinite I0
  let hS : Corepresented.groupScheme (latticeFunctor (CommRingCat.of ℚ) (FreeAbelianGroup I0))
      (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup I0)) ⟶ AffineWeil.groupScheme ℚ F G :=
    ((torusIso (CommRingCat.of ℚ) I0).hom ≫ eS.inv) ≫ j
  have hSc : IsCentral hS := hj.2.comp _
  let α := natOfHom (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup I0))
    (AffineWeil.corepresentableBy ℚ F G) hS
  have hα : IsCentralNat α := isCentralNat_of_isCentral _ _ (by
    rw [groupSchemeMap_natOfHom]
    exact hSc)
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  let β := AffineWeil.counitTrans ℚ G α
  have hβ : IsCentralNat β := AffineWeil.isCentralNat_counitTrans ℚ G hα
  let φ := homOfNat G (latticeCorep (CommRingCat.of F) (FreeAbelianGroup I0)) β
  have hφ : IsCentral φ := isCentral_homOfNat G _ hβ
  obtain ⟨f, hf⟩ := hi.exists_comp_eq_of_isCentral (finiteType_coordinateAlgebra G)
    ((torusIso (CommRingCat.of F) I0).inv ≫ φ) (isSplitTorus_splitTorus I0) (hφ.comp _)
  have hc := (mem_orderedCoefficientPositiveSubgroup_iff_coordinates ℚ S ℝ I0 eS a).mp ha
  let s : I0 → ℝ≥0ˣ := fun k => Units.mk0 ⟨((coordinates ℚ I0 S eS ℝ a k : ℝˣ) : ℝ), (hc k).le⟩
    (fun h => (hc k).ne' (congrArg Subtype.val h))
  let w0 := full F I0 (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I0) (Iso.refl _) s
  have hw0 :
      w0 ∈ intrinsicSubgroup F (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I0) := by
    rw [← subgroup_eq_intrinsicSubgroup F I0 _ (Iso.refl _)]
    exact ⟨s, rfl⟩
  refine ⟨_, map_intrinsicSubgroup_le F _ T
    (Additive.ofMul f : splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I0 ⟶ T)
    ⟨w0, hw0, rfl⟩, ?_⟩
  rw [positiveImageHom_apply]
  -- the adelic side
  let y0 := w0 ≫ (torusIso (CommRingCat.of F) I0).inv.hom.hom
  have hL : pointMap F T.toGrp G (Adeles F) i
      (pointMap F (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I0).toGrp T.toGrp
        (Adeles F) (CommGroupScheme.groupHom
          (Additive.ofMul f : splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I0 ⟶ T)) w0) =
        y0 ≫ φ.hom.hom := by
    change (w0 ≫ f.hom.hom) ≫ i.hom.hom = (w0 ≫ _) ≫ φ.hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hf, Grp.comp_hom_hom]
  rw [hL, homOfNat_affinePoints, AffineWeil.counitTrans_app]
  set χA := Corepresented.affinePointsEquiv _
    (latticeCorep (CommRingCat.of F) (FreeAbelianGroup I0))
    (CommAlgCat.of F (Adeles F)) y0 with hχA_def
  have hχA : freeCharEquiv (CommRingCat.of F) I0 (CommAlgCat.of F (Adeles F)) χA =
      fun k => PositiveRealIdeles.full F (s k) := by
    rw [hχA_def, ← algebraPointsEquiv_torusIso]
    have hy : y0 ≫ (torusIso (CommRingCat.of F) I0).hom.hom.hom = w0 := by
      change (w0 ≫ _) ≫ _ = w0
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    rw [hy, ← coordinates_refl, coordinates_full]
  -- the real side
  have c1 : (torusIso (CommRingCat.of ℚ) I0).inv.hom.hom ≫
      (torusIso (CommRingCat.of ℚ) I0).hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  have c2 : eS.hom.hom.hom ≫ eS.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom]
  let x1 := a ≫ eS.hom.hom.hom ≫ (torusIso (CommRingCat.of ℚ) I0).inv.hom.hom
  have hR1 : pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j a = x1 ≫ hS.hom.hom := by
    change a ≫ j.hom.hom = x1 ≫ (((torusIso (CommRingCat.of ℚ) I0).hom ≫ eS.inv) ≫ j).hom.hom
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom]
    simp only [x1, Category.assoc, reassoc_of% c1, reassoc_of% c2]
  have hR2 : AffineWeil.pointsEquiv ℚ F G ℝ (x1 ≫ hS.hom.hom) =
      α.app (CommAlgCat.of ℚ ℝ) (Corepresented.affinePointsEquiv _
        (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup I0)) _ x1) := by
    rw [natOfHom_app, MulEquiv.symm_apply_apply]
    rfl
  set χR := Corepresented.affinePointsEquiv _
    (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup I0))
    (CommAlgCat.of ℚ ℝ) x1 with hχR_def
  have hχR : freeCharEquiv (CommRingCat.of ℚ) I0 (CommAlgCat.of ℚ ℝ) χR =
      coordinates ℚ I0 S eS ℝ a := by
    rw [hχR_def, ← algebraPointsEquiv_torusIso]
    have hx : x1 ≫ (torusIso (CommRingCat.of ℚ) I0).hom.hom.hom = a ≫ eS.hom.hom.hom := by
      simp only [x1, Category.assoc, c1, Category.comp_id]
    rw [hx]
    rfl
  rw [hR1, realPointsEquiv_apply, hR2]
  have hR := (congrArg (fun m => G.affinePointMap m (α.app (CommAlgCat.of ℚ ℝ) χR))
    (tensorMap_realDiagonal_multiplication F).symm).trans
      (AffineWeil.affinePointMap_tensorMap_multiplication ℚ G α (realDiagonal F) χR)
  have hInf := AffineWeil.affinePointMap_multiplication_app ℚ G α
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F)))
    ((AffineWeil.latticeRestrict ℚ F (FreeAbelianGroup I0)).app _ χA)
  have hFin := AffineWeil.affinePointMap_multiplication_app ℚ G α
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F)))
    ((AffineWeil.latticeRestrict ℚ F (FreeAbelianGroup I0)).app _ χA)
  have hcharInf : (latticeFunctor (CommRingCat.of ℚ) (FreeAbelianGroup I0)).map
      ((AffineWeil.restrictScalars ℚ F).map
        (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F))))
      ((AffineWeil.latticeRestrict ℚ F (FreeAbelianGroup I0)).app _ χA) =
        (latticeFunctor (CommRingCat.of ℚ) (FreeAbelianGroup I0)).map (realDiagonal F) χR := by
    apply (freeCharEquiv (CommRingCat.of ℚ) I0 _).injective
    funext k
    apply Units.ext
    have h1 := congrFun hχA k
    have h2 := congrFun hχR k
    change (AlgHom.fst F (InfiniteAdeles F) (FiniteAdeles F))
        ((freeCharEquiv (CommRingCat.of F) I0 (CommAlgCat.of F (Adeles F)) χA k : (Adeles F)ˣ) :
          Adeles F) =
      (realDiagonal F).hom ((freeCharEquiv (CommRingCat.of ℚ) I0 (CommAlgCat.of ℚ ℝ) χR k : ℝˣ) : ℝ)
    rw [h1, h2]
    rfl
  have hcharFin : (latticeFunctor (CommRingCat.of ℚ) (FreeAbelianGroup I0)).map
      ((AffineWeil.restrictScalars ℚ F).map
        (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F))))
      ((AffineWeil.latticeRestrict ℚ F (FreeAbelianGroup I0)).app _ χA) = 1 := by
    apply (freeCharEquiv (CommRingCat.of ℚ) I0 _).injective
    rw [map_one]
    funext k
    apply Units.ext
    have h1 := congrFun hχA k
    change (AlgHom.snd F (InfiniteAdeles F) (FiniteAdeles F))
        ((freeCharEquiv (CommRingCat.of F) I0 (CommAlgCat.of F (Adeles F)) χA k : (Adeles F)ˣ) :
          Adeles F) = 1
    rw [h1]
    rfl
  apply (AdelicGroupPoints.split F G).injective
  rw [AdelicGroupPoints.split_apply, AdelicGroupPoints.split_apply,
    AdelicGroupPoints.infinite_ofInfinite, AdelicGroupPoints.finite_ofInfinite]
  refine Prod.ext ?_ ?_
  · refine hInf.trans ((congrArg (fun χ => G.affinePointMap
      (AffineWeil.multiplication ℚ (CommAlgCat.of F (InfiniteAdeles F)))
        (α.app _ χ)) hcharInf).trans hR.symm)
  · refine hFin.trans ((congrArg (fun χ => G.affinePointMap
      (AffineWeil.multiplication ℚ (CommAlgCat.of F (FiniteAdeles F)))
        (α.app _ χ)) hcharFin).trans ?_)
    change G.affinePointMap _ ((α.app _).hom 1) = 1
    rw [map_one]
    exact (G.affinePointMap _).map_one

end Comparison

/-- **Comparison of the two split-centre subgroups.** A split component of the Weil restriction
and a split component of the group have the same positive real image in the actual adelic
points. -/
theorem comparison : ComparisonStatement := by
  intro F _ _ G _ _ S j T i hj hi
  have : IsAffineHom G.X.hom := inferInstance
  have : IsClosedImmersion i.hom.hom.left := hi.1.1.2
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  exact le_antisymm (subgroup_le_imageSubgroup F G S j T i hj.1 hi)
    (imageSubgroup_le_subgroup F G S j T i hj hi.1)

end Langlands.Global.RestrictionSplitCentre
