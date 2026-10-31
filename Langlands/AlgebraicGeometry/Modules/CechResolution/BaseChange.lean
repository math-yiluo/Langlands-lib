import Langlands.AlgebraicGeometry.Modules.CechResolution.Complex
import Langlands.Cohomology.AcyclicResolution.Composition
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Maps of sheafified Čech complexes over a morphism of schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  {M : X.Modules} {N : Y.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)

/-- The target intersection lies over the source intersection. -/
lemma sheafOnPushforward_le {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) (V : X.Opens) :
    W'.ι ''ᵁ (W'.ι ⁻¹ᵁ (g ⁻¹ᵁ V)) ≤
      g ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) := by
  rw [image_preimage_eq, image_preimage_eq, Scheme.Hom.preimage_inf]
  exact inf_le_inf_right _ hW

/-- A map on sections of the source intersection followed by restriction
to the target intersection. -/
def sheafOnPushforwardApp {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) (V : X.Opens) :
    Γ(sheafOn M W, V) ⟶
      Γ((Scheme.Modules.pushforward g).obj (sheafOn N W'), V) :=
  a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) ≫
    N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op

lemma sheafOnPushforwardApp_naturality {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) {V V' : X.Opens} (i : V' ⟶ V) :
    (sheafOn M W).presheaf.map i.op ≫ sheafOnPushforwardApp g a hW V' =
      sheafOnPushforwardApp g a hW V ≫
        ((Scheme.Modules.pushforward g).obj (sheafOn N W')).presheaf.map i.op := by
  have ha := a.mapPresheaf.naturality
    (homOfLE (image_preimage_mono_right W (leOfHom i))).op
  change M.presheaf.map _ ≫ a.app _ = a.app _ ≫ N.presheaf.map _ at ha
  change M.presheaf.map (homOfLE (image_preimage_mono_right W (leOfHom i))).op ≫
      (a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V')) ≫
        N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V')).op) =
    (a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) ≫
      N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op) ≫
        N.presheaf.map
          (homOfLE (image_preimage_mono_right W' (show g ⁻¹ᵁ V' ≤ g ⁻¹ᵁ V from
            fun x hx => leOfHom i hx))).op
  rw [← Category.assoc, ha, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) ≫ N.presheaf.map k)
    (Subsingleton.elim _ _)

lemma sheafOnPushforwardApp_smul {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) (V : X.Opens)
    (r : Γ(X, V)) (m : Γ(sheafOn M W, V)) :
    sheafOnPushforwardApp g a hW V (r • m) =
      r • sheafOnPushforwardApp g a hW V m := by
  have hr := g.naturality
    (homOfLE (W.ι.image_preimage_le V)).op
  have hr' := congrArg
    (fun k => k ≫ Y.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op) hr
  simp only [Category.assoc, ← Functor.map_comp] at hr'
  have hr'' :
      (W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv) ≫
          g.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) ≫
          Y.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op =
        g.app V ≫
          (W'.ι.app (g ⁻¹ᵁ V) ≫
            (W'.ι.appIso (W'.ι ⁻¹ᵁ (g ⁻¹ᵁ V))).inv) := by
    rw [Scheme.Hom.app_appIso_inv, Scheme.Hom.app_appIso_inv]
    exact hr'.trans (congrArg (fun k => g.app V ≫ Y.presheaf.map k)
      (Subsingleton.elim _ _))
  let m' : Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) := m
  let n : Γ(N, g ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V))) :=
    a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) m'
  let r' : Γ(X, W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) :=
    (W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv) r
  have ha :
      (show Γ(N, g ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V))) from
        a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) (r' • m')) =
      g.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) r' • n :=
    Scheme.Modules.Hom.app_smul a r' m'
  have hn := Scheme.Modules.map_smul N (homOfLE (sheafOnPushforward_le g hW V))
    (g.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) r') n
  have he := congrArg
    (fun z : Γ(Y, W'.ι ''ᵁ (W'.ι ⁻¹ᵁ (g ⁻¹ᵁ V))) =>
      (N.smul z).hom (N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op n))
    (ConcreteCategory.congr_hom hr'' r)
  exact (congrArg
    (fun z : Γ(N, g ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V))) =>
      N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op z) ha).trans
        (hn.trans he)

/-- The actual map of module sheaves from one open factor of a Čech term
to the pushforward of a corresponding target factor. -/
def sheafOnPushforward {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) :
    sheafOn M W ⟶ (Scheme.Modules.pushforward g).obj (sheafOn N W') where
  val := PresheafOfModules.homMk
    { app V := sheafOnPushforwardApp g a hW V.unop
      naturality _ _ i := sheafOnPushforwardApp_naturality g a hW i.unop }
    (fun V r m => sheafOnPushforwardApp_smul g a hW V.unop r m)

@[simp]
lemma sheafOnPushforward_app {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) (V : X.Opens) :
    (sheafOnPushforward g a hW).app V =
      a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) ≫
        N.presheaf.map (homOfLE (sheafOnPushforward_le g hW V)).op := rfl

/-- The factor map commutes with the restriction units. -/
@[reassoc]
lemma unit_sheafOnPushforward {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) :
    unit M W ≫ sheafOnPushforward g a hW =
      a ≫ (Scheme.Modules.pushforward g).map (unit N W') := by
  ext V : 1
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    sheafOnPushforward_app, Scheme.Modules.pushforward_map_app, unit_app, unit_app]
  have ha := a.mapPresheaf.naturality (homOfLE (W.ι.image_preimage_le V)).op
  change M.presheaf.map _ ≫ a.app _ = a.app _ ≫ N.presheaf.map _ at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k => a.app V ≫ N.presheaf.map k) (Subsingleton.elim _ _)

/-- The factor map commutes with restriction to smaller source and target opens. -/
@[reassoc]
lemma res_sheafOnPushforward {W₀ W₁ : X.Opens} {W₀' W₁' : Y.Opens}
    (h : W₁ ≤ W₀) (h' : W₁' ≤ W₀')
    (h₀ : W₀' ≤ g ⁻¹ᵁ W₀) (h₁ : W₁' ≤ g ⁻¹ᵁ W₁) :
    res M h ≫ sheafOnPushforward g a h₁ =
      sheafOnPushforward g a h₀ ≫ (Scheme.Modules.pushforward g).map (res N h') := by
  ext V : 1
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    sheafOnPushforward_app, sheafOnPushforward_app,
    Scheme.Modules.pushforward_map_app, res_app, res_app]
  have ha := a.mapPresheaf.naturality (homOfLE (image_preimage_mono h V)).op
  change M.presheaf.map _ ≫ a.app _ = a.app _ ≫ N.presheaf.map _ at ha
  rw [← Category.assoc, ha, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => a.app (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V)) ≫ N.presheaf.map k)
    (Subsingleton.elim _ _)

section InverseImage

attribute [local instance] preservesBiproduct_of_preservesProduct

variable [IsAffineHom g] (𝒰 : X.OrderedAffineCover)

/-- The inverse-image ordered affine cover, with the same ordered index type. -/
abbrev inverseImageCover : Y.OrderedAffineCover where
  ι := 𝒰.ι
  U i := g ⁻¹ᵁ 𝒰.U i
  isAffineOpen i := (𝒰.isAffineOpen i).preimage g
  iSup_eq_top := g.iSup_preimage_eq_top 𝒰.iSup_eq_top

lemma inverseImageCover_inter {p : ℕ} (s : 𝒰.Idx p) :
    (inverseImageCover g 𝒰).inter s = g ⁻¹ᵁ 𝒰.inter s := by
  apply Opens.ext
  simp only [Scheme.OrderedAffineCover.inter, Opens.coe_iInf, Scheme.Hom.coe_preimage,
    Set.preimage_iInter, inverseImageCover]

/-- The containment used in the map of corresponding Čech factors. -/
lemma inverseImageCover_inter_le {p : ℕ} (s : 𝒰.Idx p) :
    (inverseImageCover g 𝒰).inter s ≤ g ⁻¹ᵁ 𝒰.inter s :=
  le_of_eq (inverseImageCover_inter g 𝒰 s)

omit [IsAffineHom g] in
/-- A morphism into the pushforward of a finite biproduct is determined by
the pushforwards of its projections. -/
lemma pushforward_biproduct_hom_ext {ι : Type u} [Fintype ι] (B : ι → Y.Modules)
    {P : X.Modules} (b c : P ⟶ (Scheme.Modules.pushforward g).obj (⨁ B))
    (h : ∀ i, b ≫ (Scheme.Modules.pushforward g).map (biproduct.π B i) =
      c ≫ (Scheme.Modules.pushforward g).map (biproduct.π B i)) :
    b = c := by
  exact (isBilimitOfPreserves (Scheme.Modules.pushforward g)
    (biproduct.isBilimit B)).isLimit.hom_ext (fun i => h i.as)

/-- The map in degree `p`, assembled from the maps on intersections. -/
def cechTermPushforward (p : ℕ) :
    cechTerm 𝒰 M p ⟶
      (Scheme.Modules.pushforward g).obj (cechTerm (inverseImageCover g 𝒰) N p) :=
  (isBilimitOfPreserves (Scheme.Modules.pushforward g)
    (biproduct.isBilimit
      (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s)))).isLimit.lift
        (Fan.mk _ (fun s : 𝒰.Idx p =>
          biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s ≫
            sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s)))

@[reassoc]
lemma cechTermPushforward_π (p : ℕ) (s : 𝒰.Idx p) :
    cechTermPushforward g a 𝒰 p ≫
        (Scheme.Modules.pushforward g).map
          (biproduct.π (fun s : 𝒰.Idx p =>
            sheafOn N ((inverseImageCover g 𝒰).inter s)) s) =
      biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s ≫
        sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s) :=
  (isBilimitOfPreserves (Scheme.Modules.pushforward g)
    (biproduct.isBilimit _)).isLimit.fac _ ⟨s⟩

/-- The degreewise maps commute with the alternating differentials. -/
lemma cechTermPushforward_cechD (p : ℕ) :
    cechTermPushforward g a 𝒰 p ≫
        (Scheme.Modules.pushforward g).map (cechD (inverseImageCover g 𝒰) N p) =
      cechD 𝒰 M p ≫ cechTermPushforward g a 𝒰 (p + 1) := by
  apply pushforward_biproduct_hom_ext g
    (fun s : 𝒰.Idx (p + 1) => sheafOn N ((inverseImageCover g 𝒰).inter s))
  intro t
  rw [Category.assoc, ← Functor.map_comp]
  refine (congrArg (fun k => cechTermPushforward g a 𝒰 p ≫
    (Scheme.Modules.pushforward g).map k)
      (cechD_π (inverseImageCover g 𝒰) N p t)).trans ?_
  rw [Functor.map_sum, Category.assoc, cechTermPushforward_π,
    ← Category.assoc, cechD_π]
  simp only [Functor.map_zsmul, Functor.map_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    ← Category.assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hπ := cechTermPushforward_π g a 𝒰 p (𝒰.face t j)
  have hr := res_sheafOnPushforward g a (𝒰.inter_le_inter_face t j)
    ((inverseImageCover g 𝒰).inter_le_inter_face t j)
    (inverseImageCover_inter_le g 𝒰 (𝒰.face t j))
    (inverseImageCover_inter_le g 𝒰 t)
  refine (congrArg (fun k => k ≫ (Scheme.Modules.pushforward g).map
    (res N ((inverseImageCover g 𝒰).inter_le_inter_face t j))) hπ).trans ?_
  rw [Category.assoc, ← hr, ← Category.assoc]

/-- The actual cochain map induced by `a : M ⟶ g_*N` on inverse-image covers. -/
def cechPushforward :
    cechComplex 𝒰 M ⟶
      ((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex (inverseImageCover g 𝒰) N) :=
  CochainComplex.ofHom (cechTermPushforward g a 𝒰) (fun p => by
    change cechTermPushforward g a 𝒰 p ≫
        (Scheme.Modules.pushforward g).map
          ((cechComplex (inverseImageCover g 𝒰) N).d p (p + 1)) =
      (cechComplex 𝒰 M).d p (p + 1) ≫ cechTermPushforward g a 𝒰 (p + 1)
    simpa only [cechComplex, CochainComplex.of_d] using
      cechTermPushforward_cechD g a 𝒰 p)

@[simp]
lemma cechPushforward_f (p : ℕ) :
    (cechPushforward g a 𝒰).f p = cechTermPushforward g a 𝒰 p := rfl

/-- The degree-zero augmentation square for the actual cochain map. -/
lemma augmentation_cechTermPushforward :
    augmentation 𝒰 M ≫ cechTermPushforward g a 𝒰 0 =
      a ≫ (Scheme.Modules.pushforward g).map
        (augmentation (inverseImageCover g 𝒰) N) := by
  apply pushforward_biproduct_hom_ext g
    (fun s : 𝒰.Idx 0 => sheafOn N ((inverseImageCover g 𝒰).inter s))
  intro s
  rw [Category.assoc, cechTermPushforward_π, ← Category.assoc, augmentation_π,
    Category.assoc, ← Functor.map_comp]
  exact (unit_sheafOnPushforward g a _).trans
    (congrArg (fun k => a ≫ (Scheme.Modules.pushforward g).map k)
      (augmentation_π (inverseImageCover g 𝒰) N s).symm)

/-- The full augmentation square for the map induced by `a`. -/
lemma cechAug_cechPushforward :
    cechAug 𝒰 M ≫ cechPushforward g a 𝒰 =
      (CochainComplex.single₀ X.Modules).map a ≫
        Langlands.Cohomology.AcyclicResolution.mapResolutionAugmentation
          (Scheme.Modules.pushforward g) (cechAug (inverseImageCover g 𝒰) N) := by
  ext : 1
  simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    Langlands.Cohomology.AcyclicResolution.mapResolutionAugmentation_f_zero,
    cechAug, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, cechPushforward_f] using
    augmentation_cechTermPushforward g a 𝒰

/-- The Čech cochain map induced by the actual pullback/pushforward unit. -/
def cechPullback :
    cechComplex 𝒰 M ⟶
      ((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)) :=
  cechPushforward g ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰

/-- The actual pullback-unit Čech map has the required augmentation square. -/
lemma cechAug_cechPullback :
    cechAug 𝒰 M ≫ cechPullback g 𝒰 =
      (CochainComplex.single₀ X.Modules).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
        Langlands.Cohomology.AcyclicResolution.mapResolutionAugmentation
          (Scheme.Modules.pushforward g)
          (cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M)) :=
  cechAug_cechPushforward g ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰

end InverseImage

end Langlands.AlgebraicGeometry.Modules.CechResolution
