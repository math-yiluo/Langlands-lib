import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- Morphisms of module sheaves on the category of opens contained in `U`. -/
abbrev LocalHom (M N : S.Modules) (U : S.Opens) := M.over U ⟶ N.over U

namespace LocalHom

variable {M N P : S.Modules} {U V W : S.Opens}

/-- Evaluation of a local morphism on a smaller open. -/
def app (f : LocalHom M N U) (i : V ⟶ U) : M.val.obj (op V) ⟶ N.val.obj (op V) :=
  f.val.app (op (Over.mk i))

@[ext]
lemma ext (f g : LocalHom M N U) (h : ∀ (V) (i : V ⟶ U), app f i = app g i) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨V⟩
  exact h V.left V.hom

/-- Restriction of a local morphism to a smaller open. -/
def restrict (i : V ⟶ U) (f : LocalHom M N U) : LocalHom M N V where
  val :=
    { app := fun W => f.val.app ((Over.map i).op.obj W)
      naturality := fun j => f.val.naturality ((Over.map i).op.map j) }

@[simp]
lemma restrict_app (i : V ⟶ U) (f : LocalHom M N U) (j : W ⟶ V) :
    app (restrict i f) j = app f (j ≫ i) := rfl

@[simp]
lemma restrict_id (f : LocalHom M N U) : restrict (𝟙 U) f = f := by
  ext V i x
  rfl

@[simp]
lemma restrict_comp (i : V ⟶ U) (j : W ⟶ V) (f : LocalHom M N U) :
    restrict j (restrict i f) = restrict (j ≫ i) f := by
  ext T k x
  rfl

/-- Scalar multiplication uses the restriction of the scalar on each smaller open. -/
def smul (r : Γ(S, U)) (f : LocalHom M N U) : LocalHom M N U where
  val :=
    { app := fun V => ModuleCat.ofHom
        { toFun := fun x => S.presheaf.map V.unop.hom.op r • f.val.app V x
          map_add' := by intros; simp [smul_add]
          map_smul' := by
            intro a x
            change S.presheaf.map V.unop.hom.op r • f.val.app V (a • x) =
              a • (S.presheaf.map V.unop.hom.op r • f.val.app V x)
            rw [(f.val.app V).hom.map_smul]
            exact smul_comm _ _ _ }
      naturality := by
        intro V W j
        ext x
        change S.presheaf.map W.unop.hom.op r • f.val.app W (M.val.map j.unop.left.op x) =
          N.val.map j.unop.left.op (S.presheaf.map V.unop.hom.op r • f.val.app V x)
        rw [N.val.map_smul]
        have h := PresheafOfModules.naturality_apply f.val j x
        change f.val.app W (M.val.map j.unop.left.op x) =
          N.val.map j.unop.left.op (f.val.app V x) at h
        rw [h]
        congr 1
        exact (ConcreteCategory.congr_hom
          (S.presheaf.map_comp V.unop.hom.op j.unop.left.op) r) }

instance : SMul Γ(S, U) (LocalHom M N U) := ⟨smul⟩

@[simp]
lemma smul_app (r : Γ(S, U)) (f : LocalHom M N U) (i : V ⟶ U) (x : Γ(M, V)) :
    app (r • f) i x = S.presheaf.map i.op r • app f i x := rfl

@[simp] lemma add_app (f g : LocalHom M N U) (i : V ⟶ U) :
    app (f + g) i = app f i + app g i := rfl
@[simp] lemma zero_app (i : V ⟶ U) : app (0 : LocalHom M N U) i = 0 := rfl

instance : Module Γ(S, U) (LocalHom M N U) where
  one_smul f := by
    ext V i x
    change S.presheaf.map i.op 1 • app f i x = app f i x
    simp
  mul_smul r s f := by
    ext V i x
    change S.presheaf.map i.op (r * s) • app f i x =
      S.presheaf.map i.op r • (S.presheaf.map i.op s • app f i x)
    simp [mul_smul]
  smul_zero r := by
    ext V i x
    change S.presheaf.map i.op r • (0 : Γ(N, V)) = 0
    simp
  smul_add r f g := by
    ext V i x
    change S.presheaf.map i.op r • (app f i x + app g i x) =
      S.presheaf.map i.op r • app f i x + S.presheaf.map i.op r • app g i x
    exact smul_add _ _ _
  add_smul r s f := by
    ext V i x
    change S.presheaf.map i.op (r + s) • app f i x =
      S.presheaf.map i.op r • app f i x + S.presheaf.map i.op s • app f i x
    simp [add_smul]
  zero_smul f := by
    ext V i x
    change S.presheaf.map i.op 0 • app f i x = 0
    simp

@[simp]
lemma restrict_add (i : V ⟶ U) (f g : LocalHom M N U) :
    restrict i (f + g) = restrict i f + restrict i g := rfl

@[simp]
lemma restrict_smul (i : V ⟶ U) (r : Γ(S, U)) (f : LocalHom M N U) :
    restrict i (r • f) = S.presheaf.map i.op r • restrict i f := by
  ext W j x
  change S.presheaf.map (j ≫ i).op r • app f (j ≫ i) x =
    S.presheaf.map j.op (S.presheaf.map i.op r) • app f (j ≫ i) x
  rw [op_comp, S.presheaf.map_comp]
  rfl

end LocalHom

/-- The presheaf of modules of local module-sheaf morphisms. -/
def internalHomPresheaf (M N : S.Modules) : S.PresheafOfModules where
  obj U := ModuleCat.of Γ(S, U.unop) (LocalHom M N U.unop)
  map {U V} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (S.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(S, V.unop) (LocalHom M N V.unop)))
    { toFun := LocalHom.restrict i.unop
      map_add' := LocalHom.restrict_add i.unop
      map_smul' := LocalHom.restrict_smul i.unop }
  map_id U := by ext f; rfl
  map_comp i j := by ext f; rfl

/-- The linear local maps form a subpresheaf of the additive local maps. -/
def linearHomSubfunctor (M N : S.Modules) :
    Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := { f | ∀ (V : Over U.unop) (r : Γ(S, V.left)) (x : Γ(M, V.left)),
    f.app (op V) (r • x) = (r • · : Γ(N, V.left) → Γ(N, V.left)) (f.app (op V) x) }
  map := by
    intro U V i f hf W r x
    exact hf ((Over.map i.unop).obj W) r x

/-- Forgetting linearity identifies local module maps with the linear additive local maps. -/
def localHomEquiv (M N : S.Modules) (U : S.Opens) :
    LocalHom M N U ≃ (linearHomSubfunctor M N).toFunctor.obj (op U) where
  toFun f := ⟨(PresheafOfModules.toPresheaf _).map f.val,
    fun V r x => (f.val.app (op V)).hom.map_smul r x⟩
  invFun f := ⟨PresheafOfModules.homMk f.val (fun V r x => f.property V.unop r x)⟩
  left_inv f := by ext V i x; rfl
  right_inv f := by apply Subtype.ext; apply NatTrans.ext; funext V; ext x; rfl

/-- The underlying type presheaf is the linear subpresheaf of additive local maps. -/
def internalHomTypeIso (M N : S.Modules) :
    (internalHomPresheaf M N).presheaf ⋙ forget Ab ≅ (linearHomSubfunctor M N).toFunctor :=
  NatIso.ofComponents (fun U => (localHomEquiv M N U.unop).toIso) (by
    intro U V i
    ext f
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl)

/-- Linearity of a local additive map is local on the target open. -/
lemma linearHomSubfunctor_isSheaf (M N : S.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology S)
      (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf))).mpr
  intro U f hf V r x
  apply N.isSheaf.isSeparated V.left
    (((linearHomSubfunctor M N).sieveOfSection f).pullback V.hom)
    ((Opens.grothendieckTopology S).pullback_stable V.hom hf)
  intro W i hi
  have hn (z : Γ(M, V.left)) :
      f.app (op (Over.mk (i ≫ V.hom))) (M.val.map i.op z) =
        N.val.map i.op (f.app (op V) z) :=
    ConcreteCategory.congr_hom (f.naturality (Over.homMk i : Over.mk (i ≫ V.hom) ⟶ V).op) z
  change N.val.map i.op (f.app (op V) (r • x)) =
    N.val.map i.op ((r • · : Γ(N, V.left) → Γ(N, V.left)) (f.app (op V) x))
  rw [N.val.map_smul, ← hn, ← hn, M.val.map_smul]
  exact hi (Over.mk (𝟙 W)) (S.presheaf.map i.op r) (M.val.map i.op x)

/-- The sheaf internal Hom of two actual scheme modules. -/
def internalHom (M N : S.Modules) : S.Modules where
  val := internalHomPresheaf M N
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
    ((Presheaf.isSheaf_of_iso_iff (internalHomTypeIso M N)).mpr
      (linearHomSubfunctor_isSheaf M N))

/-- Sections of the internal Hom are local morphisms on the over-category. -/
def internalHomOverEquiv (M N : S.Modules) (U : S.Opens) :
    Γ(internalHom M N, U) ≃ₗ[Γ(S, U)] LocalHom M N U := LinearEquiv.refl _ _

/-- Sections of the internal Hom identify with morphisms of modules on the open subscheme. -/
def internalHomSectionsEquiv (M N : S.Modules) (U : S.Opens) :
    Γ(internalHom M N, U) ≃ (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (internalHomOverEquiv M N U).toEquiv |>.trans
    ((AlgebraicGeometry.Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv) |>.trans
    (Iso.homCongr ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M)
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app N))

/-- On an open inside the open subscheme, the section equivalence evaluates the same local map. -/
@[simp]
lemma internalHomSectionsEquiv_app (M N : S.Modules) (U : S.Opens)
    (h : Γ(internalHom M N, U)) (V : U.toScheme.Opens) :
    (internalHomSectionsEquiv M N U h).app V =
      (forget₂ _ Ab).map (LocalHom.app h (homOfLE (U.ι_image_le V))) := rfl

@[simp]
lemma internalHomSectionsEquiv_zero (M N : S.Modules) (U : S.Opens) :
    internalHomSectionsEquiv M N U 0 = 0 := by
  ext V x
  rfl

@[simp]
lemma internalHomSectionsEquiv_add (M N : S.Modules) (U : S.Opens)
    (h k : Γ(internalHom M N, U)) :
    internalHomSectionsEquiv M N U (h + k) =
      internalHomSectionsEquiv M N U h + internalHomSectionsEquiv M N U k := by
  ext V x
  rfl

/-- Restriction of internal-Hom sections restricts the associated local morphisms. -/
lemma internalHomSectionsEquiv_restrict_app (M N : S.Modules) {U V : S.Opens}
    (i : V ⟶ U) (h : Γ(internalHom M N, U)) (W : V.toScheme.Opens) :
    (internalHomSectionsEquiv M N V ((internalHom M N).presheaf.map i.op h)).app W =
      (forget₂ _ Ab).map
        (LocalHom.app h (homOfLE ((V.ι_image_le W).trans (leOfHom i)))) := rfl

@[simp]
lemma internalHom_restrict (M N : S.Modules) {U V : S.Opens} (i : V ⟶ U)
    (f : Γ(internalHom M N, U)) :
    (internalHom M N).presheaf.map i.op f = LocalHom.restrict i f := rfl

/-- Evaluate a local module morphism on sections of its open. -/
def internalHomEval (M N : S.Modules) (U : S.Opens) :
    Γ(internalHom M N, U) →ₗ[Γ(S, U)] (Γ(M, U) →ₗ[Γ(S, U)] Γ(N, U)) where
  toFun f := (LocalHom.app f (𝟙 U)).hom
  map_add' f g := rfl
  map_smul' r f := by
    ext x
    change S.presheaf.map (𝟙 U).op r • LocalHom.app f (𝟙 U) x =
      r • LocalHom.app f (𝟙 U) x
    simp

@[simp]
lemma internalHomEval_apply (M N : S.Modules) (U : S.Opens)
    (f : Γ(internalHom M N, U)) (x : Γ(M, U)) :
    internalHomEval M N U f x = LocalHom.app f (𝟙 U) x := rfl

/-- Evaluation commutes with restriction of both the local map and its argument. -/
lemma internalHomEval_restrict (M N : S.Modules) {U V : S.Opens} (i : V ⟶ U)
    (f : Γ(internalHom M N, U)) (x : Γ(M, U)) :
    internalHomEval M N V ((internalHom M N).presheaf.map i.op f) (M.presheaf.map i.op x) =
      N.presheaf.map i.op (internalHomEval M N U f x) :=
  PresheafOfModules.naturality_apply f.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op x

/-- Precomposition and postcomposition give the bifunctorial internal-Hom map. -/
def internalHomMap {M M' N N' : S.Modules} (f : M' ⟶ M) (g : N ⟶ N') :
    internalHom M N ⟶ internalHom M' N' where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun h => f.over U.unop ≫ h ≫ g.over U.unop
          map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp]
          map_smul' := by
            intro r h
            ext V i x
            change g.val.app (op V) (S.presheaf.map i.op r • LocalHom.app h i (f.val.app (op V) x)) =
              S.presheaf.map i.op r • g.val.app (op V) (LocalHom.app h i (f.val.app (op V) x))
            exact (g.val.app (op V)).hom.map_smul _ _ }
      naturality := by intros; ext h; rfl }

@[simp]
lemma internalHomMap_app {M M' N N' : S.Modules} (f : M' ⟶ M) (g : N ⟶ N')
    (U : S.Opens) (h : Γ(internalHom M N, U)) :
    (internalHomMap f g).app U h = f.over U ≫ h ≫ g.over U := rfl

@[simp]
lemma internalHomMap_eval {M M' N N' : S.Modules} (f : M' ⟶ M) (g : N ⟶ N')
    (U : S.Opens) (h : Γ(internalHom M N, U)) (x : Γ(M', U)) :
    internalHomEval M' N' U ((internalHomMap f g).app U h) x =
      g.app U (internalHomEval M N U h (f.app U x)) := rfl

/-- The section identification is natural in both module arguments. -/
lemma internalHomSectionsEquiv_naturality {M M' N N' : S.Modules}
    (f : M' ⟶ M) (g : N ⟶ N') (U : S.Opens) (h : Γ(internalHom M N, U)) :
    internalHomSectionsEquiv M' N' U ((internalHomMap f g).app U h) =
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map f ≫
        internalHomSectionsEquiv M N U h ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map g := by
  ext V x
  rfl

/-- The dual of an actual module sheaf, with values in the actual structure sheaf. -/
def dual (M : S.Modules) : S.Modules := internalHom M (Langlands.SchemeModule.structureModule S)

/-- The contravariant map on duals given by precomposition. -/
def dualMap {M N : S.Modules} (f : M ⟶ N) : dual N ⟶ dual M :=
  internalHomMap f (𝟙 (Langlands.SchemeModule.structureModule S))

@[simp]
lemma dualMap_app {M N : S.Modules} (f : M ⟶ N) (U : S.Opens)
    (h : Γ(dual N, U)) : (dualMap f).app U h = f.over U ≫ h := by
  change f.over U ≫ h ≫ (SheafOfModules.overFunctor S.ringCatSheaf U).map (𝟙 _) = _
  simp

/-- The evaluation pairing of a dual section and a module section. -/
def dualEval (M : S.Modules) (U : S.Opens) :
    Γ(dual M, U) →ₗ[Γ(S, U)] (Γ(M, U) →ₗ[Γ(S, U)] Γ(S, U)) :=
  internalHomEval M (Langlands.SchemeModule.structureModule S) U

@[simp]
lemma dualMap_eval {M N : S.Modules} (f : M ⟶ N) (U : S.Opens)
    (h : Γ(dual N, U)) (x : Γ(M, U)) :
    dualEval M U ((dualMap f).app U h) x = dualEval N U h (f.app U x) := rfl

@[simp]
lemma dualMap_id (M : S.Modules) : dualMap (𝟙 M) = 𝟙 (dual M) := by
  ext U h
  rfl

@[simp]
lemma dualMap_comp {M N P : S.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  ext U h
  rfl

@[simp]
lemma dualMap_zero (M N : S.Modules) : dualMap (0 : M ⟶ N) = 0 := by
  ext U h
  change (0 : LocalHom M N U) ≫ h ≫ 𝟙 _ = 0
  simp

@[simp]
lemma dualMap_add {M N : S.Modules} (f g : M ⟶ N) :
    dualMap (f + g) = dualMap f + dualMap g := by
  ext U h
  change (f.over U + g.over U) ≫ h ≫ 𝟙 _ =
    (f.over U ≫ h ≫ 𝟙 _) + (g.over U ≫ h ≫ 𝟙 _)
  simp [Preadditive.add_comp]

/-- Dualization as a contravariant functor on actual scheme modules. -/
def dualFunctor (S : AlgebraicGeometry.Scheme.{u}) : S.Modulesᵒᵖ ⥤ S.Modules where
  obj M := dual M.unop
  map f := dualMap f.unop
  map_id M := dualMap_id M.unop
  map_comp f g := dualMap_comp g.unop f.unop

instance : (dualFunctor S).Additive where
  map_add {_ _} f g := dualMap_add f.unop g.unop

end Langlands.Scheme.Modules
