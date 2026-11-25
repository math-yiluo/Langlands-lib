/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Module gluing on a finite clopen pro-etale partition

The restriction functors are continuous pushforwards. The gluing theorem specifies its inverse
on sections, morphisms and restriction maps.

## References

* Stacks Project, Tags 04TQ, 04TR and 04TS, finite-disjoint module expansion
* Stacks Project, Tags 04TQ, 04TR, 04TS and 03DB
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Restriction of ring sheaves along composition into a weakly etale open subscheme. -/
abbrev clopenRingRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    RingCat.{u} (topology Y) (topology X)

/-- Restriction of module sheaves, with the unchanged sectionwise scalar actions. -/
abbrev clopenModuleRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    ringedSiteModules.{v} R ⥤ ringedSiteModules.{v} ((clopenRingRestriction j).obj R) :=
  SheafOfModules.pushforward (F := MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale j)) (𝟙 _)

/-- The component of a test object, as an object of the component's own pro-etale site. -/
abbrev clopenTestPiece {X Y : Scheme.{t}} (j : Y ⟶ X) (U : X.ProEt) : Y.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj U

/-- The component projection into the ambient test object. -/
def clopenTestInclusion {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      (clopenTestPiece j U) ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom j) pullback.condition

/-- Restriction of sheaves of modules along an open immersion is additive. -/
theorem clopenModuleRestriction_additive {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    (clopenModuleRestriction.{t, u, v} j R).Additive := by
  constructor
  intro F H f g
  ext U x
  rfl

attribute [instance] clopenModuleRestriction_additive

/-- Restriction to all members of a finite clopen family. -/
abbrev clopenRestriction {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :=
  Functor.pi' (fun i ↦ clopenModuleRestriction.{t, u, v} (j i) R)

/-- The diagonal identification of a component object with its own base change.
This is the unit of the actual composition/base-change adjunction. -/
abbrev clopenDiagonal {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (W : Y.ProEt) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).unit.app W

private theorem clopenHasSheafify (X : Scheme.{t}) :
    HasSheafify (topology X) AddCommGrpCat.{max v (t + 1)} := by
  have : EssentiallySmall.{max v (t + 1)} X.ProEt := essentiallySmallSelf.{v} _
  exact hasSheafifyEssentiallySmallSite.{t, max v (t + 1), t + 1,
    max v (t + 1) + 1, max v (t + 1)} _ _

private theorem clopenWEqualsLocallyBijective (X : Scheme.{t}) :
    (topology X).WEqualsLocallyBijective AddCommGrpCat.{max v (t + 1)} := by
  have : EssentiallySmall.{max v (t + 1)} X.ProEt := essentiallySmallSelf.{v} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t,
    max v (t + 1), t + 1, max v (t + 1) + 1, max v (t + 1)} _

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

private theorem clopenCover {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)) (U : X.ProEt) :
    Sieve.ofArrows
      (fun i ↦ (MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale (j i))).obj (clopenTestPiece (j i) U))
      (fun i ↦ clopenTestInclusion (j i) U) ∈ topology X U := by
  rw [mem_topology_iff]
  refine ⟨Presieve.ofArrows _ (fun i ↦ clopenTestInclusion (j i) U), ?_,
    Sieve.le_generate _⟩
  rw [mem_precoverage_iff, Presieve.map_ofArrows]
  apply Precoverage.mem_coverings_of_isPullback j _ U.hom _
    (fun i ↦ pullback.snd U.hom (j i)) (fun i ↦ IsPullback.of_hasPullback U.hom (j i))
  apply Scheme.etalePrecoverage_le_proetalePrecoverage
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
    ⟨by simpa only [Set.iUnion_eq_univ_iff] using hcover, fun _ ↦ inferInstance⟩

private theorem moduleSections_empty {X : Scheme.{t}} (R : Sheaf (topology X) RingCat.{u})
    (M : ringedSiteModules.{v} R) (U : X.ProEt) [IsEmpty U.left] :
    Subsingleton (M.val.obj (op U)) := by
  have h := isTerminalSectionsOfIsEmpty (SheafOfModules.toSheaf R |>.obj M) U
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (isZero_zero AddCommGrpCat)
      (h.uniqueUpToIso (isZero_zero AddCommGrpCat).isTerminal))

private theorem clopenSections_bijective {X : Scheme.{t}} {I : Type w}
    {Y : I → Scheme.{t}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u}) (M : ringedSiteModules.{v} R) (U : X.ProEt) :
    Function.Bijective (fun x i ↦ M.val.map (clopenTestInclusion (j i) U).op x) := by
  let V (i : I) := (MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale (j i))).obj (clopenTestPiece (j i) U)
  let a (i : I) : V i ⟶ U := clopenTestInclusion (j i) U
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ M.val.presheaf
      (CategoryTheory.forget AddCommGrpCat.{v}) M.isSheaf) (Sieve.ofArrows V a) (clopenCover j hc U)
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsh
  have hm (i : I) : Mono (a i) := by
    constructor
    intro Z f g h
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono (pullback.fst U.hom (j i))).mp
      (congrArg (fun k ↦ k.left) h)
  have he {Z : X.ProEt} {i k : I} (hik : i ≠ k) (f : Z ⟶ V i) (g : Z ⟶ V k)
      (h : f ≫ a i = g ≫ a k) : IsEmpty Z.left := by
    constructor
    intro z
    have hi : (j i) ((pullback.snd U.hom (j i)) (f.left z)) = Z.hom z := by
      change ((f.left ≫ pullback.snd U.hom (j i)) ≫ j i) z = Z.hom z
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (fun q ↦ q z) (MorphismProperty.Over.w (f ≫ a i))
    have hk : (j k) ((pullback.snd U.hom (j k)) (g.left z)) = Z.hom z := by
      change ((g.left ≫ pullback.snd U.hom (j k)) ≫ j k) z = Z.hom z
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (fun q ↦ q z) (MorphismProperty.Over.w (g ≫ a k))
    exact Set.disjoint_left.mp (hd hik) ⟨_, hi⟩ ⟨_, hk⟩
  have hex (x : ∀ i, M.val.obj (op (V i))) :
      ∃! t, ∀ i, M.val.map (a i).op t = x i := by
    apply hsh x
    intro i k Z f g h
    by_cases hik : i = k
    · subst k
      obtain rfl := (cancel_mono (a i)).mp h
      rfl
    · have := he hik f g h
      exact (moduleSections_empty R M Z).elim _ _
  constructor
  · intro x y hxy
    exact (hex (fun i ↦ M.val.map (a i).op x)).unique (fun _ ↦ rfl)
      (fun i ↦ congrFun hxy i |>.symm)
  · intro x
    obtain ⟨t, ht, _⟩ := hex x
    exact ⟨t, funext ht⟩

private def pieceRingMap {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    R ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).sheafPushforwardContinuous
      RingCat (topology X) (topology Y)).obj
        ((clopenRingRestriction j).obj R) where
  hom := Functor.whiskerRight
    (NatTrans.op (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial).counit) R.obj

private def pieceExtension {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    ringedSiteModules.{v} ((clopenRingRestriction j).obj R) ⥤ ringedSiteModules.{v} R := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).IsContinuous
      (topology X) (topology Y) := isContinuous_overPullback j
  exact SheafOfModules.pushforward (pieceRingMap j R)

private def productModules {X : Scheme.{t}} {I : Type w}
    (R : Sheaf (topology X) RingCat.{u})
    (M : I → ringedSiteModules.{max v w (t + 1)} R) :
    ringedSiteModules.{max v w (t + 1)} R := by
  let P : _root_.PresheafOfModules.{max v w (t + 1)} R.obj :=
    { obj U := ModuleCat.of _ (∀ i, (M i).val.obj U)
      map {U V} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
          (ModuleCat.of _ (∀ i, (M i).val.obj V)))
        { toFun := fun x i ↦ (M i).val.map f (x i)
          map_add' := fun x y ↦ funext (fun i ↦ map_add ((M i).val.map f).hom (x i) (y i))
          map_smul' := fun r x ↦ funext (fun i ↦ (M i).val.map_smul f r (x i)) }
      map_id U := by
        ext x
        funext i
        change (M i).val.map (𝟙 U) (x i) = x i
        simp
      map_comp f g := by
        ext x
        funext i
        exact (M i).val.map_comp_apply f g (x i) }
  let c : Fan (fun i ↦ (M i).val) := Fan.mk P (fun i ↦
    { app U := ModuleCat.ofHom (LinearMap.proj i)
      naturality f := by ext x; rfl })
  have hc : IsLimit c :=
    PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun U ↦ by
      refine
        { lift := fun s ↦ ModuleCat.ofHom (LinearMap.pi fun i ↦ (s.π.app ⟨i⟩).hom)
          fac := fun _ _ ↦ rfl
          uniq := ?_ }
      intro s m hm
      ext x
      funext i
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hm ⟨i⟩)) x)
  exact ⟨P, PresheafOfModules.isSheaf_of_isLimit hc (fun i ↦ (M i.as).isSheaf)⟩

private def gluingFunctor {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    (∀ i, ringedSiteModules.{max v w (t + 1)} ((clopenRingRestriction (j i)).obj R)) ⥤
      ringedSiteModules.{max v w (t + 1)} R where
  obj M := productModules.{t, u, v, w} R
    (fun i ↦ (pieceExtension.{t, u, max v w (t + 1)} (j i) R).obj (M i))
  map f :=
    { val.app U := ModuleCat.ofHom
        { toFun := fun x i ↦ ((pieceExtension (j i) R).map (f i)).val.app U (x i)
          map_add' := fun x y ↦ funext (fun i ↦ map_add _ (x i) (y i))
          map_smul' := fun r x ↦ funext (fun i ↦ map_smul _ r (x i)) }
      val.naturality g := by
        ext x
        funext i
        exact (PresheafOfModules.naturality_apply
          ((pieceExtension (j i) R).map (f i)).val g (x i)) }
  map_id M := by ext U x; funext i; rfl
  map_comp f g := by ext U x; funext i; rfl

private def gluingUnit {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    𝟭 (ringedSiteModules.{max v w (t + 1)} R) ⟶
      clopenRestriction j R ⋙ gluingFunctor.{t, u, v, w} j R where
  app M :=
    { val.app U := ModuleCat.ofHom
        { toFun := fun x i ↦ M.val.map (clopenTestInclusion (j i) U.unop).op x
          map_add' := fun x y ↦ funext (fun i ↦ map_add _ x y)
          map_smul' := fun r x ↦ funext (fun i ↦ M.val.map_smul _ r x) }
      val.naturality f := by
        ext x
        funext i
        change (M.val.presheaf.map f ≫ M.val.presheaf.map
          (clopenTestInclusion (j i) _).op) x =
          (M.val.presheaf.map (clopenTestInclusion (j i) _).op ≫
            M.val.presheaf.map _) x
        rw [← Functor.map_comp, ← Functor.map_comp]
        apply CategoryTheory.congr_fun
        apply M.val.presheaf.congr_map
        apply Quiver.Hom.unop_inj
        apply MorphismProperty.Over.Hom.ext
        exact (pullback.lift_fst _ _ _).symm }
  naturality {M N} f := by
    ext U x
    funext i
    exact (PresheafOfModules.naturality_apply f.val
      (clopenTestInclusion (j i) U.unop).op x).symm

private theorem gluingUnit_isIso {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u}) : IsIso (gluingUnit.{t, u, v, w} j R) := by
  have (M : ringedSiteModules.{max v w (t + 1)} R) :
      IsIso ((gluingUnit.{t, u, v, w} j R).app M) := by
    let f := ((gluingUnit.{t, u, v, w} j R).app M).val
    have (U : X.ProEtᵒᵖ) : IsIso (f.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (clopenSections_bijective j hd hc R M U.unop)
    let e := PresheafOfModules.isoMk (fun U ↦ asIso (f.app U)) (fun {_ _} g ↦ f.naturality g)
    have : IsIso f := by change IsIso e.hom; infer_instance
    have : IsIso ((SheafOfModules.forget R).map
        ((gluingUnit.{t, u, v, w} j R).app M)) := by
      change IsIso f
      infer_instance
    exact isIso_of_reflects_iso ((gluingUnit.{t, u, v, w} j R).app M)
      (SheafOfModules.forget R)
  exact NatIso.isIso_of_isIso_app _

private def pieceAdjunction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    clopenModuleRestriction.{t, u, v} j R ⊣ pieceExtension j R := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).IsContinuous
      (topology X) (topology Y) := isContinuous_overPullback j
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  exact SheafOfModules.pushforwardPushforwardAdj adj (𝟙 _) (pieceRingMap j R)
    (by rfl) (by
      ext U : 2
      change R.obj.map _ ≫ R.obj.map _ = 𝟙 _
      change R.obj.map (adj.counit.app (((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U.unop))).op ≫
        R.obj.map (((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).map (adj.unit.app U.unop))).op = 𝟙 _
      rw [← Functor.map_comp, ← op_comp]
      exact (congrArg (fun f ↦ R.obj.map f.op)
        (adj.left_triangle_components U.unop)).trans (R.obj.map_id _))

private def productProjection {X : Scheme.{t}} {I : Type w}
    (R : Sheaf (topology X) RingCat.{u})
    (M : I → ringedSiteModules.{max v w (t + 1)} R) (i : I) :
    productModules.{t, u, v, w} R M ⟶ M i where
  val.app U := ModuleCat.ofHom (LinearMap.proj i)
  val.naturality f := by ext x; rfl

private def gluingCounit {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    gluingFunctor.{t, u, v, w} j R ⋙ clopenRestriction j R ⟶ 𝟭 _ where
  app F i :=
    (clopenModuleRestriction (j i) R).map
        (productProjection.{t, u, v, w} R
          (fun k ↦ (pieceExtension (j k) R).obj (F k)) i) ≫
      (pieceAdjunction (j i) R).counit.app (F i)
  naturality {F H} f := by
    funext i
    ext W x
    exact (PresheafOfModules.naturality_apply (f i).val
      (clopenDiagonal (j i) W.unop).op (x i)).symm

private theorem clopenDiagonal_isIso {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (W : Y.ProEt) : IsIso (clopenDiagonal j W) := by
  let V := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W
  let q : clopenTestPiece j V ⟶ W :=
    MorphismProperty.Over.homMk (pullback.fst V.hom j) (by
      apply (cancel_mono j).mp
      change pullback.fst V.hom j ≫ (W.hom ≫ j) = pullback.snd V.hom j ≫ j
      exact pullback.condition)
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  · apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (pullback.fst V.hom j)).mp
    simp [q, clopenDiagonal, MorphismProperty.Over.mapPullbackAdj, V]

private theorem offDiagonal_empty {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) (hd : Pairwise
      (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    [∀ i, IsOpenImmersion (j i)] {i k : I} (hik : i ≠ k) (W : (Y i).ProEt) :
    IsEmpty (clopenTestPiece (j k) ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale (j i))).obj W)).left := by
  constructor
  intro z
  exact Set.disjoint_left.mp (hd hik)
    ⟨W.hom (pullback.fst (W.hom ≫ j i) (j k) z), rfl⟩
    ⟨pullback.snd (W.hom ≫ j i) (j k) z,
      congrArg (fun f ↦ f z) (pullback.condition (f := W.hom ≫ j i) (g := j k)).symm⟩

private theorem gluingCounit_isIso {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (R : Sheaf (topology X) RingCat.{u}) :
    IsIso (gluingCounit.{t, u, v, w} j R) := by
  classical
  have (F : ∀ i, ringedSiteModules.{max v w (t + 1)}
      ((clopenRingRestriction (j i)).obj R)) (i : I) :
      IsIso (((gluingCounit.{t, u, v, w} j R).app F) i) := by
    let f := (((gluingCounit.{t, u, v, w} j R).app F) i).val
    have (W : (Y i).ProEtᵒᵖ) : IsIso (f.app W) := by
      have := clopenDiagonal_isIso (j i) W.unop
      have hinj : Function.Bijective
          (fun x ↦ (F i).val.map (clopenDiagonal (j i) W.unop).op x) := by
        exact (ConcreteCategory.bijective_of_isIso
          ((F i).val.presheaf.map (clopenDiagonal (j i) W.unop).op))
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      constructor
      · intro x y h
        funext k
        by_cases hk : i = k
        · subst k
          exact hinj.injective h
        · have he := offDiagonal_empty j hd hk W.unop
          exact @Subsingleton.elim _
            (@moduleSections_empty _ _ (F k) _ he) _ _
      · intro y
        obtain ⟨x, hx⟩ := hinj.surjective y
        let z : ∀ k, (F k).val.obj
            (op (clopenTestPiece (j k) ((MorphismProperty.Over.map ⊤
              (inferInstance : WeaklyEtale (j i))).obj W.unop))) :=
          fun k ↦ if h : k = i then by subst k; exact x else 0
        refine ⟨z, ?_⟩
        change (F i).val.map (clopenDiagonal (j i) W.unop).op (z i) = y
        simpa only [z, dite_eq_left rfl] using hx
    let e := PresheafOfModules.isoMk (fun W ↦ asIso (f.app W)) (fun {_ _} g ↦ f.naturality g)
    have : IsIso f := by change IsIso e.hom; infer_instance
    have : IsIso ((SheafOfModules.forget _).map
        (((gluingCounit.{t, u, v, w} j R).app F) i)) := by
      change IsIso f
      infer_instance
    exact isIso_of_reflects_iso (((gluingCounit.{t, u, v, w} j R).app F) i)
      (SheafOfModules.forget _)
  have (F : ∀ i, ringedSiteModules.{max v w (t + 1)}
      ((clopenRingRestriction (j i)).obj R)) :
      IsIso ((gluingCounit.{t, u, v, w} j R).app F) := by
    exact (isIso_pi_iff _).mpr (fun i ↦ inferInstance)
  exact NatIso.isIso_of_isIso_app _

private def gluingEquivalence {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u}) :
    ringedSiteModules.{max v w (t + 1)} R ≌
      (∀ i, ringedSiteModules.{max v w (t + 1)} ((clopenRingRestriction (j i)).obj R)) := by
  have := gluingUnit_isIso.{t, u, v, w} j hd hc R
  have := gluingCounit_isIso.{t, u, v, w} j hd R
  exact
    { functor := clopenRestriction j R
      inverse := gluingFunctor.{t, u, v, w} j R
      unitIso := asIso (gluingUnit.{t, u, v, w} j R)
      counitIso := asIso (gluingCounit.{t, u, v, w} j R)
      functor_unitIso_comp M := by
        funext i
        ext W x
        exact congrArg (fun f ↦ f.val.app W x)
          ((pieceAdjunction (j i) R).left_triangle_components M) }

private theorem gluingFunctor_additive {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    (gluingFunctor.{t, u, v, w} j R).Additive := by
  constructor
  intro M N f g
  ext U x
  funext i
  rfl

private theorem emptyModuleCategory {X : Scheme.{t}} [IsEmpty X]
    (R : Sheaf (topology X) RingCat.{u}) :
    Nonempty (ringedSiteModules.{max v (t + 1)} R ≌ Discrete PUnit) := by
  have := clopenHasSheafify.{t, v} X
  have := clopenWEqualsLocallyBijective.{t, v} X
  apply (equiv_punit_iff_unique _).mpr
  refine ⟨⟨HasZeroObject.zero.choose⟩, fun M N ↦ ?_⟩
  have hsub : Subsingleton (M ⟶ N) := by
    constructor
    intro f g
    ext U x
    have : IsEmpty U.unop.left :=
      ⟨fun x ↦ (inferInstance : IsEmpty X).false (U.unop.hom x)⟩
    exact (moduleSections_empty R N U.unop).elim _ _
  exact ⟨{ default := 0, uniq := fun _ ↦ hsub.elim _ _ }⟩

private def jointlyIsLimit
    {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
    (r : C ⥤ ∀ i, D i) [r.IsEquivalence]
    {J : Type*} [Category J] {F : J ⥤ C} (c : Cone F)
    (h : ∀ i, IsLimit ((r ⋙ Pi.eval D i).mapCone c)) : IsLimit c := by
  apply isLimitOfReflects r
  refine { lift := fun s i ↦ (h i).lift ((Pi.eval D i).mapCone s)
           fac := ?_, uniq := ?_ }
  · intro s j
    funext i
    exact (h i).fac ((Pi.eval D i).mapCone s) j
  · intro s m hm
    funext i
    apply (h i).uniq ((Pi.eval D i).mapCone s) (m i)
    intro j
    exact congrFun (hm j) i

private def jointlyIsColimit
    {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
    (r : C ⥤ ∀ i, D i) [r.IsEquivalence]
    {J : Type*} [Category J] {F : J ⥤ C} (c : Cocone F)
    (h : ∀ i, IsColimit ((r ⋙ Pi.eval D i).mapCocone c)) : IsColimit c := by
  apply isColimitOfReflects r
  refine { desc := fun s i ↦ (h i).desc ((Pi.eval D i).mapCocone s)
           fac := ?_, uniq := ?_ }
  · intro s j
    funext i
    exact (h i).fac ((Pi.eval D i).mapCocone s) j
  · intro s m hm
    funext i
    apply (h i).uniq ((Pi.eval D i).mapCocone s) (m i)
    intro j
    exact congrFun (hm j) i

private def coordinateTransport {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] {i k : J} (h : i = k) : D i ⥤ D k := by
  subst k
  exact 𝟭 _

private def coordinateInsertion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] (i : J) : D i ⥤ ∀ k, D k := by
  classical
  exact Functor.pi' (fun k ↦ if h : i = k then coordinateTransport D h
    else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))

private def coordinateProjection {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : 𝟭 (∀ k, D k) ⟶ Pi.eval D i ⋙ coordinateInsertion D i := by
  classical
  apply NatTrans.pi'
  intro k
  change Pi.eval D k ⟶ Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).inv
  · exact 0

private def coordinateInclusion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : Pi.eval D i ⋙ coordinateInsertion D i ⟶ 𝟭 (∀ k, D k) := by
  classical
  apply NatTrans.pi'
  intro k
  change (Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose)))
      ⟶ Pi.eval D k
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).hom
  · exact 0

private def coordinateBicone {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    Bicone (fun i ↦ Pi.eval D i ⋙ coordinateInsertion D i) := by
  classical
  refine
    { pt := 𝟭 _
      π := coordinateProjection D
      ι := coordinateInclusion D
      ι_π := ?_ }
  intro i k
  by_cases h : i = k
  · subst k
    simp only [dite_true, eqToHom_refl]
    apply NatTrans.ext
    funext M l
    by_cases hl : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, coordinateInsertion,
        coordinateTransport, NatTrans.pi', Functor.pi', Pi.eval]
    · have hz : IsZero ((coordinateInsertion D i).obj (M i) l) := by
        simpa only [coordinateInsertion, Functor.pi'_obj, dite_eq_right hl, Functor.const_obj_obj]
          using (HasZeroObject.zero (C := D l)).choose_spec
      exact hz.eq_of_src _ _
  · simp only [dite_eq_right h]
    apply NatTrans.ext
    funext M l
    by_cases hi : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, NatTrans.pi', Ne.symm h]
      rfl
    · simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
      rfl

private theorem coordinateBicone_total {J : Type*} [Fintype J] (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    ∑ i, (coordinateBicone D).π i ≫ (coordinateBicone D).ι i = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext M k
  rw [NatTrans.app_sum]
  rw [Finset.sum_apply]
  change (∑ i, (coordinateProjection D i).app M k ≫
    (coordinateInclusion D i).app M k) = 𝟙 (M k)
  rw [Finset.sum_eq_single k]
  · simp [coordinateProjection, coordinateInclusion, NatTrans.pi',
      coordinateTransport]
  · intro i _ hi
    simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
  · simp

private theorem clopenRestriction_preservesFiniteLimits {X Y : Scheme.{t}}
    (j : Y ⟶ X) [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (clopenModuleRestriction.{t, u, v} j R) := by
  let Ri := (clopenRingRestriction j).obj R
  let V := SheafOfModules.forget.{v} Ri ⋙ PresheafOfModules.toPresheaf Ri.obj
  have : PreservesFiniteLimits
      (clopenModuleRestriction.{t, u, v} j R ⋙ V) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{v} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ AddCommGrpCat.{v}).obj
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ V

private theorem clopenRestrictions_preservesFiniteLimits {X : Scheme.{t}} {I : Type w}
    {Y : I → Scheme.{t}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (clopenRestriction.{t, u, v, w} j R) := by
  have (i : I) : PreservesFiniteLimits (clopenModuleRestriction.{t, u, v} (j i) R) :=
    clopenRestriction_preservesFiniteLimits (j i) R
  constructor
  intro J _ _
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨?_⟩
  refine { lift := fun s i ↦ (isLimitOfPreserves
      (clopenModuleRestriction (j i) R) hc).lift ((Pi.eval _ i).mapCone s)
           fac := ?_, uniq := ?_ }
  · intro s x
    funext i
    exact (isLimitOfPreserves (clopenModuleRestriction (j i) R) hc).fac _ x
  · intro s m hm
    funext i
    exact (isLimitOfPreserves (clopenModuleRestriction (j i) R) hc).uniq
      ((Pi.eval _ i).mapCone s) (m i)
      (fun x ↦ congrFun (hm x) i)

private theorem clopenRestrictions_preservesFiniteColimits {X : Scheme.{t}} {I : Type w}
    {Y : I → Scheme.{t}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteColimits (clopenRestriction.{t, u, v, w} j R) := by
  have (i : I) : PreservesColimits (clopenModuleRestriction.{t, u, v} (j i) R) :=
    (pieceAdjunction (j i) R).leftAdjoint_preservesColimits
  constructor
  intro J _ _
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨?_⟩
  refine { desc := fun s i ↦ (isColimitOfPreserves
      (clopenModuleRestriction (j i) R) hc).desc ((Pi.eval _ i).mapCocone s)
           fac := ?_, uniq := ?_ }
  · intro s x
    funext i
    exact (isColimitOfPreserves (clopenModuleRestriction (j i) R) hc).fac _ x
  · intro s m hm
    funext i
    exact (isColimitOfPreserves (clopenModuleRestriction (j i) R) hc).uniq
      ((Pi.eval _ i).mapCocone s) (m i)
      (fun x ↦ congrFun (hm x) i)

private theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) := by
  classical
  let := Fintype.ofFinite J
  let s := coordinateInsertion D
  let e (i : J) := s i ⋙ E.inverse
  have hs (i : J) : s i ⋙ Pi.eval D i ≅ 𝟭 _ := by
    dsimp only [s, coordinateInsertion]
    refine Functor.pi'CompEval _ i ≪≫ ?_
    simpa only [dite_true, coordinateTransport] using (Iso.refl (𝟭 (D i)))
  have hz (i k : J) (h : k ≠ i) (M : D i) : IsZero ((s i).obj M k) := by
    simpa [s, coordinateInsertion, Ne.symm h] using (HasZeroObject.zero (C := D k)).choose_spec
  refine ⟨e, ?_, ?_, ⟨s, fun i ↦ ⟨rfl, ⟨hs i⟩, hz i⟩⟩, ?_⟩
  · intro i
    exact ⟨Functor.associator (s i) E.inverse (E.functor ⋙ Pi.eval D i) ≪≫
      Functor.isoWhiskerLeft (s i) ((Functor.associator E.inverse E.functor (Pi.eval D i)).symm ≪≫
        Functor.isoWhiskerRight E.counitIso (Pi.eval D i) ≪≫ Functor.leftUnitor _) ≪≫ hs i⟩
  · intro i k hik M
    exact IsZero.of_iso (hz k i hik M) (Pi.isoApp (E.counitIso.app ((s k).obj M)) i)
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ (C ⥤ C) :=
      (Functor.whiskeringLeft C (∀ i, D i) (∀ i, D i)).obj E.functor ⋙
        (Functor.whiskeringRight C (∀ i, D i) C).obj E.inverse
    have : H.Additive := inferInstance
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    let b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i) :=
      { pt := 𝟭 _
        π i := E.unitIso.hom ≫ b'.π i
        ι i := b'.ι i ≫ E.unitIso.inv
        ι_π i k := by
          change (b'.ι i ≫ E.unitIso.inv) ≫ (E.unitIso.hom ≫ b'.π k) = _
          rw [Category.assoc, Iso.inv_hom_id_assoc]
          exact b'.ι_π i k }
    refine ⟨b, rfl, ⟨isBilimitOfTotal b ?_⟩⟩
    change ∑ i, (E.unitIso.hom ≫ b'.π i) ≫ (b'.ι i ≫ E.unitIso.inv) = 𝟙 _
    have ht' : ∑ i, b'.π i ≫ b'.ι i = 𝟙 (E.functor ⋙ E.inverse) := ht
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id] using
      congrArg (fun f ↦ E.unitIso.hom ≫ f ≫ E.unitIso.inv) ht'

/-- Exact gluing of arbitrary commutative-ring module sheaves on a finite clopen cover.
The section equivalences specify the product formula for G, its componentwise maps,
its scalar action, its restriction maps, the restriction unit and the projection counit.
The functors e_i are characterized as G applied to a tuple supported in coordinate i.
The bicone with vertex the identity is the natural direct-sum decomposition. -/
theorem clopen_ringed_module_gluing
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u})
    (hcomm : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ (G : (∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R)) ⥤
          ringedSiteModules.{max v w (t + 1)} R)
      (η : 𝟭 _ ≅ clopenRestriction j R ⋙ G)
      (ε : G ⋙ clopenRestriction j R ≅ 𝟭 _),
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f g : F ⟶ H) i,
        (clopenModuleRestriction (j i) R).map (f + g) =
          (clopenModuleRestriction (j i) R).map f +
            (clopenModuleRestriction (j i) R).map g) ∧
      Nonempty (Abelian (∀ i, ringedSiteModules.{max v w (t + 1)}
        ((clopenRingRestriction (j i)).obj R))) ∧
      (∀ (F H : ∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R)) (f g : F ⟶ H),
        G.map (fun i ↦ f i + g i) = G.map f + G.map g) ∧
      PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) ∧
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      (∀ F, (clopenRestriction j R).map (η.hom.app F) ≫
        ε.hom.app ((clopenRestriction j R).obj F) = 𝟙 _) ∧
      (∀ F, η.hom.app (G.obj F) ≫ G.map (ε.hom.app F) = 𝟙 _) ∧
      (∃ σ : ∀ F U, (G.obj F).val.obj (op U) ≃+
          (∀ i, (F i).val.obj (op (clopenTestPiece (j i) U))),
        (∀ F U (a : R.obj.obj (op U)) x i,
          σ F U (a • x) i = R.obj.map (clopenTestInclusion (j i) U).op a • σ F U x i) ∧
        (∀ F (U V : X.ProEt) (f : V ⟶ U) x i,
          σ F V ((G.obj F).val.map f.op x) i =
            (F i).val.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j i)).map f).op
              (σ F U x i)) ∧
        (∀ F H (f : F ⟶ H) U x i,
          σ H U ((G.map f).val.app (op U) x) i =
            (f i).val.app (op (clopenTestPiece (j i) U)) (σ F U x i)) ∧
        (∀ F U x i, σ ((clopenRestriction j R).obj F) U
            ((η.hom.app F).val.app (op U) x) i =
          F.val.map (clopenTestInclusion (j i) U).op x) ∧
        (∀ F i (W : (Y i).ProEt) x,
          ((ε.hom.app F) i).val.app (op W) x =
            (F i).val.map (clopenDiagonal (j i) W).op
              (σ F ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (j i))).obj W) x i))) ∧
      (∃ e : ∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R) ⥤
          ringedSiteModules.{max v w (t + 1)} R,
        (∀ i, Nonempty (e i ⋙ clopenModuleRestriction (j i) R ≅ 𝟭 _)) ∧
        (∀ i k, i ≠ k → ∀ M,
          IsZero ((e k ⋙ clopenModuleRestriction (j i) R).obj M)) ∧
        (∃ s : ∀ i, ringedSiteModules.{max v w (t + 1)}
            ((clopenRingRestriction (j i)).obj R) ⥤
            (∀ k, ringedSiteModules.{max v w (t + 1)}
              ((clopenRingRestriction (j k)).obj R)),
          ∀ i, e i = s i ⋙ G ∧
            Nonempty (s i ⋙ Pi.eval (fun k ↦ ringedSiteModules.{max v w (t + 1)}
              ((clopenRingRestriction (j k)).obj R)) i ≅ 𝟭 _) ∧
            (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
        (∃ b : Bicone (fun i ↦ clopenModuleRestriction (j i) R ⋙ e i),
          b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit)) ∧
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f : F ⟶ H)
        (c : KernelFork f), Nonempty (IsLimit c) ↔
          ∀ i, Nonempty (IsLimit ((clopenModuleRestriction (j i) R).mapCone c))) ∧
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f : F ⟶ H)
        (c : CokernelCofork f), Nonempty (IsColimit c) ↔
          ∀ i, Nonempty (IsColimit ((clopenModuleRestriction (j i) R).mapCocone c))) ∧
      (∀ S : ShortComplex (ringedSiteModules.{max v w (t + 1)} R),
        S.Exact ↔ ∀ i, (S.map (clopenModuleRestriction (j i) R)).Exact) ∧
      (∀ i, IsEmpty (Y i) → Nonempty
        (ringedSiteModules.{max v w (t + 1)} ((clopenRingRestriction (j i)).obj R) ≌
          Discrete PUnit)) ∧
      (IsEmpty I → IsEmpty X ∧ Nonempty
        (ringedSiteModules.{max v w (t + 1)} R ≌ Discrete PUnit)) := by
  classical
  have _ := hcomm
  have (Z : Scheme.{t}) : HasSheafify (topology Z)
      AddCommGrpCat.{max v w (t + 1)} := clopenHasSheafify.{t, max v w} Z
  have (Z : Scheme.{t}) : (topology Z).WEqualsLocallyBijective
      AddCommGrpCat.{max v w (t + 1)} := clopenWEqualsLocallyBijective.{t, max v w} Z
  let E := gluingEquivalence.{t, u, v, w} j hdisjoint hcover R
  let D (i : I) := ringedSiteModules.{max v w (t + 1)}
    ((clopenRingRestriction (j i)).obj R)
  have : E.inverse.Additive := gluingFunctor_additive.{t, u, v, w} j R
  have : HasFiniteProducts (∀ i, D i) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.inverse⟩
  have (i : I) : PreservesFiniteLimits
      (clopenModuleRestriction.{t, u, max v w (t + 1)} (j i) R) :=
    clopenRestriction_preservesFiniteLimits.{t, u, max v w (t + 1)} (j i) R
  have (i : I) : PreservesColimits
      (clopenModuleRestriction.{t, u, max v w (t + 1)} (j i) R) :=
    (pieceAdjunction (j i) R).leftAdjoint_preservesColimits
  refine ⟨E.inverse, E.unitIso, E.counitIso, ?_, ⟨abelianOfEquivalence E.inverse⟩, ?_,
    (clopenRestrictions_preservesFiniteLimits j R),
    (clopenRestrictions_preservesFiniteColimits j R),
    inferInstance, inferInstance, E.functor_unitIso_comp, E.unit_inverse_comp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F H f g i
    exact Functor.map_add _
  · intro F H f g
    exact Functor.map_add E.inverse
  · refine ⟨fun F U ↦ AddEquiv.refl _, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; rfl
  · exact equivalenceCoordinateDecomposition D E
  · intro F H f c
    constructor
    · rintro ⟨hc⟩ i
      exact ⟨isLimitOfPreserves (clopenModuleRestriction (j i) R) hc⟩
    · intro hc
      exact ⟨jointlyIsLimit E.functor c (fun i ↦ (hc i).some)⟩
  · intro F H f c
    constructor
    · rintro ⟨hc⟩ i
      exact ⟨isColimitOfPreserves (clopenModuleRestriction (j i) R) hc⟩
    · intro hc
      exact ⟨jointlyIsColimit E.functor c (fun i ↦ (hc i).some)⟩
  · intro S
    constructor
    · intro h i
      exact h.map (clopenModuleRestriction (j i) R)
    · intro h
      apply (S.exact_iff_of_forks (kernelIsKernel S.g) (cokernelIsCokernel S.f)).mpr
      apply E.functor.map_injective
      funext i
      have hi := ((S.map (clopenModuleRestriction (j i) R)).exact_iff_of_forks
        (KernelFork.mapIsLimit _ (kernelIsKernel S.g) (clopenModuleRestriction (j i) R))
        (CokernelCofork.mapIsColimit _ (cokernelIsCokernel S.f)
          (clopenModuleRestriction (j i) R))).mp (h i)
      change (clopenModuleRestriction (j i) R).map (kernel.ι S.g) ≫
        (clopenModuleRestriction (j i) R).map (cokernel.π S.f) = 0 at hi
      change (clopenModuleRestriction (j i) R).map (kernel.ι S.g) ≫
        (clopenModuleRestriction (j i) R).map (cokernel.π S.f) = 0
      exact hi
  · intro i hi
    let := hi
    exact emptyModuleCategory.{t, u, max v w} _
  · intro hi
    have hX : IsEmpty X := ⟨fun x ↦ hi.false (hcover x).choose⟩
    let := hX
    exact ⟨hX, emptyModuleCategory.{t, u, max v w} R⟩

private def constantComparison {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{max u (t + 1)}) :
    (clopenRingRestriction j).obj
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (topology X) CommRingCat.{max u (t + 1)}).obj A)) ≅
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (topology Y) CommRingCat.{max u (t + 1)}).obj A) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (sheafCompose (topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
    ((F.pushforwardContinuousSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
        (topology X)).app ((Functor.const X.ProEtᵒᵖ).obj A)).symm

private theorem constantComparison_sections {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{max u (t + 1)}) (W : Y.ProEt) :
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
        (constantComparison.{t, u} j A).hom.hom.app (op W) =
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        ((toSheafify (topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app (op W)) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have h := congrArg (fun f ↦ f.app (op W))
    (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
      (topology X) ((Functor.const X.ProEtᵒᵖ).obj A))
  let c := (F.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj A)
  change (forget₂ CommRingCat RingCat).map
      ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (F.op.obj (op W)) ≫
        c.inv.hom.app (op W)) = _
  apply (forget₂ CommRingCat RingCat).congr_map
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  apply (cancel_mono (c.hom.hom.app (op W))).mp
  have hc : c.inv.hom.app (op W) ≫ c.hom.hom.app (op W) = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.app (op W)) c.inv_hom_id
  rw [Category.assoc, hc]
  erw [Category.comp_id]
  exact h.symm

private theorem constantComparison_naturality {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (clopenRingRestriction j).map
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (topology X) CommRingCat.{max u (t + 1)}).map f)) ≫
        (constantComparison.{t, u} j B).hom =
      (constantComparison.{t, u} j A).hom ≫
        (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (topology Y) CommRingCat.{max u (t + 1)}).map f) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (sheafCompose (topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).congr_map
    ((F.pushforwardContinuousSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
      (topology X)).inv.naturality ((Functor.const X.ProEtᵒᵖ).map f))

private theorem ringRestriction_preservesLimits {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    PreservesLimitsOfShape ℕᵒᵖ (clopenRingRestriction.{t, max u (t + 1)} j) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : PreservesLimitsOfShape ℕᵒᵖ
      (clopenRingRestriction.{t, max u (t + 1)} j ⋙
        sheafToPresheaf (topology Y) RingCat.{max u (t + 1)}) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (topology X) RingCat.{max u (t + 1)} ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj F.op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (topology Y) RingCat.{max u (t + 1)})

end AlgebraicGeometry.Scheme.ProEt
