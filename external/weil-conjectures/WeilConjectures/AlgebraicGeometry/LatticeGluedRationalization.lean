/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import Mathlib.CategoryTheory.Sites.SheafHom
/-!
# The map from a glued integral module to its rational sheaf

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60.
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective

attribute [local instance] AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOver
  AlgebraicGeometry.ProEtale.restrictionWeakSheafifyOverOver
  AlgebraicGeometry.ProEtale.restrictionWEqualsOverOver
  AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOverOver
universe u v w r m s
open CategoryTheory Opposite
open scoped ChangeOfRings
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Cᵒᵖ ⥤ CommRingCat.{r})
  (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat.{r}))
  (M N : SheafOfModules.{m} ⟨R ⋙ forget₂ CommRingCat RingCat.{r}, hR⟩)
  {I : Type w} (W : I → C) (hW : J.CoversTop W)
  (φ : ∀ i, M.over (W i) ⟶ N.over (W i))
  (hφ : ∀ i j (V : C) (a : V ⟶ W i) (b : V ⟶ W j)
    (z : M.val.obj (op V)),
    (φ i).val.app (op (Over.mk a)) z = (φ j).val.app (op (Over.mk b)) z)
include hW hφ in
theorem exists_hom_of_coversTop :
    ∃ f : M ⟶ N, ∀ i (V : C) (a : V ⟶ W i) (z : M.val.obj (op V)),
      f.val.app (op V) z = (φ i).val.app (op (Over.mk a)) z := by
  classical
  let P := M.val.presheaf
  let Q := N.val.presheaf
  let localMap : Presheaf.FamilyOfElementsOnObjects (presheafHom P Q) W := fun i ↦
    (PresheafOfModules.toPresheaf _).map (φ i).val
  have hc : localMap.IsCompatible := by
    intro V i j a b
    apply NatTrans.ext
    funext T
    obtain ⟨T⟩ := T
    ext z
    exact hφ i j T.left (T.hom ≫ a) (T.hom ≫ b) z
  obtain ⟨s, hs, _⟩ := hc.existsUnique_section hW (N.isSheaf.hom P)
  let α := presheafHomSectionsEquiv P Q s
  have happ (i : I) (V : C) (a : V ⟶ W i) :
      α.app (op V) = (forget₂ _ AddCommGrpCat).map ((φ i).val.app (op (Over.mk a))) := by
    change (s.val (op V)).app (op (Over.mk (𝟙 V))) = _
    rw [← s.property a.op, hs i]
    exact presheafHom_map_app_op_mk_id a (localMap i)
  have hlinear (V : C) (r : R.obj (op V)) (z : M.val.obj (op V)) :
      α.app (op V) (r • z) =
        ((r • ·) : N.val.obj (op V) → N.val.obj (op V)) (α.app (op V) z) := by
    have hN : Presieve.IsSheaf J (Q ⋙ CategoryTheory.forget AddCommGrpCat.{m}) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (Presheaf.isSheaf_comp_of_isSheaf J Q (CategoryTheory.forget AddCommGrpCat.{m}) N.isSheaf)
    apply (hN.isSeparated _ (hW V)).ext
    rintro Z f ⟨i, ⟨a⟩⟩
    have hn (y : M.val.obj (op V)) :
        N.val.map f.op (α.app (op V) y) = α.app (op Z) (M.val.map f.op y) :=
      (ConcreteCategory.congr_hom (α.naturality f.op) y).symm
    change N.val.map f.op (α.app (op V) (r • z)) =
      N.val.map f.op
        (((r • ·) : N.val.obj (op V) → N.val.obj (op V)) (α.app (op V) z))
    rw [hn, (M.val.map f.op).hom.map_smul, (N.val.map f.op).hom.map_smul, hn, happ i Z a]
    exact ((φ i).val.app (op (Over.mk a))).hom.map_smul _ _
  let f : M ⟶ N :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom
          { toFun := (α.app V).hom
            map_add' := (α.app V).hom.map_add
            map_smul' := hlinear V.unop }
        naturality := by
          intro V V' g
          ext z
          exact ConcreteCategory.congr_hom (α.naturality g) z } }
  refine ⟨f, ?_⟩
  intro i V a z
  exact ConcreteCategory.congr_hom (happ i V a) z
end SheafOfModules

namespace AlgebraicGeometry.ProEtale
set_option backward.isDefEq.respectTransparency false
theorem extendScalars_one {A : Type r} {B : Type s} [CommRing A] [CommRing B]
    (f : A →+* B) {M : ModuleCat.{max r s m} A} {N : ModuleCat.{max r s m} B}
    (e : M ⟶ (ModuleCat.restrictScalars f).obj N) (m : M) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f e)
      ((1 : B) ⊗ₜ[A, f] m) = e m := by
  let : Module A B := Module.compHom B f
  let : Module A N := Module.compHom N f
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  exact one_smul B (e m)

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  (U : X.ProEt)
set_option hygiene false in
local notation "𝓡" => (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
set_option hygiene false in
local notation "𝓢" => (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
set_option hygiene false in
local notation "N" => (SheafOfModules.restrictScalars.{u + 1}
  ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (latticeScalarMap a U))).obj (L.over U)
variable (M : SheafOfModules.{u + 1} ((𝓡).over U)) (e : M ⟶ N)
noncomputable def rationalizeEmbeddingPresheaf :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M ⟶
      (L.over U).val where
  app T := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    ((latticeScalarMap a U).hom.app T).hom (e.val.app T)
  naturality := by
    intro T T' f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      ((latticeScalarMap a U).hom.app T').hom (e.val.app T'))
      (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) M f
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m)) =
      (L.over U).val.map f
        ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          ((latticeScalarMap a U).hom.app T).hom (e.val.app T))
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m))
    have h := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f) (1 : (S.over U).obj.obj T) m
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f _ = _ at h
    rw [h, map_one]
    exact (extendScalars_one.{u + 1, u + 1, u + 1} ((latticeScalarMap a U).hom.app T').hom
      (e.val.app T') (M.val.map f m)).trans
      ((PresheafOfModules.naturality_apply e.val f m).trans
        (congrArg ((L.over U).val.map f)
          (extendScalars_one.{u + 1, u + 1, u + 1} ((latticeScalarMap a U).hom.app T).hom
            (e.val.app T) m).symm))

noncomputable def rationalizeEmbedding :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M ⟶ L.over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 ((𝓢).over U).obj)
    (P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)
    (F := L.over U)).symm
    (rationalizeEmbeddingPresheaf a L U M e)

theorem rationalizeEmbedding_unit (T : (Over U)ᵒᵖ) (m : M.val.obj T) :
    (rationalizeEmbedding a L U M e).val.app T
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m)) = e.val.app T m := by
  have h := (PresheafOfModules.sheafificationHomEquiv (𝟙 ((𝓢).over U).obj)
    (P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)
    (F := L.over U)).apply_symm_apply
    (rationalizeEmbeddingPresheaf a L U M e)
  have h' := congrArg (fun η ↦ η.app T
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m)) h
  exact h'.trans (extendScalars_one.{u + 1, u + 1, u + 1}
    (A := (R.over U).obj.obj T) (B := (S.over U).obj.obj T) _ _ _)

variable (ha : ∀ (V : X.ProEt) T,
    Function.Injective (((latticeScalarMap a V).hom.app T).hom))
  (r : Sieve U)
  (x : Presieve.FamilyOfElements (latticeClassPresheaf a L) r.arrows)
  (hx : x.Compatible)

noncomputable def latticeCoverEmbeddingHom (i : latticeCoverIndex U r) :
    latticeCoverModule a L U r x i ⟶ (N).over (latticeCoverObject U r i) := by
  letI : (latticeCoverObject U r i).iteratedSliceForward.IsContinuous
      (((Scheme.ProEt.topology X).over U).over (latticeCoverObject U r i))
      ((Scheme.ProEt.topology X).over i.1) :=
    inferInstanceAs ((latticeCoverObject U r i).iteratedSliceForward.IsContinuous
      _ ((Scheme.ProEt.topology X).over (latticeCoverObject U r i).left))
  exact (SheafOfModules.pushforward (F := (latticeCoverObject U r i).iteratedSliceForward)
    (𝟙 _)).map (pairEmbedding a L i.1 (latticeCoverPair a L U r x i))

/-- The local lattice embeddings glue to a morphism from the tuple module.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices.
(auxiliary; not a blueprint node).
Proof: compose each tuple projection with its local integral embedding. The
transition formula and tuple compatibility identify these maps on all overlap
tests. The sheaf Hom glues the underlying additive maps; scalar linearity can
be checked on the covering family, so the glued map is a module morphism. -/
theorem exists_gluedLatticeEmbedding (hr : r ∈ (Scheme.ProEt.topology X) U) :
    ∃ e : gluedLatticeModule a L ha U r x hx ⟶ N,
      ∀ (i : latticeCoverIndex U r) (W : Over U)
        (b : W ⟶ latticeCoverObject U r i)
        (m : (gluedLatticeModule a L ha U r x hx).val.obj (op W)),
        e.val.app (op W) m = latticeCoverEmbedding a L U r x i W b
          ((gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app
            (op (Over.mk b)) m) := by
  let φ := fun i ↦ (gluedLatticeModuleLocalIso a L ha U r x hx i).hom ≫
    latticeCoverEmbeddingHom a L U r x i
  apply SheafOfModules.exists_hom_of_coversTop ((R.over U).obj)
    ((𝓡).over U).property (gluedLatticeModule a L ha U r x hx) N
    (latticeCoverObject U r) (latticeCover_coversTop U r hr) φ
  intro i j W b c m
  change latticeCoverEmbedding a L U r x i W b _ =
    latticeCoverEmbedding a L U r x j W c _
  exact (latticeCoverTransition_spec a L ha U r x hx i j W b c _).symm.trans
    (congrArg (latticeCoverEmbedding a L U r x j W c)
      (gluedLatticeModule_overlap a L ha U r x hx i j W b c m))

noncomputable def gluedLatticeEmbedding (hr : r ∈ (Scheme.ProEt.topology X) U) :
    gluedLatticeModule a L ha U r x hx ⟶ N :=
  (exists_gluedLatticeEmbedding a L U ha r x hx hr).choose

theorem gluedLatticeEmbedding_spec (hr : r ∈ (Scheme.ProEt.topology X) U)
    (i : latticeCoverIndex U r) (W : Over U) (b : W ⟶ latticeCoverObject U r i)
    (m : (gluedLatticeModule a L ha U r x hx).val.obj (op W)) :
    (gluedLatticeEmbedding a L U ha r x hx hr).val.app (op W) m =
      latticeCoverEmbedding a L U r x i W b
        ((gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app
          (op (Over.mk b)) m) :=
  (exists_gluedLatticeEmbedding a L U ha r x hx hr).choose_spec i W b m

noncomputable def gluedLatticeRationalization
    (hr : r ∈ (Scheme.ProEt.topology X) U) :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U)
      (gluedLatticeModule a L ha U r x hx) ⟶ L.over U :=
  rationalizeEmbedding a L U _ (gluedLatticeEmbedding a L U ha r x hx hr)

end AlgebraicGeometry.ProEtale
