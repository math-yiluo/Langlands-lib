/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite

public import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Local invertibility of the glued rationalization

Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices
(blueprint: lem-weil-pbc-lattice-glued-rationalization-isIso).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective

attribute [local instance] AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOver
  AlgebraicGeometry.ProEtale.restrictionWeakSheafifyOverOver
  AlgebraicGeometry.ProEtale.restrictionWEqualsOverOver
  AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOverOver

universe u c v w

open CategoryTheory Opposite

namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
private noncomputable def undoSliceIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C) (f : Over U)
    (M : SheafOfModules.{w} (R.over U))
    (P : SheafOfModules.{w} (R.over f.left))
    (e : M.over f ≅ (pushforward (F := f.iteratedSliceForward) (𝟙 _)).obj P) :
    (overMap R f.hom).obj M ≅ P :=
  (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun T ↦
      (evaluation _ (op (f.iteratedSliceBackward.obj T.unop))).mapIso e) (by
      intro T T' g
      exact e.hom.val.naturality (f.iteratedSliceBackward.op.map g)))

private theorem isIso_of_overMap_cover
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C)
    {M N : SheafOfModules.{w} (R.over U)} (φ : M ⟶ N)
    {I : Type*} (W : I → Over U) (hW : (J.over U).CoversTop W)
    (hφ : ∀ i, IsIso ((overMap R (W i).hom).map φ)) : IsIso φ := by
  suffices h : IsIso ((toSheaf _).map φ) by
    let _ := h
    exact isIso_of_reflects_iso φ (toSheaf _)
  apply Sheaf.isIso_of_coversTop hW
  intro i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro T
  let Z := T.unop.left
  let b : Z ⟶ W i := T.unop.hom
  have hz : (Over.map (W i).hom).obj (Over.mk b.left) = Z := by
    change Over.mk (b.left ≫ (W i).hom) = Z
    rw [Over.w b]
    have hZ : ∀ Z : Over U, Over.mk Z.hom = Z := by
      intro Z
      obtain ⟨V, f, rfl⟩ := Z.mk_surjective
      rfl
    exact hZ Z
  let _ := hφ i
  have h : IsIso (((overMap R (W i).hom).map φ).val.app (op (Over.mk b.left))) :=
    Functor.map_isIso (evaluation (R.over (W i).left) (op (Over.mk b.left)))
      ((overMap R (W i).hom).map φ)
  change IsIso (φ.val.app (op ((Over.map (W i).hom).obj (Over.mk b.left)))) at h
  rw [hz] at h
  let _ := h
  exact Functor.map_isIso (forget₂ (ModuleCat ((R.over U).obj.obj (op Z)))
    AddCommGrpCat) (φ.val.app (op Z))

end SheafOfModules

namespace AlgebraicGeometry.ProEtale
set_option backward.isDefEq.respectTransparency false
open scoped ChangeOfRings
private noncomputable def latticeExtendIso
    {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEt)
    {M N : SheafOfModules.{u + 1}
      (((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)}
    (e : M ≅ N) :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) N :=
  (PresheafOfModules.sheafification (𝟙
    (((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).over U).obj)).mapIso
      (PresheafOfModules.isoMk (fun T ↦
        (ModuleCat.extendScalars ((latticeScalarMap a U).hom.app T).hom).mapIso
          ((SheafOfModules.evaluation _ T).mapIso e))
        (by
          intro T T' f
          exact SheafOfModules.changeOfRingsHom_naturality
            (latticeScalarMap a U) M e.hom f))

private noncomputable def localIntegralIso
    {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (ha : ∀ (U : X.ProEt) T,
      Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (U : X.ProEt) (r : Sieve U)
    (x : Presieve.FamilyOfElements (latticeClassPresheaf a L) r.arrows)
    (hx : x.Compatible) (i : latticeCoverIndex U r) :
    (SheafOfModules.overMap
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) i.2.val).obj
        (gluedLatticeModule a L ha U r x hx) ≅ (latticeCoverPair a L U r x i).module :=
  SheafOfModules.undoSliceIso _ U (latticeCoverObject U r i)
    (gluedLatticeModule a L ha U r x hx) (latticeCoverPair a L U r x i).module
    (gluedLatticeModuleLocalIso a L ha U r x hx i)

private theorem rationalizeEmbedding_restrict_eq
    {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    {U V : X.ProEt} (f : V ⟶ U)
    (M : SheafOfModules.{u + 1}
      (((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))
    (e : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U))
    (P : IntegralLatticePair a L V)
    (α : (SheafOfModules.overMap
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) f).obj M ≅
        P.module)
    (h : ∀ T m, e.val.app ((Over.map f).op.obj T) m =
      (pairEmbedding a L V P).val.app T (α.hom.val.app T m)) :
    restrictedTensorComparison a f M ≫
      (SheafOfModules.overMap
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) f).map
        (rationalizeEmbedding a L U M e) ≫
      ((SheafOfModules.overFunctorMap
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) f).app L).hom =
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
        (latticeScalarMap a V) _ α.hom ≫ P.rationalization.hom := by
  let A := (SheafOfModules.overMap
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) f).obj M
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).over V).obj)).injective
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (rationalizeEmbedding a L U M e).val.app ((Over.map f).op.obj T)
      ((restrictedTensorComparison a f M).val.app T
        ((latticeTensorUnit a V A).app T
          ((1 : (S.over V).obj.obj T) ⊗ₜ[(R.over V).obj.obj T,
            ((latticeScalarMap a V).hom.app T).hom] m))) =
    P.rationalization.hom.val.app T
      ((SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
        (latticeScalarMap a V) A α.hom).val.app T
        ((latticeTensorUnit a V A).app T
          ((1 : (S.over V).obj.obj T) ⊗ₜ[(R.over V).obj.obj T,
            ((latticeScalarMap a V).hom.app T).hom] m)))
  have hc := restrictedTensorComparison_app_unit a f M T
    ((1 : (S.over V).obj.obj T) ⊗ₜ[(R.over V).obj.obj T,
      ((latticeScalarMap a V).hom.app T).hom] m)
  have he := latticeExtension_unit a V A P.module α.hom T m
  exact (congrArg ((rationalizeEmbedding a L U M e).val.app
    ((Over.map f).op.obj T)) hc).trans
    ((rationalizeEmbedding_unit a L U M e ((Over.map f).op.obj T) m).trans
      ((h T m).trans (congrArg (P.rationalization.hom.val.app T) he.symm)))

/-- The scalar extension of the explicitly constructed glued embedding is invertible.
Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60, descent of lattices.
(blueprint: lem-weil-pbc-lattice-glued-rationalization-isIso).
Proof: over the covering object indexed by f : V → U, use the compatible-tuple
projection to identify the glued integral module with its chosen local lattice.
The slice tensor comparison is invertible. On tensors 1 ⊗ m, the restriction of
the glued rationalization equals the given local rationalization: the formula for
the sheafification unit reduces this to the proved formula for the glued embedding.
The adjunction for scalar extension and the sheafification universal property
then give equality on all sections. Thus each restriction of this morphism is an
isomorphism. Apply the local criterion for isomorphisms of sheaves to the covering
family on the slice, and reflect the resulting isomorphism to module sheaves.
This also applies to empty covers, zero modules, and varying finite local rank. -/
theorem gluedLatticeRationalization_isIso
    {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (ha : ∀ (U : X.ProEt) T,
      Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (U : X.ProEt) (r : Sieve U) (hr : r ∈ (Scheme.ProEt.topology X) U)
    (x : Presieve.FamilyOfElements (latticeClassPresheaf a L) r.arrows)
    (hx : x.Compatible) :
    IsIso (gluedLatticeRationalization a L U ha r x hx hr) := by
  let M := gluedLatticeModule a L ha U r x hx
  let e := gluedLatticeRationalization a L U ha r x hx hr
  apply SheafOfModules.isIso_of_overMap_cover
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    U e (latticeCoverObject U r) (latticeCover_coversTop U r hr)
  intro i
  let f := i.2.val
  let P := latticeCoverPair a L U r x i
  let α := localIntegralIso a L ha U r x hx i
  have hc := rationalizeEmbedding_restrict_eq a L f M
    (gluedLatticeEmbedding a L U ha r x hx hr) P α
    (fun T m ↦ gluedLatticeEmbedding_spec a L U ha r x hx hr i
      ((Over.map f).obj T.unop) (Over.homMk T.unop.hom rfl) m)
  have he : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a i.1) _ α.hom = (latticeExtendIso a i.1 α).hom := rfl
  have hi : IsIso (restrictedTensorComparison a f M ≫
      (SheafOfModules.overMap
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) f).map e ≫
      ((SheafOfModules.overFunctorMap
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) f).app L).hom) := by
    exact (congrArg IsIso
      (hc.trans (congrArg (fun q ↦ q ≫ P.rationalization.hom) he))).mpr inferInstance
  let _ : IsIso (restrictedTensorComparison a f M) :=
    restrictedTensorComparison_isIso a f M
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)

end AlgebraicGeometry.ProEtale
