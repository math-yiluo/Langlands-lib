/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Canonical tensor pullback with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

This is the general canonical representative interface, with a site-object universe s and an
independent site-morphism universe h. Rings and modules live in max s h, as in the
published K-flat interface. Both sites retain their actual Hom universe. The ring map is arbitrary,
  including coefficient quotients, and
the geometric morphism can be the etale-to-pro-etale comparison. The pure-tensor,
unit and signed total-complex normalizations are retained verbatim. Public imports
retain both earlier interfaces for existing callers.
-/

@[expose] public section

set_option Elab.async false

set_option autoImplicit false

universe s h w u uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.CanonicalTensorPullbackOfUniverses

-- Both site sizes fit the coefficient universe.
attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

set_option backward.isDefEq.respectTransparency true

variable {C D : Type s} [Category.{h} C] [Category.{h} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{max s h}) (S RI : Sheaf JD CommRingCat.{max s h})
  (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj S))
  (hobj : ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
theorem ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) _ _ (monoidalCategory R) :=
  cochainModulesPreadditive R

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
abbrev CanonicalRingedTensorComparison :=
  CanonicalRingedTensorComparisonOnSmallSites.{max s h, s, h, s, h}
    R S RI uInv I c L hobj

attribute [local irreducible] monoidalCategory
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] PresheafOfModules.sheafification

private theorem weakSheafification {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    HasWeakSheafify J AddCommGrpCat.{u} := inferInstance

private theorem additiveCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) := inferInstance

private theorem ringCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u}) := inferInstance

section TensorSections

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

attribute [local irreducible] CochainTensorComparison.scalarInsertion

open scoped ChangeOfRings TensorProduct
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private theorem pure_eq (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (𝓡 R)) (W : Dᵒᵖ)
    (m : M.val.obj W) (n : N.val.obj W) :
    CochainScalarConstruction.pure R M N W m n = ringedComparisonPure R M N W m n := by
  rfl

@[no_expose] private noncomputable def ts (M N : SheafOfModules.{u} (𝓡 B))
    (W : Dᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.obj W :=
  ringedComparisonPure B M N W m n
private theorem ts_naturality (M N : SheafOfModules.{u} (𝓡 B))
    {W V : Dᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.map i (ts B M N W m n) =
      ts B M N V (M.val.map i m) (N.val.map i n) := by
  exact (congrArg (((monoidalCategory B).tensorObj M N).val.map i)
    (pure_eq B M N W m n).symm).trans
      ((CochainScalarConstruction.pure_restrict B M N i m n).trans
        (pure_eq B M N V (M.val.map i m) (N.val.map i n)))
@[no_expose] private noncomputable def tensorPair (M N : SheafOfModules.{u} (𝓡 B))
    (Z : Sheaf J (Type u))
    (x : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj N)) :
    Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((monoidalCategory B).tensorObj M N)) :=
  ⟨{ app := fun W ↦ ↾fun t ↦ ts B M N W (x.hom.app W t) (y.hom.app W t)
     naturality := by
       intro W V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change ts B M N V (x.hom.app V (Z.obj.map i t))
           (y.hom.app V (Z.obj.map i t)) =
         ((monoidalCategory B).tensorObj M N).val.map i
           (ts B M N W (x.hom.app W t) (y.hom.app W t))
       rw [hx, hy]
       exact (ts_naturality B M N i _ _).symm }⟩

private theorem productElements {E : Type*} [Category* E] [HasBinaryProducts E]
    (F : E ⥤ Type u) (X Y : E) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

variable (c : A ⟶ B)

@[no_expose] private noncomputable def ins (M : SheafOfModules.{u} (𝓡 A))
    (W : Dᵒᵖ) (m : M.val.obj W) : (changeOfRings.{vD, uD, u} c M).val.obj W :=
  CochainScalarConstruction.ins c M W m
-- Expand the two scalar extensions through the sheafification adjunction.
private theorem scalar_tensor_ext
    (M N : SheafOfModules.{u} (𝓡 A)) (H : SheafOfModules.{u} (𝓡 B))
    {f g : (monoidalCategory B).tensorObj (changeOfRings.{vD, uD, u} c M)
      (changeOfRings.{vD, uD, u} c N) ⟶ H}
    (h : ∀ W m n, f.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n)) =
      g.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n))) : f = g := by
  apply CochainScalarConstruction.scalar_tensor_ext c M N H
  intro W m n
  exact h W m n

private theorem ts_cast
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{vD, uD, u} c M)
    (hy : Y = changeOfRings.{vD, uD, u} c N)
    (W : Dᵒᵖ) (m : (changeOfRings.{vD, uD, u} c M).val.obj W)
    (n : (changeOfRings.{vD, uD, u} c N).val.obj W) :
    (eqToHom (congrArg₂ (monoidalCategory B).tensorObj hx.symm hy.symm)).val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W m n) =
    ts B X Y W ((eqToHom hx.symm).val.app W m)
      ((eqToHom hy.symm).val.app W n) := by
  subst X
  subst Y
  rfl

private theorem scalarTensorSections_hom_ext
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y H : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{vD, uD, u} c M)
    (hy : Y = changeOfRings.{vD, uD, u} c N)
    {f g : (monoidalCategory B).tensorObj X Y ⟶ H}
    (h : ∀ W m n, f.val.app W (ts B X Y W
      ((eqToHom hx.symm).val.app W (ins A B c M W m))
      ((eqToHom hy.symm).val.app W (ins A B c N W n))) =
      g.val.app W (ts B X Y W
        ((eqToHom hx.symm).val.app W (ins A B c M W m))
        ((eqToHom hy.symm).val.app W (ins A B c N W n)))) : f = g := by
  let e := eqToHom (congrArg₂ (monoidalCategory B).tensorObj hx.symm hy.symm)
  apply (cancel_epi e).mp
  apply scalar_tensor_ext A B c M N H
  intro W m n
  change f.val.app W (e.val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W
        (ins A B c M W m) (ins A B c N W n))) =
    g.val.app W (e.val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W
        (ins A B c M W m) (ins A B c N W n)))
  dsimp only [e]
  rw [ts_cast A B c M N X Y hx hy]
  exact h W m n

end TensorSections

section TensorUniqueness

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

set_option backward.isDefEq.respectTransparency true

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

set_option backward.isDefEq.respectTransparency.types true

private theorem comparison_q_apply
    (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj)
    (M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W) :
    (k.q M).hom.app W m =
      (eqToHom (hobj M).symm).val.app W (ins RI S c (I.modules.obj M) W m) := by
  exact k.q_one M W m

-- Normalize the record projection while its generalized elements are abstract.
private theorem comparison_pure_apply
    (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj)
    (M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (Z : Sheaf JC (Type u))
    (x : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
    (y : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
    (z : Z ⟶ (CochainScalarConstruction.underlying R).obj
      ((monoidalCategory R).tensorObj M N))
    (hz : ∀ V t, z.hom.app V t = ts R M N V (x.hom.app V t) (y.hom.app V t))
    (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W) :
    (k.mu M N).hom.val.app W
      ((uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        k.q ((monoidalCategory R).tensorObj M N)).hom.app W t) =
      ts S (L.obj M) (L.obj N) W
        ((k.q M).hom.app W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t))
        ((k.q N).hom.app W ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) := by
  exact k.pure M N Z x y z hz W t

-- The two data fields determine the record; its remaining fields are propositions.
private theorem comparison_ext
    (a b : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj)
    (hq : a.q = b.q) (hmu : a.mu = b.mu) : a = b := by
  cases a
  cases b
  cases hq
  cases hmu
  rfl

-- Detect inverse tensorators on scalar-extension generators and universal products.
private theorem comparison_subsingleton [PreservesFiniteLimits uInv]
    [HasBinaryProducts (Sheaf JC (Type u))] :
    Subsingleton (CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj) := by
  refine ⟨fun a b ↦ ?_⟩
  have hqq : a.q = b.q := by
    funext M
    ext W m
    exact (comparison_q_apply R S RI uInv I c L hobj a M W m).trans
      (comparison_q_apply R S RI uInv I c L hobj b M W m).symm
  have hmm : a.mu = b.mu := by
    funext M N
    apply Iso.ext_inv
    apply scalarTensorSections_hom_ext RI S c (I.modules.obj M) (I.modules.obj N)
      (L.obj M) (L.obj N) _ (hobj M) (hobj N)
    intro W m n
    let UR := toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})
    let Z := UR.obj M ⨯ UR.obj N
    let x : Z ⟶ UR.obj M := prod.fst
    let y : Z ⟶ UR.obj N := prod.snd
    let z := tensorPair R M N Z x y
    let ev := sheafToPresheaf JD (Type u) ⋙ (CategoryTheory.evaluation Dᵒᵖ (Type u)).obj W
    obtain ⟨t, htx, hty⟩ := productElements (uInv ⋙ ev) (UR.obj M) (UR.obj N)
      ((I.moduleUnderlying.hom.app M).hom.app W m)
      ((I.moduleUnderlying.hom.app N).hom.app W n)
    have hm : (uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t = m := by
      change (I.moduleUnderlying.inv.app M).hom.app W ((uInv.map x).hom.app W t) = m
      change (uInv.map x).hom.app W t = _ at htx
      rw [htx]
      exact congrArg (fun f ↦ f.hom.app W m) (I.moduleUnderlying.app M).hom_inv_id
    have hn : (uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = n := by
      change (I.moduleUnderlying.inv.app N).hom.app W ((uInv.map y).hom.app W t) = n
      change (uInv.map y).hom.app W t = _ at hty
      rw [hty]
      exact congrArg (fun f ↦ f.hom.app W n) (I.moduleUnderlying.app N).hom_inv_id
    have hz : ∀ V s, z.hom.app V s = ts R M N V (x.hom.app V s) (y.hom.app V s) := by
      intros
      rfl
    have ha := comparison_pure_apply R S RI uInv I c L hobj a M N Z x y z hz W t
    have hb := comparison_pure_apply R S RI uInv I c L hobj b M N Z x y z hz W t
    let i := (uInv.map z ≫ I.moduleUnderlying.inv.app
      ((monoidalCategory R).tensorObj M N)).hom.app W t
    let v := (a.q ((monoidalCategory R).tensorObj M N)).hom.app W i
    let p := ts S (L.obj M) (L.obj N) W
    have hv : (b.q ((monoidalCategory R).tensorObj M N)).hom.app W i = v :=
      (congrArg (fun q ↦ (q ((monoidalCategory R).tensorObj M N)).hom.app W i) hqq).symm
    have hm' : (b.q M).hom.app W m = (a.q M).hom.app W m :=
      (congrArg (fun q ↦ (q M).hom.app W m) hqq).symm
    have hn' : (b.q N).hom.app W n = (a.q N).hom.app W n :=
      (congrArg (fun q ↦ (q N).hom.app W n) hqq).symm
    have ha' : (a.mu M N).hom.val.app W v =
        p ((a.q M).hom.app W m) ((a.q N).hom.app W n) :=
      ha.trans (congrArg₂ p (congrArg ((a.q M).hom.app W) hm)
        (congrArg ((a.q N).hom.app W) hn))
    have hb' : (b.mu M N).hom.val.app W v =
        p ((a.q M).hom.app W m) ((a.q N).hom.app W n) :=
      (congrArg ((b.mu M N).hom.val.app W) hv).symm.trans
        (hb.trans (congrArg₂ p ((congrArg ((b.q M).hom.app W) hm).trans hm')
          ((congrArg ((b.q N).hom.app W) hn).trans hn')))
    have haInv := congrArg ((a.mu M N).inv.val.app W) ha'
    have hbInv := congrArg ((b.mu M N).inv.val.app W) hb'
    have haCancel := congrArg (fun f ↦ f.val.app W v) (a.mu M N).hom_inv_id
    have hbCancel := congrArg (fun f ↦ f.val.app W v) (b.mu M N).hom_inv_id
    have hi := (haCancel.symm.trans haInv).symm.trans (hbCancel.symm.trans hbInv)
    have hp := congrArg₂ p
      (comparison_q_apply R S RI uInv I c L hobj a M W m)
      (comparison_q_apply R S RI uInv I c L hobj a N W n)
    exact (congrArg ((a.mu M N).inv.val.app W) hp).symm.trans
      (hi.trans (congrArg ((b.mu M N).inv.val.app W) hp))
  exact comparison_ext R S RI uInv I c L hobj a b hqq hmm

/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data).
Proof: apply the ordinary comparison theorem to the given inverse-image lift.
Its generalized-element normalization gives q and mu. Scalar-extension pure tensors
generate after sheafification, giving uniqueness of q. Bilinear generalized pure tensors
generate the sheaf tensor, giving uniqueness of mu; proof irrelevance handles the laws.
Unlike SheafOfModules.canonicalRingedTensorComparison_existsUnique, the explicit
binders below allow five independent universes uC, vC, uD, vD and u. The published
statement requires C,D : Type u with Category.{u} on both sites. -/
private theorem normalizedComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    [HasBinaryProducts (Sheaf JC (Type u))]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨mu, hn, hp⟩ := CochainTensorComparison.normalizedTensorator_exists
      R S RI uInv I c L hobj
      uPush adj hmap
    exact ⟨{ q := CochainTensorComparison.scalarInsertion R S RI uInv I c L hobj
             q_one := by intro M W m; rfl
             mu := mu
             naturality := hn
             pure := by
               simp only [ringedComparisonPureCondition]
               exact hp }⟩
  · exact comparison_subsingleton R S RI uInv I c L hobj

end TensorUniqueness

/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: apply the ordinary comparison theorem to the given inverse-image lift.
Its generalized-element normalization gives q and mu. Scalar-extension pure tensors
generate after sheafification, giving uniqueness of q. Bilinear generalized pure tensors
generate the sheaf tensor, giving uniqueness of mu; proof irrelevance handles the laws. -/
theorem canonicalRingedTensorComparison_existsUnique
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by
  exact normalizedComparison R S RI uInv I c L hobj uPush adj hmap

namespace UnitConstruction

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (I : AlgebraicInverseImage F R A)
@[no_expose]
private noncomputable abbrev base (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
@[no_expose]
private noncomputable abbrev rset (R : Sheaf J CommRingCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
@[no_expose]
private noncomputable abbrev mset (R : Sheaf J CommRingCat.{u}) :
    SheafOfModules.{u} (base R) ⥤ Sheaf J (Type u) :=
  toSheaf (base R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
@[no_expose]
private noncomputable def oneMap : rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
     naturality := by intro X Y f; ext; exact (map_one (R.obj.map f).hom).symm }⟩
@[no_expose]
private noncomputable def unitSetIso :
    (mset A).obj (I.modules.obj (unit (base R))) ≅ rset A :=
  I.moduleUnderlying.app (unit (base R)) ≪≫ I.ringUnderlying
private theorem basis (W : Dᵒᵖ) (a : A.obj.obj W) :
    (show (I.modules.obj (unit (base R))).val.obj W from
      (unitSetIso R A F I).inv.hom.app W a) = a •
        (show (I.modules.obj (unit (base R))).val.obj W from
          (unitSetIso R A F I).inv.hom.app W (1 : A.obj.obj W)) := by
  change (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W a)) = a •
    (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W)))
  let T := rset R
  let t := I.ringUnderlying.inv.hom.app W a
  have ho := I.ringOne T (oneMap R) (fun _ _ ↦ rfl) W t
  have he : (F.map (oneMap R)).hom.app W t =
      I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W) := by
    have hh := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc := congrArg (fun k ↦ k.hom.app W ((F.map (oneMap R)).hom.app W t))
      I.ringUnderlying.hom_inv_id
    exact hc.symm.trans hh
  have hs := I.moduleSMul (unit (base R)) T (𝟙 T) (oneMap R) (𝟙 T)
    (fun U x ↦ (mul_one (show R.obj.obj U from x)).symm) W t
  have hid : (F.map (𝟙 T)).hom.app W t = t :=
    congrArg (fun f ↦ f.hom.app W t) (F.map_id T)
  have ht := congrArg ((I.moduleUnderlying.inv.app (unit (base R))).hom.app W) hid
  have hr := congrArg (fun v : (F.obj T).obj.obj W ↦
    (show A.obj.obj W from I.ringUnderlying.hom.hom.app W v) •
      (show (I.modules.obj (unit (base R))).val.obj W from
        (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
          ((F.map (oneMap R)).hom.app W t))) hid
  have hs' := ht.symm.trans (hs.trans hr)
  have he' := congrArg ((I.moduleUnderlying.inv.app (unit (base R))).hom.app W) he
  have hs'' := hs'.trans (congrArg (fun v : (I.modules.obj (unit (base R))).val.obj W ↦
    (show A.obj.obj W from I.ringUnderlying.hom.hom.app W t) • v) he')
  have hc := congrArg (fun k ↦ k.hom.app W a) I.ringUnderlying.inv_hom_id
  change I.ringUnderlying.hom.hom.app W t = a at hc
  exact hs''.trans (congrArg (fun r : A.obj.obj W ↦
    r • (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W)))) hc)
@[no_expose]
private def rankOneLinearEquiv {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (e : K ≃ V) (he : ∀ a, e a = a • e 1) : K ≃ₗ[K] V where
  toEquiv := e
  map_add' a b := (he (a + b)).trans ((add_smul a b (e 1)).trans
    (congrArg₂ (fun x y : V ↦ x + y) (he a).symm (he b).symm))
  map_smul' a b := (he (a * b)).trans ((mul_smul a b (e 1)).trans
    (congrArg (fun x : V ↦ a • x) (he b).symm))

@[no_expose]
private noncomputable def unitIso : I.modules.obj (unit (base R)) ≅ unit (base A) := by
  let eW (W : Dᵒᵖ) : A.obj.obj W ≃ₗ[A.obj.obj W]
      (I.modules.obj (unit (base R))).val.obj W :=
    rankOneLinearEquiv
      ((((sheafToPresheaf K (Type u)).mapIso (unitSetIso R A F I)).app W).toEquiv.symm)
      (basis R A F I W)
  let ep : (unit (base A)).val ≅ (I.modules.obj (unit (base R))).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun k ↦ k a) ((unitSetIso R A F I).inv.hom.naturality f))
  exact ((fullyFaithfulForget (base A)).preimageIso (X := unit (base A))
    (Y := I.modules.obj (unit (base R))) ep).symm
@[no_expose]
private noncomputable def scalarUnitRawIso
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) :
    changeOfRingsPresheaf c (unit (base A)) ≅ (unit (base S)).val :=
  PresheafOfModules.isoMk (fun W ↦ by
    let := (c.hom.app W).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      (A.obj.obj W) (S.obj.obj W) (S.obj.obj W)).toModuleIso) (by
    intro W V i
    let := (c.hom.app W).hom.toAlgebra
    let := (c.hom.app V).hom.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro a
    change (TensorProduct.AlgebraTensorModule.rid
        (A.obj.obj V) (S.obj.obj V) (S.obj.obj V))
        (changeOfRingsMap c (unit (base A)) i
          ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] a)) = _
    have ht := CochainScalarConstruction.tensorRestriction_tmul c (unit (base A)) i 1 a
    change changeOfRingsMap c (unit (base A)) i
      ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] a) = _ at ht
    rw [ht]
    change (c.hom.app V (A.obj.map i a)) * S.obj.map i 1 =
      S.obj.map i ((c.hom.app W a) * 1)
    simp only [map_one, mul_one]
    exact ConcreteCategory.congr_hom (c.hom.naturality i) a)

@[no_expose]
private noncomputable def scalarUnitIso
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) :
    (CochainScalarConstruction.tensorFunctor c).obj (unit (base A)) ≅ unit (base S) :=
  (PresheafOfModules.sheafification (𝟙 (base S).obj)).mapIso (scalarUnitRawIso A S c) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (base S).obj)).counit).app
      (unit (base S))

private theorem scalarUnitIso_insertion
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) (W : Dᵒᵖ) (a : A.obj.obj W) :
    (scalarUnitIso A S c).hom.val.app W
      ((CochainScalarConstruction.tensorUnit c (unit (base A))).hom.app W a) =
        (c.hom.app W).hom a := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (base S).obj)
  have h : adj.homEquiv _ _ (scalarUnitIso A S c).hom = (scalarUnitRawIso A S c).hom := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app (unit (base S))) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  rw [CochainScalarConstruction.tensorUnit_apply]
  have he := congrArg
    (fun f ↦ f.app W ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] a)) h
  exact he.trans (by
    change (c.hom.app W).hom a * 1 = _
    exact mul_one _)

open MonoidalCategory
set_option maxHeartbeats 30000 in
-- Use the abstract unitor coherence before specializing sheafification.
private theorem unitor_transport
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (L : A ⥤ B) [L.Monoidal] (X : A) (Y : B) (e : L.obj X ≅ Y)
    (eU : L.obj (𝟙_ A) ≅ 𝟙_ B) (hu : eU.inv = Functor.LaxMonoidal.ε L) :
    (e.inv ⊗ₘ eU.inv) ≫ Functor.LaxMonoidal.μ L X (𝟙_ A) ≫
      L.map (ρ_ X).hom ≫ e.hom = (ρ_ Y).hom := by
  rw [tensorHom_def, Category.assoc, hu,
    ← Functor.LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

attribute [local semireducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option maxHeartbeats 180000 in
-- Specialize the abstract formula using the explicit counit components.
private theorem unitor_formula
    (M : SheafOfModules.{u} (base R)) :
    (tensorObjIsoSheafification M (unit (base R))).hom ≫
      (PresheafOfModules.sheafification (𝟙 (base R).obj)).map
        ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).counit.app M =
      ((monoidalCategory R).rightUnitor M).hom := by
  let L := PresheafOfModules.sheafification (𝟙 (base R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)
  exact unitor_transport L M.val M ((asIso adj.counit).app M)
    ((asIso adj.counit).app (unit (base R))) rfl

set_option maxHeartbeats 80000 in
-- Use the sheafification API without unfolding its monoidal structure.
private theorem unitor_pure
    (M : SheafOfModules.{u} (base R)) (W : Cᵒᵖ)
    (m : M.val.obj W) (r : R.obj.obj W) :
    ((monoidalCategory R).rightUnitor M).hom.val.app W
      (ringedComparisonPure R M (unit (base R)) W m r) = r • m := by
  have hf := congrArg (fun f ↦ (tensorObjIsoSheafification M (unit (base R))).inv ≫ f)
    (unitor_formula R M)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hf
  have h := hf.symm
  have he := congrArg (fun f ↦ f.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
      (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r))) h
  change ((monoidalCategory R).rightUnitor M).hom.val.app W
    (ringedComparisonPure R M (unit (base R)) W m r) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).counit.app M).val.app W
      (((PresheafOfModules.sheafification (𝟙 (base R).obj)).map
        ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom).val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
            (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r))) at he
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.naturality
    ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom
  have hn' := congrArg (fun f ↦ f.app W (m ⊗ₜ[R.obj.obj W] r)) hn
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
      M.val).app W (r • m) =
    ((PresheafOfModules.sheafification (𝟙 (base R).obj)).map
      ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
          (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r)) at hn'
  rw [← hn'] at he
  have hc := (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).right_triangle_components
    M
  have hh := congrArg (fun f ↦ f.app W (r • m)) hc
  exact he.trans hh
-- Keep the concrete coefficient unit in the API without expanding the localization.
@[no_expose, irreducible]
private noncomputable def explicitRightUnitor
    (M : SheafOfModules.{u} (base R)) :
    (monoidalCategory R).tensorObj M (unit (base R)) ≅ M :=
  (monoidalCategory R).rightUnitor M

private theorem explicitRightUnitor_pure
    (M : SheafOfModules.{u} (base R)) (W : Cᵒᵖ)
    (m : M.val.obj W) (r : R.obj.obj W) :
    (explicitRightUnitor R M).hom.val.app W
      (ringedComparisonPure R M (unit (base R)) W m r) = r • m := by
  unfold explicitRightUnitor
  exact unitor_pure R M W m r

private theorem unitor_map_pure
    (M N : SheafOfModules.{u} (base R)) (f : N ⟶ unit (base R)) (W : Cᵒᵖ)
    (m : M.val.obj W) (n : N.val.obj W)
    (hf : f.val.app W n = (1 : R.obj.obj W)) :
    (explicitRightUnitor R M).hom.val.app W
      (((monoidalCategory R).tensorHom (𝟙 M) f).val.app W
        (ringedComparisonPure R M N W m n)) = m := by
  have ht := CochainScalarConstruction.pure_map R (𝟙 M) f W m n
  simp only [pure_eq] at ht
  change ((monoidalCategory R).tensorHom (𝟙 M) f).val.app W
      (ringedComparisonPure R M N W m n) =
    ringedComparisonPure R M (unit (base R)) W m (f.val.app W n) at ht
  have he := congrArg ((explicitRightUnitor R M).hom.val.app W) ht
  rw [hf] at he
  exact he.trans ((explicitRightUnitor_pure R M W m 1).trans
    (@MulAction.one_smul _ _ _
      (ModuleCat.isModule (M.val.obj W)).toDistribMulAction.toMulAction m))

private theorem unitIso_hom_apply (W : Dᵒᵖ)
    (m : (I.modules.obj (unit (base R))).val.obj W) :
    (unitIso R A F I).hom.val.app W m = (unitSetIso R A F I).hom.hom.app W m := by
  rfl

@[no_expose]
private noncomputable def pullbackUnitIso
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) :
    (CochainScalarConstruction.tensorFunctor c).obj (I.modules.obj (unit (base R))) ≅
      unit (base S) :=
  (CochainScalarConstruction.tensorFunctor c).mapIso (unitIso R A F I) ≪≫
    scalarUnitIso A S c

private theorem pullbackUnitIso_insertion
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) (W : Dᵒᵖ)
    (m : (I.modules.obj (unit (base R))).val.obj W) :
    (pullbackUnitIso R A F I S c).hom.val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m) =
        (c.hom.app W).hom ((unitSetIso R A F I).hom.hom.app W m) := by
  have hu := congrArg (fun k ↦ k.val.app W m)
    ((CochainScalarConstruction.tensorAdjunction c).unit.naturality (unitIso R A F I).hom)
  change (CochainScalarConstruction.tensorUnit c (unit (base A))).hom.app W
      ((unitIso R A F I).hom.val.app W m) =
    ((CochainScalarConstruction.tensorFunctor c).map (unitIso R A F I).hom).val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m)
    at hu
  change (scalarUnitIso A S c).hom.val.app W
    (((CochainScalarConstruction.tensorFunctor c).map (unitIso R A F I).hom).val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m)) = _
  rw [← hu, scalarUnitIso_insertion, unitIso_hom_apply]

set_option maxHeartbeats 60000 in
-- Bound the Hom-equivalence computation by its explicit underlying formula.
private theorem scalarHom_ext
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S)
    (M : SheafOfModules.{u} (base A)) (H : SheafOfModules.{u} (base S))
    {f g : (CochainScalarConstruction.tensorFunctor c).obj M ⟶ H}
    (h : ∀ W m, f.val.app W
      ((CochainScalarConstruction.tensorUnit c M).hom.app W m) =
      g.val.app W ((CochainScalarConstruction.tensorUnit c M).hom.app W m)) : f = g := by
  apply (CochainScalarConstruction.tensorHomEquiv c M H).injective
  apply (CochainScalarConstruction.underlying A).map_injective
  have hf := CochainScalarConstruction.tensorAdjunction_underlying c M H f
  have hg := CochainScalarConstruction.tensorAdjunction_underlying c M H g
  change (CochainScalarConstruction.underlying A).map
    (CochainScalarConstruction.tensorHomEquiv c M H f) = _ at hf
  change (CochainScalarConstruction.underlying A).map
    (CochainScalarConstruction.tensorHomEquiv c M H g) = _ at hg
  rw [hf, hg]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro m
  exact h W m

private theorem unitMap_unique
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (mu : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (j j' : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X, (mu X (𝟙_ A)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hj' : ∀ X, (mu X (𝟙_ A)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j'.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom) : j = j' := by
  have h := (hj (𝟙_ A)).trans (hj' (𝟙_ A)).symm
  have ht : (𝟙 (F.obj (𝟙_ A)) ⊗ₘ j.hom) =
      (𝟙 (F.obj (𝟙_ A)) ⊗ₘ j'.hom) := by
    apply (cancel_mono (ρ_ (F.obj (𝟙_ A))).hom).mp
    apply (cancel_epi (mu (𝟙_ A) (𝟙_ A)).hom).mp
    simpa only [Category.assoc] using h
  have ht' := congrArg (fun f ↦ (j.inv ⊗ₘ 𝟙 (F.obj (𝟙_ A))) ≫ f ≫
    (j.hom ⊗ₘ 𝟙 (𝟙_ B))) ht
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht'
  have he := congrArg (fun f ↦ f ≫ (λ_ (𝟙_ B)).hom) ht'
  simp only [id_tensorHom, leftUnitor_naturality] at he
  apply Iso.ext
  exact (cancel_epi (λ_ (F.obj (𝟙_ A))).hom).mp he

-- Specialize tensor-unit cancellation once, with concrete units in the signature.
private theorem explicitUnitMap_unique
    (S : Sheaf K CommRingCat.{u})
    (L : SheafOfModules.{u} (base R) ⥤ SheafOfModules.{u} (base S))
    (mu : ∀ M N : SheafOfModules.{u} (base R),
      L.obj ((monoidalCategory R).tensorObj M N) ≅
        (monoidalCategory S).tensorObj (L.obj M) (L.obj N))
    (j j' : L.obj (unit (base R)) ≅ unit (base S))
    (hj : ∀ M, (mu M (unit (base R))).hom ≫
      (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
        (explicitRightUnitor S (L.obj M)).hom = L.map (explicitRightUnitor R M).hom)
    (hj' : ∀ M, (mu M (unit (base R))).hom ≫
      (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j'.hom ≫
        (explicitRightUnitor S (L.obj M)).hom = L.map (explicitRightUnitor R M).hom) :
    j = j' := by
  let := monoidalCategory R
  let := monoidalCategory S
  unfold explicitRightUnitor at hj hj'
  exact unitMap_unique L mu j j' hj hj'

end UnitConstruction

attribute [local irreducible] ringedComparisonPure tensorObjIsoSheafification

attribute [local irreducible] UnitConstruction.unitIso UnitConstruction.scalarUnitIso
  UnitConstruction.pullbackUnitIso

section GenericUnit

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

/-- The specified scalar-extension presentation is a natural isomorphism. -/
@[no_expose, irreducible]
private noncomputable def scalarTransport
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm) :
    L ≅ I.modules ⋙ CochainScalarConstruction.tensorFunctor c :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

private theorem scalarTransport_inv_app
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm)
    (M : SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    (scalarTransport R S RI uInv I c L hobj hmap).inv.app M = eqToHom (hobj M).symm := by
  unfold scalarTransport
  rfl

/-- The coefficient-unit comparison with its specified object presentation. -/
@[no_expose, irreducible]
private noncomputable def unitComparisonIso :
    L.obj (unit (UnitConstruction.base R)) ≅ unit (UnitConstruction.base S) :=
  eqToIso (hobj (unit (UnitConstruction.base R))) ≪≫
    UnitConstruction.pullbackUnitIso R RI uInv I S c

set_option backward.isDefEq.respectTransparency true in
private theorem unitComparisonIso_insertion
    (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj)
    (W : Dᵒᵖ) (m : (I.modules.obj (unit (UnitConstruction.base R))).val.obj W) :
    (unitComparisonIso R S RI uInv I c L hobj).hom.val.app W
      ((k.q (unit (UnitConstruction.base R))).hom.app W m) =
      (c.hom.app W).hom ((UnitConstruction.unitSetIso R RI uInv I).hom.hom.app W m) := by
  let U := unit (UnitConstruction.base R)
  let e := eqToIso (hobj U)
  let η := (CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W m
  have hq : (k.q U).hom.app W m = e.inv.val.app W η :=
    (k.q_one U W m).trans
      (congrArg (e.inv.val.app W)
        (CochainScalarConstruction.tensorUnit_apply c (I.modules.obj U) W m).symm)
  have hc : e.hom.val.app W (e.inv.val.app W η) = η :=
    congrArg (fun f ↦ f.val.app W η) e.inv_hom_id
  unfold unitComparisonIso
  change (UnitConstruction.pullbackUnitIso R RI uInv I S c).hom.val.app W
    (e.hom.val.app W ((k.q U).hom.app W m)) = _
  exact (congrArg ((UnitConstruction.pullbackUnitIso R RI uInv I S c).hom.val.app W)
    ((congrArg (e.hom.val.app W) hq).trans hc)).trans
      (UnitConstruction.pullbackUnitIso_insertion R RI uInv I S c W m)

-- The explicit-unit API keeps the localized monoidal structure abstract.

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(blueprint: def-pur-cochain-tensor-coherence-data).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j.
Unlike SheafOfModules.canonicalRingedTensorComparison_unit, the explicit binders
below retain independent uC, vC, uD, vD and coefficient/module universe u. -/
private theorem normalizedUnit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            (UnitConstruction.explicitRightUnitor S (L.obj M)).hom =
          L.map ((UnitConstruction.explicitRightUnitor R M).hom) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let T := CochainScalarConstruction.tensorFunctor c
  let ε : L ≅ I.modules ⋙ T := scalarTransport R S RI uInv I c L hobj hmap
  have hq (M) (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W) :
      (k.q M).hom.app W m = (ε.inv.app M).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m) := by
    rw [show ε.inv.app M = eqToHom (hobj M).symm from
      scalarTransport_inv_app R S RI uInv I c L hobj hmap M]
    exact (k.q_one M W m).trans
      (congrArg ((eqToHom (hobj M).symm).val.app W)
        (CochainScalarConstruction.tensorUnit_apply c (I.modules.obj M) W m).symm)
  have hqmap {M N} (f : M ⟶ N) (W : Dᵒᵖ)
      (m : (I.modules.obj M).val.obj W) :
      (L.map f).val.app W ((k.q M).hom.app W m) =
        (k.q N).hom.app W ((I.modules.map f).val.app W m) := by
    rw [hq, hq]
    have hn := congrArg (fun a ↦ a.val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m))
        (ε.inv.naturality f)
    have hu := congrArg (fun a ↦ a.val.app W m)
      ((CochainScalarConstruction.tensorAdjunction c).unit.naturality (I.modules.map f))
    change (CochainScalarConstruction.tensorUnit c (I.modules.obj N)).hom.app W
        ((I.modules.map f).val.app W m) =
      (T.map (I.modules.map f)).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m) at hu
    exact hn.symm.trans (congrArg ((ε.inv.app N).val.app W) hu.symm)
  let U := unit (UnitConstruction.base R)
  let j : L.obj U ≅ unit (UnitConstruction.base S) :=
    unitComparisonIso R S RI uInv I c L hobj
  have hj : ∀ M, (k.mu M U).hom ≫ (𝟙 (L.obj M) ⊗ₘ j.hom) ≫
      (UnitConstruction.explicitRightUnitor S (L.obj M)).hom =
        L.map (UnitConstruction.explicitRightUnitor R M).hom := by
    intro M
    let P := (monoidalCategory R).tensorObj M U
    let Z := (UnitConstruction.mset R).obj P
    let x : Z ⟶ (UnitConstruction.mset R).obj M :=
      (UnitConstruction.mset R).map (UnitConstruction.explicitRightUnitor R M).hom
    let y : Z ⟶ (UnitConstruction.mset R).obj U :=
      ⟨{ app := fun V ↦ ↾(fun _ ↦ (1 : R.obj.obj V))
         naturality := by
           intro V V' f
           ext z
           exact (map_one (R.obj.map f).hom).symm }⟩
    have hz (V : Cᵒᵖ) (z : Z.obj.obj V) :
        (𝟙 Z : Z ⟶ Z).hom.app V z = ringedComparisonPure R M U V
          (x.hom.app V z) (y.hom.app V z) := by
      have he := UnitConstruction.explicitRightUnitor_pure R M V
        ((UnitConstruction.explicitRightUnitor R M).hom.val.app V z) 1
      rw [one_smul] at he
      have ht := congrArg ((UnitConstruction.explicitRightUnitor R M).inv.val.app V) he
      have hc (v : P.val.obj V) := congrArg (fun f ↦ f.val.app V v)
        (UnitConstruction.explicitRightUnitor R M).hom_inv_id
      exact ((hc _).symm.trans (ht.trans (hc z))).symm
    apply (cancel_epi (ε.inv.app P)).mp
    apply UnitConstruction.scalarHom_ext RI S c (I.modules.obj P) (L.obj M)
    intro W m
    change (UnitConstruction.explicitRightUnitor S (L.obj M)).hom.val.app W
        ((𝟙 (L.obj M) ⊗ₘ j.hom).val.app W
          ((k.mu M U).hom.val.app W
            ((ε.inv.app P).val.app W
              ((CochainScalarConstruction.tensorUnit c (I.modules.obj P)).hom.app W m)))) =
      (L.map (UnitConstruction.explicitRightUnitor R M).hom).val.app W ((ε.inv.app P).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj P)).hom.app W m))
    rw [← hq P W m]
    let t := (I.moduleUnderlying.hom.app P).hom.app W m
    let a := (uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t
    let b := (uInv.map y ≫ I.moduleUnderlying.inv.app U).hom.app W t
    have hc : (I.moduleUnderlying.inv.app P).hom.app W t = m :=
      congrArg (fun f ↦ f.hom.app W m) (I.moduleUnderlying.app P).hom_inv_id
    have hp := comparison_pure_apply R S RI uInv I c L hobj
      k M U Z x y (𝟙 Z) hz W t
    rw [uInv.map_id] at hp
    change (k.mu M U).hom.val.app W
        ((k.q P).hom.app W ((I.moduleUnderlying.inv.app P).hom.app W t)) =
      ringedComparisonPure S (L.obj M) (L.obj U) W
        ((k.q M).hom.app W a) ((k.q U).hom.app W b) at hp
    rw [hc] at hp
    have hb : (UnitConstruction.unitSetIso R RI uInv I).hom.hom.app W b =
        (1 : RI.obj.obj W) := by
      have hi := congrArg (fun f ↦ f.hom.app W ((uInv.map y).hom.app W t))
        (I.moduleUnderlying.app U).inv_hom_id
      change (I.moduleUnderlying.hom.app U).hom.app W b =
        (uInv.map y).hom.app W t at hi
      change I.ringUnderlying.hom.hom.app W
        ((I.moduleUnderlying.hom.app U).hom.app W b) = (1 : RI.obj.obj W)
      rw [hi]
      exact I.ringOne Z y (fun _ _ ↦ rfl) W t
    have hu : j.hom.val.app W ((k.q U).hom.app W b) = (1 : S.obj.obj W) := by
      exact (unitComparisonIso_insertion R S RI uInv I c L hobj k W b).trans
        ((congrArg ((c.hom.app W).hom) hb).trans (map_one _))
    have ha : a = (I.modules.map (UnitConstruction.explicitRightUnitor R M).hom).val.app W m := by
      have hi := congrArg (fun f ↦ f.hom.app W t)
        (I.moduleUnderlying.inv.naturality (UnitConstruction.explicitRightUnitor R M).hom)
      change a = (I.modules.map (UnitConstruction.explicitRightUnitor R M).hom).val.app W
        ((I.moduleUnderlying.inv.app P).hom.app W t) at hi
      exact hi.trans (congrArg
        ((I.modules.map (UnitConstruction.explicitRightUnitor R M).hom).val.app W) hc)
    have he := UnitConstruction.unitor_map_pure S (L.obj M) (L.obj U) j.hom W
      ((k.q M).hom.app W a) ((k.q U).hom.app W b) hu
    exact (congrArg (fun z ↦ (UnitConstruction.explicitRightUnitor S (L.obj M)).hom.val.app W
      ((𝟙 (L.obj M) ⊗ₘ j.hom).val.app W z)) hp).trans
        (he.trans ((congrArg ((k.q M).hom.app W) ha).trans
          (hqmap (UnitConstruction.explicitRightUnitor R M).hom W m).symm))
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  exact UnitConstruction.explicitUnitMap_unique R S L k.mu j' j hj' hj

attribute [local semireducible] monoidalCategory
attribute [local semireducible] UnitConstruction.explicitRightUnitor

private theorem normalizedUnitNative
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := by
  exact normalizedUnit R S RI uInv I c L hobj hmap k

end GenericUnit

attribute [local semireducible] monoidalCategory
attribute [local semireducible] UnitConstruction.explicitRightUnitor

/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j. -/
theorem canonicalRingedTensorComparison_unit
    (hmap : ∀ {M N : (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj S),
      ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{max s h}
          RingCat.{max s h})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := by
  exact normalizedUnitNative R S RI uInv I c L hobj hmap k

attribute [local irreducible] monoidalCategory
attribute [local instance 20000] cochainTensorLeftPreservesColimits
  cochainTensorRightPreservesColimits

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JC
      (forget₂
      CommRingCat.{max s h} RingCat.{max s h})).obj R)) _ (monoidalCategory R))) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  exact tensorPullbackTotal L k.mu k.naturality P Q

attribute [local irreducible] CanonicalRingedTensorComparison.total

/-- The specified total comparison is an isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: its summand maps are the inverse ordinary comparisons. Pullback is a left
adjoint and preserves the coproducts defining total complexes. Thus each component
is an isomorphism, and so is the chain map. -/
theorem CanonicalRingedTensorComparison.total_isIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :
    IsIso (k.total R S RI uInv I c L hobj P Q) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  unfold CanonicalRingedTensorComparison.total
  exact tensorPullbackTotal_isIso L k.mu k.naturality V am P Q

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :=
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (k.total_isIso R S RI uInv I c L hobj V am P Q)

end SheafOfModules.CanonicalTensorPullbackOfUniverses
