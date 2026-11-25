/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitUnique
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction

/-!
# Canonical representative comparison for tensor pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The inverse ordinary tensor comparison, summed over all bidegrees.
Source: Stacks 07A4, last display of the proof
(auxiliary; not a blueprint node). -/
noncomputable def tensorPullbackTotalComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).X n ⟶
        L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary summand comparison commutes with the two tensor differentials.
Source: Stacks 07A4, construction of the total comparison
(auxiliary; not a blueprint node).
Proof: test on every summand. Naturality of e handles d_P and d_Q separately.
Additivity of L preserves the sign (-1)^a on the second differential. The two
summand equations add to the asserted chain-map equation. -/
theorem tensorPullbackTotalComponent_comm
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    tensorPullbackTotalComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).d n m ≫
          tensorPullbackTotalComponent L e P Q m := by
  have hi {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y') :
      (e X Y).inv ≫ L.map (f ⊗ₘ g) =
        (L.map f ⊗ₘ L.map g) ≫ (e X' Y').inv := by
    apply (cancel_mono (e X' Y').hom).1
    rw [Category.assoc, he, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    simp only [tensorPullbackTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    simp only [L.map_add, Preadditive.comp_add, Category.assoc]
    rw [← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega)]
    simp only [
      ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      one_smul, Functor.map_units_smul, Functor.map_comp,
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d, ← tensorHom_id, ← id_tensorHom]
    dsimp only [Functor.mapHomologicalComplex, curriedTensor_obj_obj]
    apply congrArg₂ (· + ·)
    · simpa only [L.map_id, Category.assoc] using
        congrArg (fun f ↦ f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            (a + 1) b (n + 1) (by omega))) (hi (P.d a (a + 1)) (𝟙 (Q.X b)))
    · simpa only [L.map_id, Category.assoc, Linear.units_smul_comp,
        Linear.comp_units_smul] using
        congrArg (fun f ↦ a.negOnePow • (f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            a (b + 1) (n + 1) (by omega)))) (hi (𝟙 (P.X a)) (Q.d b (b + 1)))
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm,
      L.map_zero, comp_zero, zero_comp]

/-- The chain comparison is the signed total of the inverse ordinary comparisons.
Source: Stacks 07A4, final display
(auxiliary; not a blueprint node). -/
noncomputable def tensorPullbackTotal
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (P Q : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B) ⟶
        (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q (curriedTensor A)) where
  f := tensorPullbackTotalComponent L e P Q
  comm' n m _ := tensorPullbackTotalComponent_comm L e he P Q n m

/-- A left adjoint preserves the coproducts defining total tensor, so beta is invertible.
Source: Stacks 07A4 and Modules on Sites 03D7
(auxiliary; not a blueprint node).
Proof: each inverse ordinary comparison is invertible. The adjunction identifies
maps out of a pulled-back coproduct with families of maps out of the pulled-back
summands, so its coproduct comparison is invertible. Each degree of beta is the
composite of these two isomorphisms. A degreewise isomorphism of complexes is an
isomorphism of complexes. -/
theorem tensorPullbackTotal_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ) :
    IsIso (tensorPullbackTotal L e he P Q) := by
  let := adj.isLeftAdjoint
  have (n : ℤ) : IsIso ((tensorPullbackTotal L e he P Q).f n) := by
    let f := Cofan.IsColimit.desc
      (HomologicalComplex.mapBifunctor.isColimitMapCofan
        (G := L) (F := curriedTensor A) (c := ComplexShape.up ℤ) P Q n)
      (fun x ↦ (e (P.X x.1.1) (Q.X x.1.2)).hom ≫
        CochainComplex.ιMapBifunctor
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
          (curriedTensor B) x.1.1 x.1.2 n x.2)
    have hf (a b : ℤ) (h : a + b = n) :
        L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h) ≫ f =
          (e (P.X a) (Q.X b)).hom ≫
            CochainComplex.ιMapBifunctor
              ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
              ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
              (curriedTensor B) a b n h :=
      Cofan.IsColimit.fac
        (HomologicalComplex.mapBifunctor.isColimitMapCofan
          (G := L) (F := curriedTensor A) (c := ComplexShape.up ℤ) P Q n)
        _ ⟨⟨a, b⟩, h⟩
    refine ⟨f, ?_, ?_⟩
    · apply HomologicalComplex.mapBifunctor.hom_ext
      intro a b h
      dsimp only [tensorPullbackTotal]
      simp only [tensorPullbackTotalComponent,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, Category.assoc, hf,
        Iso.inv_hom_id_assoc, Category.comp_id]
    · apply HomologicalComplex.mapBifunctor.hom_ext_of_map L
      intro a b h
      rw [← Category.assoc, hf, Category.assoc]
      dsimp only [tensorPullbackTotal]
      simp only [tensorPullbackTotalComponent,
        HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
      dsimp only [Functor.mapHomologicalComplex]
      rw [Category.comp_id]
  exact HomologicalComplex.Hom.isIso_of_components _

universe wA wB

/-- Transport the homotopy left-derived comparison to the complex localization Q.
Source: Stacks 06YY and 07A4
(auxiliary; not a blueprint node). -/
noncomputable def derivedPullbackComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    epsilon.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

end CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

universe w

section TensorSections

attribute [local irreducible] monoidalCategory

open scoped ChangeOfRings TensorProduct
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
  (A B : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

@[no_expose] private noncomputable def ts (M N : SheafOfModules.{u} (𝓡 B))
    (W : Dᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[B.obj.obj W] n))
private theorem ts_naturality (M N : SheafOfModules.{u} (𝓡 B))
    {W V : Dᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.map i (ts B M N W m n) =
      ts B M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)
  let v := m ⊗ₜ[B.obj.obj W] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)
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

private theorem productElements {E : Type u} [Category.{v} E] [HasBinaryProducts E]
    (F : E ⥤ Type v) (X Y : E) [PreservesLimit (pair X Y) F]
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
    (W : Dᵒᵖ) (m : M.val.obj W) : (changeOfRings.{u, u, u} c M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} c M)).app W
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))
-- Expand the two scalar extensions through the sheafification adjunction.
private theorem scalar_tensor_ext
    (M N : SheafOfModules.{u} (𝓡 A)) (H : SheafOfModules.{u} (𝓡 B))
    {f g : (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
      (changeOfRings.{u, u, u} c N) ⟶ H}
    (h : ∀ W m n, f.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n)) =
      g.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n))) : f = g := by
  let := monoidalCategory B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)
  let S := PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)
  let E := changeOfRingsPresheaf.{u, u, u} c M
  let F := changeOfRingsPresheaf.{u, u, u} c N
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  have hη (G : PresheafOfModules.{u} (𝓡 B).obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf (𝓡 B).obj)) (adj.unit.app G) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)]
    change IsIso (S.map (adj.unit.app G))
    dsimp only [S, adj]
    infer_instance
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf (𝓡 B).obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫ (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := inferInstance
  apply (cancel_epi q).mp
  apply (adj.homEquiv (E ⊗ F) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing ((𝓡 B).obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : (E.obj W) ⊗[(𝓡 B).obj.obj W] (F.obj W) →ₗ[(𝓡 B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (𝓡 B) ⋙ PresheafOfModules.restrictScalars (𝟙 (𝓡 B).obj)).map
          (q ≫ f)).app W).hom
  let b : (E.obj W) ⊗[(𝓡 B).obj.obj W] (F.obj W) →ₗ[(𝓡 B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (𝓡 B) ⋙ PresheafOfModules.restrictScalars (𝟙 (𝓡 B).obj)).map
          (q ≫ g)).app W).hom
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of ((𝓡 B).obj.obj W) ((F.obj W) →ₗ[(𝓡 B).obj.obj W] H.val.obj W))
        (TensorProduct.curry a) = ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of ((𝓡 B).obj.obj W) ((F.obj W) →ₗ[(𝓡 B).obj.obj W] H.val.obj W))
          (TensorProduct.curry b) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry a _ = TensorProduct.curry b _
    have hm : ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
        (TensorProduct.curry a ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
          (TensorProduct.curry b ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      have hn := adj.unit.naturality (ηE ⊗ₘ ηF)
      have he := congrArg (fun k ↦ (k.app W)
        (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) hn
      change (adj.unit.app ((S.obj E).val ⊗ (S.obj F).val)).app W
          (ηE.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
            ⊗ₜ[B.obj.obj W]
            ηF.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
        (S.map (ηE ⊗ₘ ηF)).val.app W
          ((adj.unit.app (E ⊗ F)).app W
            (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) at he
      change f.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _))) =
        g.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _)))
      exact (congrArg (fun v ↦ f.val.app W
        ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he.symm).trans
          ((h W m n).trans (congrArg (fun v ↦ g.val.app W
            ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he))
    exact congrArg ModuleCat.Hom.hom hm
  exact ModuleCat.hom_ext (TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh))

private theorem ts_cast
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{u, u, u} c M)
    (hy : Y = changeOfRings.{u, u, u} c N)
    (W : Dᵒᵖ) (m : (changeOfRings.{u, u, u} c M).val.obj W)
    (n : (changeOfRings.{u, u, u} c N).val.obj W) :
    (eqToHom (congrArg₂ (monoidalCategory B).tensorObj hx.symm hy.symm)).val.app W
      (ts B (changeOfRings.{u, u, u} c M) (changeOfRings.{u, u, u} c N) W m n) =
    ts B X Y W ((eqToHom hx.symm).val.app W m)
      ((eqToHom hy.symm).val.app W n) := by
  subst X
  subst Y
  rfl

private theorem scalarTensorSections_hom_ext
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y H : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{u, u, u} c M)
    (hy : Y = changeOfRings.{u, u, u} c N)
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
      (ts B (changeOfRings.{u, u, u} c M) (changeOfRings.{u, u, u} c N) W
        (ins A B c M W m) (ins A B c N W n))) =
    g.val.app W (e.val.app W
      (ts B (changeOfRings.{u, u, u} c M) (changeOfRings.{u, u, u} c N) W
        (ins A B c M W m) (ins A B c N W n)))
  dsimp only [e]
  rw [ts_cast A B c M N X Y hx hy]
  exact h W m n

end TensorSections

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
theorem ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  by
    let := monoidalCategory R
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

section TensorUniqueness

attribute [local irreducible] monoidalCategory

set_option backward.isDefEq.respectTransparency.types false

-- Compare bilinear maps through sheafification and the scalar-extension adjunctions.
/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (auxiliary; not a blueprint node).
Proof: use the separate existence construction for the specified inverse-image lift.
For uniqueness, q_one fixes q on every section. Preservation of binary products lifts
every pair of inverse-image sections to a generalized pair. The two pure equations
then identify the inverse tensorators on inserted pure tensors. Cancel tensor
sheafification and apply the two scalar-extension adjunctions to obtain equality
on the whole tensor product. Proof irrelevance identifies all remaining law fields. -/
theorem canonicalRingedTensorComparison_existsUnique
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by
  refine ⟨canonicalRingedTensorComparison_nonempty R S RI uInv I c L hobj uPush adj hmap, ?_⟩
  refine ⟨fun a b ↦ ?_⟩
  rcases a with ⟨qa, hqa, ma, hna, hpa⟩
  rcases b with ⟨qb, hqb, mb, hnb, hpb⟩
  have hqq : qa = qb := by
    funext M
    ext W m
    exact (hqa M W m).trans (hqb M W m).symm
  subst qb
  have hmm : ma = mb := by
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
    have ha := hpa M N Z x y z hz W t
    have hb := hpb M N Z x y z hz W t
    let v := (uInv.map z ≫ I.moduleUnderlying.inv.app
      ((monoidalCategory R).tensorObj M N) ≫ qa
        ((monoidalCategory R).tensorObj M N)).hom.app W t
    change (ma M N).hom.val.app W v = ts S (L.obj M) (L.obj N) W
      ((qa M).hom.app W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t))
      ((qa N).hom.app W ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) at ha
    rw [hm, hn] at ha
    change (mb M N).hom.val.app W v = ts S (L.obj M) (L.obj N) W
      ((qa M).hom.app W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t))
      ((qa N).hom.app W ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) at hb
    rw [hm, hn] at hb
    have hai := congrArg (fun w ↦ (ma M N).inv.val.app W w) ha
    have hbi := congrArg (fun w ↦ (mb M N).inv.val.app W w) hb
    have hai' : (ma M N).inv.val.app W ((ma M N).hom.val.app W v) = v :=
      congrArg (fun f ↦ f.val.app W v) (ma M N).hom_inv_id
    have hbi' : (mb M N).inv.val.app W ((mb M N).hom.val.app W v) = v :=
      congrArg (fun f ↦ f.val.app W v) (mb M N).hom_inv_id
    rw [hai'] at hai
    rw [hbi'] at hbi
    have hi := hai.symm.trans hbi
    rw [hqa M W m, hqa N W n] at hi
    exact hi
  cases hmm
  rfl

end TensorUniqueness

/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(auxiliary; not a blueprint node).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j. -/
theorem canonicalRingedTensorComparison_unit
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := by
  obtain ⟨j, hj⟩ := canonicalRingedTensorComparison_unit_exists R S RI uInv I c L hobj hmap k
  refine ⟨j, hj, ?_⟩
  intro y hy
  exact canonicalRingedTensorComparison_unit_unique R S RI uInv I c L hobj hmap k y j hy hj

attribute [local irreducible] monoidalCategory

namespace CanonicalTensorPullbackProof

open CategoryTheory.Functor in
set_option synthInstance.maxSize 2048 in
private theorem tensorPullbackTotal_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f)
      ((L.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he P' Q' =
      tensorPullbackTotal L e he P Q ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv =
        (e X Y).inv ≫ L.map (a ⊗ₘ b) := by
    apply (cancel_mono (e X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  change (L.map (f.f a) ▷ L.obj (Q.X b)) ≫
    (L.obj (P'.X a) ◁ L.map (g.f b)) ≫ _ = _
  rw [← tensorHom_def_assoc]
  change (L.map (f.f a) ⊗ₘ L.map (g.f b)) ≫ (e (P'.X a) (Q'.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab) ≫
        L.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← Category.assoc, hi, Category.assoc, ← L.map_comp]
  congr 2
  rw [← L.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl

end CanonicalTensorPullbackProof

end SheafOfModules
