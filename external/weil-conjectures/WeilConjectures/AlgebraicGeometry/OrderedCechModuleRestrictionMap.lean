/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Ordered restriction as a module cochain map

Source: Stacks Project, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordered coordinates of the usual differential are the signed face sum.
Source: Stacks Project, Tags 01FJ and 01FK, ordered restriction.
(blueprint: lem-pc-ordered-cech-module-restriction-map).

Proof: Transport the extended differential through extendXIso in degrees p and p+1.
Evaluation of pushforward is evaluation on the inverse-image open. Apply hd to
replace the differential transported through e by the usual Cech differential.
Project to the tuple t and expand that differential as the alternating sum of
its face maps. Restriction along orderedCechTupleOpenMap is additive and commutes
with integer scalar multiplication, so it passes through the sum. For each face,
the composite from the ordered full intersection to the categorical face product
is the composite through the ordered face intersection: opens form a poset, so
the two arrows with these endpoints agree. The resulting terms are precisely
the ordered coordinates in the asserted formula. -/
private theorem orderedCechModuleCoordinate_d {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (p : ℕ) (B : T'.Opens)
    (s : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
    (t : Fin (p + 2) ↪o Fin r) :
    orderedCechModuleCoordinate f' M W₀ D e (p + 1) B t
      ((((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        M.presheaf.map (homOfLE (inf_le_inf
          (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
            (orderedCechModuleCoordinate f' M W₀ D e p B
              ((Fin.succAboveOrderEmb j).trans t) s)  := by
  classical
  let P := ((Modules.pushforward f').mapHomologicalComplex (ComplexShape.up ℕ)).obj D
  let E (k : ℕ) := P.extendXIso ComplexShape.embeddingUpNat (i := k) rfl
  have he : (E (p + 1)).hom.app B
      (((P.extend ComplexShape.embeddingUpNat).d
        (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) =
      (D.d p (p + 1)).app (f' ⁻¹ᵁ B) ((E p).hom.app B s) := by
    rw [HomologicalComplex.extend_d_eq P ComplexShape.embeddingUpNat
      (i := p) (j := p + 1) (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) rfl rfl]
    change (E (p + 1)).hom.app B
      ((E (p + 1)).inv.app B
        ((D.d p (p + 1)).app (f' ⁻¹ᵁ B) ((E p).hom.app B s))) = _
    have hi := congrArg (fun k ↦ (k.app B)
      ((D.d p (p + 1)).app (f' ⁻¹ᵁ B) ((E p).hom.app B s))) (E (p + 1)).inv_hom_id
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      CategoryTheory.id_apply] using hi
  let F := (prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat
  have h := congrArg
    (fun v ↦ ((v ≫ TopCat.Presheaf.cechComplexFunctorπ W₀ F (p + 1)
      (fun k ↦ ⟨t k⟩)).app (op (f' ⁻¹ᵁ B))) ((E p).hom.app B s)) (hd p)
  simp only [Category.assoc] at h
  rw [TopCat.Presheaf.cechComplexFunctor_d_π W₀ F] at h
  unfold orderedCechModuleCoordinate
  rw [he]
  change M.presheaf.map (orderedCechTupleOpenMap W₀ (f' ⁻¹ᵁ B) t).op
    ((((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
      (D.d p (p + 1)).val ≫ (e (p + 1)).hom ≫
        TopCat.Presheaf.cechComplexFunctorπ W₀ F (p + 1) (fun k ↦ ⟨t k⟩)).app
          (op (f' ⁻¹ᵁ B))) ((E p).hom.app B s)) = _
  erw [h]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, NatTrans.app_sum,
    NatTrans.app_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (M.presheaf.map _ ≫ M.presheaf.map _)
      ((((e p).hom ≫ TopCat.Presheaf.cechComplexFunctorπ W₀ F p
        (fun k ↦ ⟨t (j.succAbove k)⟩)).app (op (f' ⁻¹ᵁ B))) ((E p).hom.app B s)) =
    (M.presheaf.map _ ≫ M.presheaf.map _)
      ((((e p).hom ≫ TopCat.Presheaf.cechComplexFunctorπ W₀ F p
        (fun k ↦ ⟨t (j.succAbove k)⟩)).app (op (f' ⁻¹ᵁ B))) ((E p).hom.app B s))
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to increasing coordinates is a morphism of module cochain complexes.
Source: Stacks Project, Tags 01FJ and 01FK, ordered restriction.
(blueprint: lem-pc-ordered-cech-module-restriction-map).

Proof: In degree p and on B take the inverse of a p B applied to the family of
orderedCechModuleCoordinate values. Additivity follows from additivity of a and
of every coordinate. Apply a to the naturality and scalar equations: hn and hl
reduce them to the proved naturality and scalar formulas for the coordinates.
Thus these formulas define morphisms of module sheaves. For the differential,
apply a and evaluate at an increasing tuple; ha gives the alternating sum of
restrictions of the ordered faces. The presentation equation hd identifies this
sum with the ordered coordinate of the usual differential. The restriction
composites agree since opens form a poset. Put the negative components equal to
zero. The source is zero in negative degrees, so its boundary equations vanish.
This proves the chain equation also across degree -1. The coordinate formula is
exactly the inverse-equivalence identity. Empty tuple index sets cause no exception. -/
theorem orderedCech_module_restriction {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ) (hK : K.IsStrictlyGE 0)
    (a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)))
    (hn : ∀ (p : ℕ) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(K.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
      a p B ((K.X (p : ℤ)).presheaf.map i.op s) t =
        M.presheaf.map (homOfLE (inf_le_inf le_rfl
          ((TopologicalSpace.Opens.map f'.base).map i).le)).op (a p C s t))
    (hl : ∀ (p : ℕ) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(K.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
      a p B (b • s) t =
        X'.presheaf.map (homOfLE (show
          alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
            from inf_le_right)).op (f'.app B b) • a p B s t)
    (ha : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (a p B s ((Fin.succAboveOrderEmb j).trans t)))
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s) :
    ∃ rmap : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶ K,
      ∀ (p : ℕ) (B : T'.Opens) (s : Γ(
        ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
        (t : Fin (p + 1) ↪o Fin r),
        a p B ((rmap.f (p : ℤ)).app B s) t =
          orderedCechModuleCoordinate f' M W₀ D e p B t s := by
  classical
  have := hK
  let L : CochainComplex T'.Modules ℤ :=
    (((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
    ComplexShape.embeddingUpNat
  let q := orderedCechModuleCoordinate f' M W₀ D e
  let ψ : ∀ p : ℕ, (L.X (p : ℤ)).presheaf ⟶ (K.X (p : ℤ)).presheaf := fun p ↦
      { app := fun B ↦ AddCommGrpCat.ofHom
          { toFun := fun s ↦ (a p B.unop).symm (fun t ↦ q p B.unop t s)
            map_zero' := by
              apply (a p B.unop).injective
              simp only [map_zero, AddEquiv.apply_symm_apply]
              funext t
              exact orderedCechModuleCoordinate_zero f' M W₀ D e p B.unop t
            map_add' := by
              intro s s'
              apply (a p B.unop).injective
              simp only [map_add, AddEquiv.apply_symm_apply]
              funext t
              exact orderedCechModuleCoordinate_add f' M W₀ D e p B.unop t s s' }
        naturality := by
          intro B C i
          ext s
          apply (a p C.unop).injective
          funext t
          change a p C.unop ((a p C.unop).symm _) t =
            a p C.unop ((K.X (p : ℤ)).presheaf.map i
              ((a p B.unop).symm _)) t
          rw [AddEquiv.apply_symm_apply]
          have h := hn p i.unop ((a p B.unop).symm (fun t ↦ q p B.unop t s)) t
          rw [AddEquiv.apply_symm_apply] at h
          exact (orderedCechModuleCoordinate_naturality f' M W₀ D e p i.unop s t).trans
            h.symm }
  have hψ (p : ℕ) (B : T'.Opens) (b : Γ(T', B)) (s : Γ(L.X (p : ℤ), B)) :
      (ψ p).app (op B) (b • s) = b • (ψ p).app (op B) s := by
    apply (a p B).injective
    funext t
    change a p B ((a p B).symm _) t = a p B (b • (a p B).symm _) t
    rw [AddEquiv.apply_symm_apply, hl, AddEquiv.apply_symm_apply]
    exact orderedCechModuleCoordinate_smul f' M W₀ D e hlinear p B t b s
  let R : ∀ p : ℕ, L.X (p : ℤ) ⟶ K.X (p : ℤ) := fun p ↦
    ⟨PresheafOfModules.homMk (ψ p) (fun B ↦ hψ p B.unop)⟩
  have hR (p : ℕ) (B : T'.Opens) (s : Γ(L.X (p : ℤ), B))
      (t : Fin (p + 1) ↪o Fin r) :
      a p B ((R p).app B s) t = q p B t s := by
    exact congrFun ((a p B).apply_symm_apply _) t
  have hcomm (p : ℕ) :
      R p ≫ K.d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
        L.d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫ R (p + 1) := by
    apply Modules.hom_ext
    intro B
    ext s
    apply (a (p + 1) B).injective
    funext t
    change a (p + 1) B ((K.d _ _).app B ((R p).app B s)) t =
      a (p + 1) B ((R (p + 1)).app B ((L.d _ _).app B s)) t
    rw [ha, hR]
    simp_rw [hR]
    exact (orderedCechModuleCoordinate_d f' M W₀ D e hd p B s t).symm
  let RZ : ∀ i : ℤ, L.X i ⟶ K.X i := fun i ↦
    match i with
    | Int.ofNat p => R p
    | Int.negSucc p => (K.isZero_of_isStrictlyGE 0 (Int.negSucc p) (by omega)).from_ _
  let rmap : L ⟶ K :=
    { f := RZ
      comm' := by
        intro i j hij
        change i + 1 = j at hij
        subst j
        cases i with
        | ofNat p =>
          exact hcomm p
        | negSucc p =>
          exact (L.isZero_of_isStrictlyGE 0 (Int.negSucc p) (by omega)).eq_of_src _ _ }
  exact ⟨rmap, hR⟩

end AlgebraicGeometry.Scheme.Modules
