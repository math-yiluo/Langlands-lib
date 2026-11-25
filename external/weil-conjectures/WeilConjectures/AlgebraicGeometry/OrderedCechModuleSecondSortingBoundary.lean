/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleProjectionLift
public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechSecondSortingIdentity
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleSecondSortingLift
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # The second sorting boundary for module Čech cochains

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def sortingSectionSite {X : Scheme.{u}} {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) :
    SiteCechComplex (fun i : Fin r ↦ W ⟨i⟩ ⨯ B)
      (fun i ↦ homOfLE (le_top : (W ⟨i⟩ ⨯ B) ≤ ⊤)) where
  W p t := (∏ᶜ fun k : Fin (p + 1) ↦ W ⟨t k⟩) ⨯ B
  pr p t k := prod.map (Pi.π (fun l ↦ W ⟨t l⟩) k) (𝟙 B)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨prod.lift (Pi.lift fun k ↦ a k ≫ prod.fst) (a 0 ≫ prod.snd), ?_, ?_⟩
    · intro k; exact Subsingleton.elim _ _
    · intro b _; exact Subsingleton.elim _ _
  W_zero := by
    intro t
    apply le_antisymm
    · exact (prod.map (Pi.π (fun l : Fin (0 + 1) ↦ W ⟨t l⟩) 0) (𝟙 B)).le
    · exact (prod.map (Pi.lift fun l : Fin (0 + 1) ↦
        eqToHom (by rw [Fin.eq_zero l])) (𝟙 B)).le
  pr_zero := by intro t; exact Subsingleton.elim _ _
  indexMap t α := prod.map (Pi.lift fun l ↦ Pi.π (fun k ↦ W ⟨t k⟩) (α l)) (𝟙 B)
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private noncomputable def sortingSectionCochain {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    (sortingSectionSite W B).cochains M.presheaf p :=
  fun t ↦ orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t k⟩) s

private noncomputable def secondSortingFamily {X : Scheme.{u}}
    (D : CochainComplex X.Modules ℕ) (K : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) : D.X i ⟶ D.X j :=
  eqToHom (congrArg D.X h.symm) ≫ K j

set_option backward.isDefEq.respectTransparency false in
private theorem sortingSectionCochain_differential {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).d p (p + 1))
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    sortingSectionCochain M W D e (p + 1) B ((D.d p (p + 1)).app B s) =
      (sortingSectionSite W B).differentialValue M.presheaf p
        (sortingSectionCochain M W D e p B s) := by
  classical
  funext t
  let F := (prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat
  have h := congrArg
    (fun f ↦ ((f ≫ TopCat.Presheaf.cechComplexFunctorπ W F (p + 1)
      (fun k ↦ ⟨t k⟩)).app (op B)) s) (hd p)
  simp only [Category.assoc] at h
  rw [TopCat.Presheaf.cechComplexFunctor_d_π W F] at h
  change orderedCechNaturalCoordinate M W D e (p + 1) B (fun k ↦ ⟨t k⟩)
    ((D.d p (p + 1)).app B s) = _ at h
  unfold sortingSectionCochain
  rw [h]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, NatTrans.app_sum, NatTrans.app_zsmul,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  unfold SiteCechComplex.differentialValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1

private theorem sortingSectionCochain_secondSorting {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (K : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (hK : ∀ (p : ℕ) (B : X.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W D e p B y ((K p).app B s) =
          orderedCechSecondSortingValue M W D e p B y s)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X (p + 1), B)) :
    sortingSectionCochain M W D e p B ((K p).app B s) =
      cechSecondSortingHom X (fun i : Fin r ↦ W ⟨i⟩ ⨯ B) M.presheaf
        (sortingSectionSite W B) p (sortingSectionCochain M W D e (p + 1) B s) := by
  classical
  funext t
  change orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t k⟩)
    ((K p).app B s) = _
  rw [hK]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sortingSectionCochain_boundary {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (K : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (hK : ∀ (p : ℕ) (B : X.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W D e p B y ((K p).app B s) =
          orderedCechSecondSortingValue M W D e p B y s)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).d p (p + 1))
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    sortingSectionCochain M W D e p B
        (((Homotopy.nullHomotopicMap' (secondSortingFamily D K)).f p).app B s) =
      ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X
        (fun i : Fin r ↦ W ⟨i⟩ ⨯ B) M.presheaf (sortingSectionSite W B))).f p)
          (sortingSectionCochain M W D e p B s) := by
  classical
  cases p with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (show
      (ComplexShape.up ℕ).Rel 0 1 from rfl) (by intro l h; change l + 1 = 0 at h; omega)]
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (show
      (ComplexShape.up ℕ).Rel 0 1 from rfl) (by intro l h; change l + 1 = 0 at h; omega)]
    simp only [secondSortingFamily, cechSecondSortingFamily, eqToHom_refl,
      Category.id_comp, Hom.comp_app, ConcreteCategory.comp_apply]
    rw [sortingSectionCochain_secondSorting M W D e K hK,
      sortingSectionCochain_differential M W D e hd]
    rfl
  | succ p =>
    rw [Homotopy.nullHomotopicMap'_f (show
      (ComplexShape.up ℕ).Rel p (p + 1) from rfl) (show
      (ComplexShape.up ℕ).Rel (p + 1) (p + 1 + 1) from rfl)]
    rw [Homotopy.nullHomotopicMap'_f (show
      (ComplexShape.up ℕ).Rel p (p + 1) from rfl) (show
      (ComplexShape.up ℕ).Rel (p + 1) (p + 1 + 1) from rfl)]
    simp only [secondSortingFamily, cechSecondSortingFamily, eqToHom_refl,
      Category.id_comp, Hom.add_app, Hom.comp_app, AddCommGrpCat.hom_add_apply,
      ConcreteCategory.comp_apply]
    have hadd (a b : Γ(D.X (p + 1), B)) :
        sortingSectionCochain M W D e (p + 1) B (a + b) =
          sortingSectionCochain M W D e (p + 1) B a +
            sortingSectionCochain M W D e (p + 1) B b := by
      funext t
      simp only [sortingSectionCochain, orderedCechNaturalCoordinate, map_add]
      rfl
    rw [hadd, sortingSectionCochain_secondSorting M W D e K hK,
      sortingSectionCochain_differential M W D e hd,
      sortingSectionCochain_differential M W D e hd,
      sortingSectionCochain_secondSorting M W D e K hK]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl

open Classical in
/-- The second sorting operator assembles into module-sheaf maps.
Source: Stacks Project, Tag 01FM, equation 20.23.6.2.
(blueprint: lem-pc-ordered-cech-module-second-sorting-boundary).

Proof: On an open B of X', identify the full cochains of D with sections on the
products of the W₀ using e. Apply the explicit first-repeat sum cechSecondSortingHom:
sum over the stable permutation and its first adjacent equality, inserting a copy with coefficient
sign(sigma) (-1)^a.
The intersection arrows are the unique arrows of opens with the prescribed tuple
projections. Transport the output back through e inverse. Every summand is additive.
Naturality of e and functoriality of restriction show naturality in B. For local
linearity, apply hlinear to each input coordinate; the two paths restricting a
scalar to the output intersection agree in the poset of opens. Since e is bijective,
the output coordinates determine a locally linear section map. These maps define
morphisms of module sheaves in adjacent natural degrees. Push them forward along f'
and conjugate by extendXIso in nonnegative degrees; put zero in all other degrees.
Apply cechSecondSortingIdentity on each open, using hd for the transported
differential. The categorical products of opens identify with the intersections in
SiteCechComplex, by their universal properties. The stable-sorting term is exactly
the displayed permutation sum, with prod.map giving the same unique restriction.
For the alternating term, the strict filter gives exactly hP: its ordered-coordinate transport
followed by orderedCechProjectionOpenMap is the same unique open map as the permutation transport.
Thus the boundary is stable sorting minus P.
In degree zero the incoming term vanishes in both natural and extended complexes.
For r=0 the products of section groups indexed by tuples are empty, hence zero;
no nonempty or covering assumption is used. Repeated tuples are retained by stable sorting,
including in degrees above r;
the alternating projection is zero there and the first-repeat formula still applies. -/
theorem orderedCech_module_secondSorting_boundary {X' T' : Scheme.{u}} (f' : X' ⟶ T')
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
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s)
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat))
    (hP : IsOrderedCechModuleProjection f' M W₀ D e P) :
    let L := ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)
    ∃ H : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel j i → (L.X i ⟶ L.X j),
      ∀ (p : ℕ) (B : T'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
        (s : Γ(L.X (p : ℤ), B)),
        orderedCechFullCoordinate f' M W₀ D e p B y
          (((Homotopy.nullHomotopicMap' H).f (p : ℤ)).app B s) =
          (∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort (fun l ↦ (y l).down) σ then
          (Equiv.Perm.sign σ : ℤ) •
            M.presheaf.map (prod.map
              (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
                (orderedCechFullCoordinate f' M W₀ D e p B (y ∘ σ) s)
        else 0) -
          orderedCechFullCoordinate f' M W₀ D e p B y ((P.f (p : ℤ)).app B s)
        := by
  classical
  obtain ⟨K, hK⟩ := orderedCech_secondSorting_degreewise_exists M W₀ D e hlinear
  let q := Homotopy.nullHomotopicMap' (secondSortingFamily D K)
  let v := ((Modules.pushforward f').mapHomologicalComplex (ComplexShape.up ℕ)).map q
  let h := ((Modules.pushforward f').mapHomotopy
    (Homotopy.nullHomotopy' (secondSortingFamily D K))).extend ComplexShape.embeddingUpNat
  let H := fun i j (_ : (ComplexShape.up ℤ).Rel j i) ↦ h.hom i j
  have hb : Homotopy.nullHomotopicMap' H =
      HomologicalComplex.extendMap v ComplexShape.embeddingUpNat := by
    have he : (fun i j ↦ @dite _ ((ComplexShape.up ℤ).Rel j i)
        (Classical.propDecidable _) (H i j) (fun _ ↦ 0)) =
        h.hom := by
      funext i j
      split_ifs with hij
      · rfl
      · exact (h.zero i j hij).symm
    change Homotopy.nullHomotopicMap _ = _
    refine (congrArg (fun t ↦ Homotopy.nullHomotopicMap t) he).trans ?_
    apply HomologicalComplex.Hom.ext
    funext i
    have hi := h.comm i
    change (dNext i h.hom + prevD i h.hom) = _
    simpa only [Functor.map_zero, HomologicalComplex.extendMap_zero,
      HomologicalComplex.zero_f_apply, add_zero] using hi.symm
  refine ⟨H, ?_⟩
  intro p B y s
  rw [hb]
  let E := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  have hv : E.hom.app B
      (((HomologicalComplex.extendMap v ComplexShape.embeddingUpNat).f (p : ℤ)).app B s) =
      (q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s) := by
    rw [HomologicalComplex.extendMap_f v ComplexShape.embeddingUpNat
      (i := p) (i' := (p : ℤ)) rfl]
    change E.hom.app B (E.inv.app B ((q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s))) = _
    have hi := congrArg (fun k ↦ (k.app B) ((q.f p).app (f' ⁻¹ᵁ B)
      (E.hom.app B s))) E.inv_hom_id
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      CategoryTheory.id_apply] using hi
  change orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B) y
    (E.hom.app B _) = _
  rw [hv]
  have ht := congrFun (sortingSectionCochain_boundary M W₀ D e K hK hd p
    (f' ⁻¹ᵁ B) (E.hom.app B s)) (fun k ↦ (y k).down)
  rw [cechSecondSortingIdentity] at ht
  rw [hP p B s y]
  change orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B) y
    ((q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s)) = _ at ht
  change orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B) y
      ((q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s)) =
    (∑ σ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort (fun l ↦ (y l).down) σ then
        (Equiv.Perm.sign σ : ℤ) • M.presheaf.map (prod.map
          (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
            (orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B)
              (y ∘ σ) (E.hom.app B s)) else 0) -
    (∑ σ : Equiv.Perm (Fin (p + 1)),
      if StrictMono (fun l ↦ (y (σ l)).down) then
        (Equiv.Perm.sign σ : ℤ) • M.presheaf.map (prod.map
          (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
            (orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B)
              (y ∘ σ) (E.hom.app B s)) else 0) at ht
  rw [ht]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with hs
  · congr 1
    change M.presheaf.map _ _ =
      M.presheaf.map (orderedCechProjectionOpenMap W₀ (f' ⁻¹ᵁ B) y σ hs).op
        (M.presheaf.map (orderedCechTupleOpenMap W₀ (f' ⁻¹ᵁ B)
          (OrderEmbedding.ofStrictMono _ hs)).op _)
    change M.presheaf.map _ _ = (M.presheaf.map _ ≫ M.presheaf.map _) _
    rw [← M.presheaf.map_comp]
    congr 2
  · rfl


end AlgebraicGeometry.Scheme.Modules
