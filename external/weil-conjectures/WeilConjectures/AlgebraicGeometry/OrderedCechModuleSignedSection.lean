/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates
import WeilConjectures.AlgebraicGeometry.SignedCechExtension
import WeilConjectures.AlgebraicGeometry.OrderedCechDegreewiseProjection
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Signed extension as a module cochain map

Source: Stacks Project, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The full-tuple value of signed extension of ordered input coordinates.
Source: Stacks 01FI and 01FK, the signed extension formula.
(blueprint: lem-pc-ordered-cech-module-signed-section). -/
private noncomputable def orderedCechSignedSectionValue {X T : Scheme.{u}} (f : X ⟶ T)
    (M : X.Modules) {r : ℕ} (W : ULift.{u} (Fin r) → X.Opens)
    (p : ℕ) (B : T.Opens)
    (s : ∀ t : Fin (p + 1) ↪o Fin r,
      Γ(M, alternatingCechIntersection (fun i ↦ W ⟨i⟩) t ⊓ f ⁻¹ᵁ B))
    (y : Fin (p + 1) → ULift.{u} (Fin r)) :
    Γ(M, (∏ᶜ fun l ↦ W (y l)) ⨯ f ⁻¹ᵁ B) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (p + 1)),
    if h : StrictMono (fun l ↦ (y (σ l)).down) then
      (Equiv.Perm.sign σ : ℤ) •
        M.presheaf.map (homOfLE (le_inf (le_iInf fun l ↦
          (prod.fst ≫ Pi.π (fun k ↦ W (y k)) (σ l)).le) prod.snd.le)).op
            (s (OrderEmbedding.ofStrictMono _ h))
    else 0

/-- Signed extension recovers the input on increasing tuples.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-module-signed-section).
Proof: Only the identity permutation preserves increasing order. Its sign is one,
and the two restriction arrows are inverse in the poset of opens. -/
private theorem orderedCechSignedSectionValue_increasing {X T : Scheme.{u}} (f : X ⟶ T)
    (M : X.Modules) {r : ℕ} (W : ULift.{u} (Fin r) → X.Opens)
    (p : ℕ) (B : T.Opens)
    (s : ∀ t : Fin (p + 1) ↪o Fin r,
      Γ(M, alternatingCechIntersection (fun i ↦ W ⟨i⟩) t ⊓ f ⁻¹ᵁ B))
    (t : Fin (p + 1) ↪o Fin r) :
    M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op
      (orderedCechSignedSectionValue f M W p B s (fun l ↦ ⟨t l⟩)) = s t := by
  classical
  unfold orderedCechSignedSectionValue
  rw [Finset.sum_eq_single (Equiv.refl _)]
  · simp only [Equiv.refl_apply, dite_eq_left t.strictMono, Equiv.Perm.sign_refl,
      Units.val_one, one_smul]
    change (M.presheaf.map _ ≫ M.presheaf.map _)
      (s (OrderEmbedding.ofStrictMono (fun l ↦ t l) t.strictMono)) = s t
    rw [← M.presheaf.map_comp]
    change M.presheaf.map (𝟙 _) (s t) = s t
    rw [M.presheaf.map_id]
    rfl
  · intro σ _ hσ
    have hn : ¬ StrictMono (fun l ↦ t (σ l)) := by
      intro h
      apply hσ
      apply Equiv.ext
      intro l
      apply t.injective
      exact congrFun (Tuple.unique_monotone h.monotone
        (show Monotone (t ∘ Equiv.refl _) from t.monotone)) l
    simp only [dite_eq_right hn]
  · simp

/-- The full-tuple specification for a graded signed extension.
It imposes no differential equation and determines each degree map uniquely.
Source: Stacks 01FI and 01FK.
(blueprint: lem-pc-ordered-cech-module-signed-section). -/
private def IsOrderedCechSignedSection {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ)
    (a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)))
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (q : ∀ p : ℕ, K.X (p : ℤ) ⟶
      (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).X (p : ℤ))) : Prop :=
  ∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
    (y : Fin (p + 1) → ULift.{u} (Fin r)),
    (((e p).hom ≫ Pi.π (fun z : Fin (p + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W₀ (z l)))) y).app (op (f' ⁻¹ᵁ B)))
      (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl).hom.app B ((q p).app B s)) =
      orderedCechSignedSectionValue f' M W₀ p B (a p B s) y

set_option backward.isDefEq.respectTransparency false in
/-- The explicit signed-coordinate formula assembles into graded module-sheaf maps.
No differential compatibility or vanishing in negative degrees is assumed.
Source: Stacks 01FI and 01FK, signed extension of ordered cochains.
(blueprint: lem-pc-ordered-cech-module-signed-section).

Proof: Fix p and a base open B. For every full tuple y sum over the permutations
whose reordered tuple is increasing, with the sign and coefficient restriction
in orderedCechSignedSectionValue. There is one such permutation for an injective
tuple and none for a repeated tuple. Evaluation preserves the product defining
the usual Cech term, so its universal property gives a unique element with these
coordinates. Apply e inverse and then the inverse extension isomorphism. This
constructs the section map, without choosing an arbitrary existence witness.
Additivity follows from additivity of a, restrictions and integer multiplication.
For an inclusion B to C, apply e and each product projection: hn gives the input
restriction, naturality of e gives the output restriction, and the two composites
between opens agree because opens form a poset. Thus these maps are natural.
For a local scalar b, hl pulls b back to each ordered intersection. Semilinearity
of restriction carries it to the full tuple intersection. Integer multiplication
commutes with this action. The output formula hlinear identifies this scalar with
the action on D; injectivity of all coordinates proves local linearity. Use
PresheafOfModules.homMk and the full inclusion of module sheaves to assemble the
maps. Compose with the inverse extension isomorphism. Empty families and degrees
with no increasing tuple give the same construction with all coordinates zero. -/
private theorem orderedCech_signedDegree_exists {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ)
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
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
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
    ∃ q : ∀ p : ℕ, K.X (p : ℤ) ⟶
      (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).X (p : ℤ)),
      IsOrderedCechSignedSection f' M W₀ K a D e q := by
  classical
  let F (p : ℕ) := fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
    ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
        (op (∏ᶜ fun l ↦ W₀ (y l)))
  let V (p : ℕ) (B : X'.Opens) : Γ(D.X p, B) ≃+
      (∀ y : Fin (p + 1) → ULift.{u} (Fin r),
        Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B)) :=
    (((e p).app (op B)) ≪≫
      PreservesProduct.iso ((evaluation _ _).obj (op B)) (F p) ≪≫
      ModuleCat.piIsoPi (fun y ↦ (F p y).obj (op B))).toLinearEquiv.toAddEquiv
  have hV (p : ℕ) (B : X'.Opens) (s : Γ(D.X p, B))
      (y : Fin (p + 1) → ULift.{u} (Fin r)) :
      V p B s y = (((e p).hom ≫ Pi.π (F p) y).app (op B)) s := by
    change (((e p).hom.app (op B) ≫
      (PreservesProduct.iso ((evaluation _ _).obj (op B)) (F p)).hom ≫
      (ModuleCat.piIsoPi (fun y ↦ (F p y).obj (op B))).hom ≫
      ModuleCat.ofHom (LinearMap.proj y)).hom) s = _
    rw [ModuleCat.piIsoPi_hom_ker_subtype]
    erw [PreservesProduct.iso_hom, piComparison_comp_π]
    rfl
  let v (p : ℕ) (B : T'.Opens) : Γ(K.X (p : ℤ), B) →+ Γ(D.X p, f' ⁻¹ᵁ B) :=
    { toFun := fun s ↦ (V p (f' ⁻¹ᵁ B)).symm
        (fun y ↦ orderedCechSignedSectionValue f' M W₀ p B (a p B s) y)
      map_zero' := by
        apply (V p (f' ⁻¹ᵁ B)).injective
        simp only [AddEquiv.apply_symm_apply, map_zero]
        funext y
        simp [orderedCechSignedSectionValue]
      map_add' := by
        intro s z
        apply (V p (f' ⁻¹ᵁ B)).injective
        simp only [AddEquiv.apply_symm_apply, map_add]
        funext y
        simp only [orderedCechSignedSectionValue, Pi.add_apply,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        split_ifs <;> simp only [map_add, smul_add, add_zero] }
  have hv (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
      (y : Fin (p + 1) → ULift.{u} (Fin r)) :
      V p (f' ⁻¹ᵁ B) (v p B s) y =
        orderedCechSignedSectionValue f' M W₀ p B (a p B s) y := by
    exact congrFun ((V p (f' ⁻¹ᵁ B)).apply_symm_apply _) y
  have hVn (p : ℕ) {B C : X'.Opens} (i : B ⟶ C) (s : Γ(D.X p, C))
      (y : Fin (p + 1) → ULift.{u} (Fin r)) :
      V p B ((D.X p).presheaf.map i.op s) y =
        M.presheaf.map (prod.map (𝟙 _) i).op (V p C s y) := by
    rw [hV, hV]
    exact congrArg (fun k ↦ k s) (((e p).hom ≫ Pi.π (F p) y).naturality i.op)
  have hvn (p : ℕ) {B C : T'.Opens} (i : B ⟶ C) (s : Γ(K.X (p : ℤ), C)) :
      v p B ((K.X (p : ℤ)).presheaf.map i.op s) =
        (D.X p).presheaf.map ((TopologicalSpace.Opens.map f'.base).map i).op (v p C s) := by
    apply (V p (f' ⁻¹ᵁ B)).injective
    funext y
    rw [hv, hVn, hv]
    unfold orderedCechSignedSectionValue
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs with h
    · rw [hn, map_zsmul]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _)
        (a p C s (OrderEmbedding.ofStrictMono _ h)) =
        (M.presheaf.map _ ≫ M.presheaf.map _)
          (a p C s (OrderEmbedding.ofStrictMono _ h))
      rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
      congr 2
    · simp only [map_zero]
  have hvl (p : ℕ) (B : T'.Opens) (b : Γ(T', B)) (s : Γ(K.X (p : ℤ), B)) :
      v p B (b • s) = f'.app B b • v p B s := by
    apply (V p (f' ⁻¹ᵁ B)).injective
    funext y
    have hc : V p (f' ⁻¹ᵁ B) (f'.app B b • v p B s) y =
        X'.presheaf.map (prod.snd : (∏ᶜ fun l ↦ W₀ (y l)) ⨯ f' ⁻¹ᵁ B ⟶
          f' ⁻¹ᵁ B).op (f'.app B b) • V p (f' ⁻¹ᵁ B) (v p B s) y := by
      rw [hV, hV]
      exact hlinear p y (f' ⁻¹ᵁ B) (f'.app B b) (v p B s)
    rw [hv, hc, hv]
    unfold orderedCechSignedSectionValue
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs with h
    · rw [hl, map_smul, smul_comm]
      congr 1
      change (X'.presheaf.map _ ≫ X'.presheaf.map _) (f'.app B b) = _
      rw [← X'.presheaf.map_comp]
      congr 2
    · exact (smul_zero _).symm
  let ψ (p : ℕ) : (K.X (p : ℤ)).presheaf ⟶
      ((Modules.pushforward f').obj (D.X p)).presheaf :=
    { app := fun B ↦ AddCommGrpCat.ofHom (v p B.unop)
      naturality := by
        intro B C i
        ext s
        exact hvn p i.unop s }
  let q₀ (p : ℕ) : K.X (p : ℤ) ⟶ (Modules.pushforward f').obj (D.X p) :=
    ⟨PresheafOfModules.homMk (ψ p) (fun B ↦ hvl p B.unop)⟩
  let E (p : ℕ) := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  refine ⟨fun p ↦ q₀ p ≫ (E p).inv, ?_⟩
  intro p B s y
  change (((q₀ p ≫ (E p).inv ≫ (E p).hom).app B) s |>
    fun x ↦ (((e p).hom ≫ Pi.π (F p) y).app (op (f' ⁻¹ᵁ B))) x) = _
  simp only [Iso.inv_hom_id, Category.comp_id]
  exact (hV p (f' ⁻¹ᵁ B) (v p B s) y).symm.trans (hv p B s y)


private theorem filtered_signed_extension (X : Scheme.{u}) {I : Type*} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ)
    (a : ∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1)))
    (t : Fin (p + 1) → I) :
    (∑ σ : Equiv.Perm (Fin (p + 1)),
      if h : StrictMono (t ∘ σ) then
        (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (a ⟨t ∘ σ, h⟩)
      else 0) = signedCechExtension X U F S p a t := by
  classical
  change _ = signedCechExtensionValue X U F S p a t
  by_cases ht : Function.Injective t
  · have hm : StrictMono (t ∘ Tuple.sort t) :=
      (Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)
    rw [signedCechExtensionValue, dite_eq_left ht]
    rw [Finset.sum_eq_single (Tuple.sort t)]
    · simp only [dite_eq_left hm]
    · intro σ _ hσ
      have hn : ¬ StrictMono (t ∘ σ) := by
        intro h
        apply hσ
        apply Equiv.ext
        intro i
        apply ht
        exact congrFun (Tuple.unique_monotone h.monotone (Tuple.monotone_sort t)) i
      simp only [dite_eq_right hn]
    · simp
  · rw [signedCechExtensionValue, dite_eq_right ht]
    apply Finset.sum_eq_zero
    intro σ _
    have hn : ¬ StrictMono (t ∘ σ) := by
      intro h
      apply ht
      intro a b hab
      have he := h.injective (show (t ∘ σ) (σ.symm a) = (t ∘ σ) (σ.symm b) by
        simpa using hab)
      simpa using congrArg σ he
    simp only [dite_eq_right hn]

/-- The intersection model on the base open B.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-module-signed-section). -/
private noncomputable def naturalCechSectionSite {X : Scheme.{u}} {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) :
    SiteCechComplex (fun i : Fin r ↦ W ⟨i⟩ ⊓ B)
      (fun i ↦ homOfLE (le_top : W ⟨i⟩ ⊓ B ≤ ⊤)) where
  W p t := (⨅ k : Fin (p + 1), W ⟨t k⟩) ⊓ B
  pr p t k := homOfLE (inf_le_inf (iInf_le _ k) le_rfl)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_inf (le_iInf fun k ↦ (a k).le.trans inf_le_left)
      ((a 0).le.trans inf_le_right)), ?_, ?_⟩
    · intro k; exact Subsingleton.elim _ _
    · intro b _; exact Subsingleton.elim _ _
  W_zero := by intro t; simp
  pr_zero := by intro t; exact Subsingleton.elim _ _
  indexMap t α := homOfLE (inf_le_inf (le_iInf fun k ↦ iInf_le _ (α k)) le_rfl)
  indexMap_pr _ _ _ := Subsingleton.elim _ _

/-- Restriction from the chosen product to the intersection model.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-module-signed-section). -/
private noncomputable def naturalCechSectionMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    (naturalCechSectionSite W B).W p t ⟶ (∏ᶜ fun k ↦ W ⟨t k⟩) ⨯ B :=
  prod.lift (Pi.lift fun k ↦ homOfLE (inf_le_left.trans (iInf_le _ k)))
    (homOfLE inf_le_right)

private theorem naturalCechSectionMap_isIso {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    IsIso (naturalCechSectionMap W B t) := by
  apply (PartialOrder.isIso_iff_eq _).mpr
  apply le_antisymm (naturalCechSectionMap W B t).le
  exact le_inf (le_iInf fun k ↦
    (prod.fst ≫ Pi.π (fun l ↦ W ⟨t l⟩) k).le) prod.snd.le

/-- All tuple coordinates, transported by actual restriction maps.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-module-signed-section). -/
private noncomputable def naturalCechSectionCochain {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    (naturalCechSectionSite W B).cochains M.presheaf p :=
  fun t ↦ M.presheaf.map (naturalCechSectionMap W B t).op
    (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t k⟩) s)

private theorem naturalCechSectionCochain_injective {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) :
    Function.Injective (naturalCechSectionCochain M W D e p B) := by
  intro s z h
  apply (ConcreteCategory.bijective_of_isIso ((e p).hom.app (op B))).injective
  apply Concrete.isLimit_ext _
    (isLimitOfPreserves ((evaluation _ _).obj (op B))
      (limit.isLimit (Discrete.functor (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
            (op (∏ᶜ fun k ↦ W (y k)))))))
  intro y
  let t : Fin (p + 1) → Fin r := fun k ↦ (y.as k).down
  have ht := congrFun h t
  have : IsIso (naturalCechSectionMap W B t) := naturalCechSectionMap_isIso W B t
  apply (ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (naturalCechSectionMap W B t).op)).injective
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate transport identifies the given differential with the alternating face sum.
Source: Stacks 01FJ, the Čech differential, and 01FK, restriction to ordered tuples.
(blueprint: lem-pc-ordered-cech-module-signed-section).

Proof: Compose hd with the projection to a full tuple and evaluate at B and s.
The Mathlib Čech differential is the sum of signed coface maps. Its j-th coface,
after projecting to t, first projects to t composed with j.succAbove and then
restricts along the map of chosen products dropping the j-th factor, times the
identity of B. Restrict further along naturalCechSectionMap. The resulting arrow
from the intersection for t to the chosen product for its j-th face equals the
composite through the face intersection, since the category of opens is thin.
Functoriality identifies the corresponding restrictions. Additivity of restriction
moves it through the finite sum and the integer coefficients. This gives exactly
the defining alternating sum for naturalCechSectionSite. For an empty index set
there are no tuples; no nonempty intersection or affine hypothesis is required. -/
private theorem naturalCechSectionCochain_differential {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
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
    naturalCechSectionCochain M W D e (p + 1) B ((D.d p (p + 1)).app B s) =
      (naturalCechSectionSite W B).differentialValue M.presheaf p
        (naturalCechSectionCochain M W D e p B s) := by
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
  unfold naturalCechSectionCochain
  rw [h]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, NatTrans.app_sum, NatTrans.app_zsmul,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  unfold SiteCechComplex.differentialValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s) =
    (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s)
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

/-- A graded signed extension commutes with adjacent differentials.
Source: Stacks 01FJ and 01FK, signed extension is a cochain map.
(blueprint: lem-pc-ordered-cech-module-signed-section).

Proof: Fix p and a base open B. Identify the chosen products times the inverse
image of B with the infima of the opens W_i intersected with that inverse image.
Apply e and all tuple projections. The full-coordinate hypothesis identifies
q with the signed extension of the a-coordinates: for an injective tuple the
unique increasing permutation is its sorting permutation; for repeated tuples
all summands are zero. The identity hd, composed with each tuple projection,
identifies D's differential with the sum of signed face restrictions. The maps
from chosen products to intersections commute with face maps because opens form
a poset. Apply signedCechExtension_differential to these sectionwise cochains.
On an increasing tuple, every face is increasing, and signed extension recovers
the original coordinate. Thus ha identifies the increasing coordinates of the
differential with the a-coordinates of d_K. Their signed extensions agree on
all tuples. Invert the product-intersection isomorphisms and use injectivity of
e and of the extension isomorphism to get equality on sections. Module-sheaf
extensionality gives the displayed equation. This argument uses neither local
linearity hypotheses nor negative-degree vanishing, and works for empty covers,
repeated tuples, empty intersections and zero coefficient modules. -/
private theorem orderedCech_signedDegree_comm {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ)
    (a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)))
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
    (q : ∀ p : ℕ, K.X (p : ℤ) ⟶
      (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).X (p : ℤ)))
    (hq : IsOrderedCechSignedSection f' M W₀ K a D e q) (p : ℕ) :
    q p ≫ (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).d (p : ℤ) ((p + 1 : ℕ) : ℤ)) =
    K.d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫ q (p + 1) := by
  classical
  let E (p : ℕ) := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  have hqs (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B)) :
      naturalCechSectionCochain M W₀ D e p (f' ⁻¹ᵁ B)
        ((E p).hom.app B ((q p).app B s)) =
      signedCechExtension X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ f' ⁻¹ᵁ B) M.presheaf
        (naturalCechSectionSite W₀ (f' ⁻¹ᵁ B)) p
        (fun t ↦ a p B s (OrderEmbedding.ofStrictMono t.1 t.2)) := by
    funext t
    rw [← filtered_signed_extension]
    unfold naturalCechSectionCochain orderedCechNaturalCoordinate
    rw [hq p B s (fun l ↦ ⟨t l⟩)]
    unfold orderedCechSignedSectionValue
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs with h h'
    · rw [map_zsmul]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _)
        (a p B s (OrderEmbedding.ofStrictMono (t ∘ σ) h)) = _
      rw [← M.presheaf.map_comp]
      congr 2
    · exact False.elim (h' h)
    · rename_i h'
      exact False.elim (h h')
    · simp only [map_zero]
  have has (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
      (t : {t : Fin (p + 2) → Fin r // StrictMono t}) :
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s)
        (OrderEmbedding.ofStrictMono t.1 t.2) =
      (naturalCechSectionSite W₀ (f' ⁻¹ᵁ B)).differentialValue M.presheaf p
        (signedCechExtension X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ f' ⁻¹ᵁ B) M.presheaf
          (naturalCechSectionSite W₀ (f' ⁻¹ᵁ B)) p
          (fun t ↦ a p B s (OrderEmbedding.ofStrictMono t.1 t.2))) t.1 := by
    rw [ha]
    unfold SiteCechComplex.differentialValue
    apply Finset.sum_congr rfl
    intro j _
    rw [signedCechExtension_increasing X' _ _ _ p _
      ⟨t.1 ∘ j.succAbove, t.2.comp j.strictMono_succAbove⟩]
    rfl
  let L := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
    ComplexShape.embeddingUpNat
  have hEd : L.d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫ (E (p + 1)).hom =
      (E p).hom ≫ (Modules.pushforward f').map (D.d p (p + 1)) := by
    dsimp only [L, E]
    erw [HomologicalComplex.extend_d_eq _ _ (i := p) (j := p + 1) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  apply Modules.hom_ext
  intro B
  ext s
  apply (ConcreteCategory.bijective_of_isIso ((E (p + 1)).hom.app B)).injective
  apply naturalCechSectionCochain_injective M W₀ D e (p + 1) (f' ⁻¹ᵁ B)
  change naturalCechSectionCochain M W₀ D e (p + 1) (f' ⁻¹ᵁ B)
      ((E (p + 1)).hom.app B
        ((L.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B ((q p).app B s))) =
    naturalCechSectionCochain M W₀ D e (p + 1) (f' ⁻¹ᵁ B)
      ((E (p + 1)).hom.app B ((q (p + 1)).app B
        ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s)))
  have hEval := congrArg (fun v ↦ v.app B ((q p).app B s)) hEd
  change (E (p + 1)).hom.app B
      ((L.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B ((q p).app B s)) =
    (D.d p (p + 1)).app (f' ⁻¹ᵁ B) ((E p).hom.app B ((q p).app B s)) at hEval
  rw [hEval, naturalCechSectionCochain_differential M W₀ D e hd, hqs, hqs,
    signedCechExtension_differential]
  congr 1
  funext t
  exact (has B s t).symm


/-- Signed extension lifts ordered coordinates to a morphism of module complexes.
Source: Stacks Project, Tags 01FJ and 01FK, signed extension of ordered cochains.
(blueprint: lem-pc-ordered-cech-module-signed-section).

Proof: Apply a to a section of K. For each all-tuple coordinate, put zero if the
tuple has a repeated index. Otherwise sort it increasingly, take the coordinate
at the sorted tuple and multiply by the sorting sign. Transport from the
intersection to the chosen product of opens by the inverse of its canonical
isomorphism, and use the inverse of e to get a section of D. Naturality of a and
e makes this construction commute with restrictions. The local scalar formulas
hl and hlinear make it linear over the base open's ring: restriction is semilinear,
and integer signs commute with scalars. Injectivity of e and its coordinate maps
verifies these claims after transporting back to all-tuple coordinates. For the
chain equation, use ha and hd to identify both differentials with their face sums.
The signedCechExtension_differential identity proves the result: distinct tuples
obey the sorting-sign identity, while faces of repeated tuples cancel in pairs.
In increasing coordinates the sorting permutation is the identity, proving the
displayed formula. Extend to negative degrees by zero; hK makes every chain
condition there and across -1 automatic. Empty families and zero modules are
covered by the same formulas. -/
theorem orderedCech_module_signedSection {X' T' : Scheme.{u}} (f' : X' ⟶ T')
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
    ∃ imap : K ⟶ ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat),
      ∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 1) ↪o Fin r),
        orderedCechModuleCoordinate f' M W₀ D e p B t
          ((imap.f (p : ℤ)).app B s) = a p B s t := by
  classical
  obtain ⟨q, hq⟩ := orderedCech_signedDegree_exists f' M W₀ K a hn hl D e hlinear
  let L := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
    ComplexShape.embeddingUpNat
  let : K.IsStrictlyGE 0 := hK
  let g (n : ℤ) : K.X n ⟶ L.X n :=
    if h : 0 ≤ n then
      eqToHom (congrArg K.X (Int.toNat_of_nonneg h).symm) ≫ q n.toNat ≫
        eqToHom (congrArg L.X (Int.toNat_of_nonneg h))
    else 0
  have hg (p : ℕ) : g (p : ℤ) = q p := by simp [g]
  let imap : K ⟶ L :=
    { f := g
      comm' := by
        intro n m hnm
        by_cases hn' : 0 ≤ n
        · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn'
          have hm : m = ((p + 1 : ℕ) : ℤ) := by
            change (p : ℤ) + 1 = m at hnm
            omega
          subst m
          change g (p : ℤ) ≫ L.d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
            K.d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫ g ((p + 1 : ℕ) : ℤ)
          rw [hg, hg]
          exact orderedCech_signedDegree_comm f' M W₀ K a ha D e hd q hq p
        · exact (K.isZero_of_isStrictlyGE 0 n (by omega)).eq_of_src _ _ }
  refine ⟨imap, ?_⟩
  intro p B s t
  change orderedCechModuleCoordinate f' M W₀ D e p B t ((g (p : ℤ)).app B s) = _
  rw [hg]
  unfold orderedCechModuleCoordinate
  rw [hq p B s (fun l ↦ ⟨t l⟩)]
  exact orderedCechSignedSectionValue_increasing f' M W₀ p B (a p B s) t

end AlgebraicGeometry.Scheme.Modules
