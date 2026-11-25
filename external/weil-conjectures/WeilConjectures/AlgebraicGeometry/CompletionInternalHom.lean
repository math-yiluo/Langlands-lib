/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomSectionsLift
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotient

/-! # Internal Hom and coherent formal completion

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.5, Tag 0882
(blueprint: lem-weil-pbc-completion-internal-hom).

The inverse limit is written as compatible families of global sections. The existential
maps are specified by quotient factorization and by their components, so the bijection
is the canonical map in the node, rather than an unspecified equivalence of sets.
As in `formalCompletionSystem`, `op n` denotes the positive level `n + 1`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem homObjSectionsEquiv_map {X : Scheme.{u}}
    {M N M' N' : X.Modules} (f : M' ⟶ M) (g : N ⟶ N')
    (s : (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) M N).sections) :
    SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf) M' N'
        (SheafOfModules.sectionsMap
          (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf) f g) s) =
      f ≫ SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf) M N s ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from completed global internal Hom to morphisms of completions is
bijective. The first two clauses express annihilation and unique local factorization.
The maps `e` factor postcomposition with the quotient projection through both quotients;
the next clause expresses compatibility with every transition. Finally `Φ` has components
obtained by taking sections of `e` and the global internal-Hom identification.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.5, Tag 0882
(blueprint: lem-weil-pbc-completion-internal-hom).

Proof (the node's five steps):
1. Ideal products are locally sums of products of ideal sections with module sections
   (def-weil-pbc-coherent-formal-module, def-pur-sheaf-tensor-product). Since I^n kills
   F/I^n F, every local map G → F/I^n F kills I^n G. Postcomposition with the quotient
   kills I^n Hom(G,F), giving e_n by the two cokernel properties. Restriction and reduction
   commute with these factorizations by uniqueness; this defines Φ on compatible families.
2. On an affine open U = Spec A, A is Noetherian (pqf-lem-affine-open-locnoeth).
   Coherent F and G correspond to finite modules M and N, and Hom(G,F) to Hom_A(N,M),
   by lem-weil-pbc-affine-tilde-gamma-adjunction, pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-quasi-coherent-finite-type-affine and
   lem-weil-pbc-coherent-sheaf-hom-coherent. Quotients and their maps on affine sections
   are module quotients (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
3. The equivalence lem-weil-pbc-coherent-formal-modules-affine identifies Φ_U with the
   map Hom_A(N,M)^ → Hom_{A^}(N^,M^) evaluating compatible reductions componentwise.
4. Completion of finite modules equals tensoring with A^ (three applications of
   lem-weil-pbc-completion-finite-module-tensor). A^ is flat over A
   (lem-weil-pbc-noetherian-completion-flat), so flat base change commutes with Hom from N
   (lem-weil-pbc-flat-base-change-hom-finitely-presented). These identifications agree
   with the specified map on generators 1 ⊗ h by naturality, hence Φ_U is bijective.
5. The affine opens form a basis. Injectivity holds by restriction to this basis.
   Local inverse images of any compatible morphism agree on affine subopens of overlaps
   by local injectivity, so glue at every level to global sections. Their compatibility
   and the required equality of morphisms hold locally and hence globally by the sheaf
   condition (situation-conventions, def-pur-sheaf-hom). -/
theorem completion_internal_hom_bijective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X) :
    (∀ n : ℕ,
      Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
          (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n + 1) F.obj) = 0) ∧
    (∀ n : ℕ, IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I (n + 1) G.obj)
      (𝟙 (formalModuleQuotient I (n + 1) F.obj)))) ∧
    ∃ e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj),
      (∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj)) ∧
      (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
        e a ≫ SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          (𝟙 (formalModuleQuotient I (a.unop + 1) G.obj))
          ((formalCompletionSystem I F.obj).map f) =
        (formalCompletionSystem I (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f ≫
          e b ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) ((formalCompletionSystem I G.obj).map f)
            (𝟙 (formalModuleQuotient I (b.unop + 1) F.obj))) ∧
      ∃ Φ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).sections //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            SheafOfModules.sectionsMap
              ((formalCompletionSystem I (SheafOfModules.homObj
                (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f)
              (s a) = s b} → ((completion X I).obj G ⟶ (completion X I).obj F),
        (∀ s n, (Φ s).hom.app n =
          SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
            (formalModuleQuotient I (n.unop + 1) G.obj)
            (formalModuleQuotient I (n.unop + 1) F.obj)
            (SheafOfModules.sectionsMap (e n) (s.val n))) ∧
        Function.Bijective Φ := by
  have hz (n : ℕ) := (completion_internal_hom_quotient I F.obj G.obj
    (n + 1) (n + 1) le_rfl).1
  have hi (n : ℕ) := (completion_internal_hom_quotient I F.obj G.obj
    (n + 1) (n + 1) le_rfl).2
  refine ⟨hz, hi, ?_⟩
  let e (n : ℕᵒᵖ) :=
    let q := SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I (n.unop + 1) G.obj)
      (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj))
    have : IsIso q := hi n.unop
    cokernel.desc (Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n.unop + 1)).2
      (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G.obj F.obj))
      (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj)) (hz n.unop) ≫ inv q
  have he (n : ℕᵒᵖ) :
      formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
        e n ≫ SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          (formalModuleQuotientπ I (n.unop + 1) G.obj)
          (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj) := by
    have := hi n.unop
    simp [e, formalModuleQuotientπ]
  have hπ (M : X.Modules) (a b : ℕᵒᵖ) (f : a ⟶ b) :
      formalModuleQuotientπ I (a.unop + 1) M ≫
        (formalCompletionSystem I M).map f =
      formalModuleQuotientπ I (b.unop + 1) M := by
    simp [formalCompletionSystem, formalModuleQuotientMap, formalModuleQuotientπ]
  have hc (a b : ℕᵒᵖ) (f : a ⟶ b) :
      e a ≫ SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 (formalModuleQuotient I (a.unop + 1) G.obj))
        ((formalCompletionSystem I F.obj).map f) =
      (formalCompletionSystem I (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f ≫
        e b ≫ SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          ((formalCompletionSystem I G.obj).map f)
          (𝟙 (formalModuleQuotient I (b.unop + 1) F.obj)) := by
    have := (completion_internal_hom_quotient I F.obj G.obj
      (a.unop + 1) (b.unop + 1) (Nat.succ_le_succ (leOfHom f.unop))).2
    apply (cancel_mono (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I (a.unop + 1) G.obj)
      (𝟙 (formalModuleQuotient I (b.unop + 1) F.obj)))).1
    apply coequalizer.hom_ext
    have hs :
        SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          (𝟙 (formalModuleQuotient I (a.unop + 1) G.obj))
          ((formalCompletionSystem I F.obj).map f) ≫
          SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
            (formalModuleQuotientπ I (a.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (b.unop + 1) F.obj)) =
        SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          (formalModuleQuotientπ I (a.unop + 1) G.obj)
          (𝟙 (formalModuleQuotient I (a.unop + 1) F.obj)) ≫
          SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
            (𝟙 G.obj) ((formalCompletionSystem I F.obj).map f) := by
      rfl
    have hea := congrArg (fun k ↦ k ≫ SheafOfModules.homObjMap
      (R := X.toRingedSpace.sheaf) (𝟙 G.obj)
      ((formalCompletionSystem I F.obj).map f)) (he a)
    simp only [Category.assoc] at hea
    simp only [Category.assoc]
    rw [hs]
    dsimp only [formalModuleQuotientπ] at hea
    erw [hea]
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id, hπ]
    dsimp only [formalModuleQuotientπ] at hπ he
    erw [hπ, ← Category.assoc, hπ, he]
  refine ⟨e, he, hc, ?_⟩
  let Φ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).sections //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            SheafOfModules.sectionsMap
              ((formalCompletionSystem I (SheafOfModules.homObj
                (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f)
              (s a) = s b} → ((completion X I).obj G ⟶ (completion X I).obj F) :=
    fun s ↦ ObjectProperty.homMk
    { app := fun n ↦ SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
        (formalModuleQuotient I (n.unop + 1) G.obj)
        (formalModuleQuotient I (n.unop + 1) F.obj)
        (SheafOfModules.sectionsMap (e n) (s.val n))
      naturality := by
        intro a b f
        have h := congrArg
          (fun k ↦ SheafOfModules.sectionsMap k (s.val a)) (hc a b f)
        have h' := congrArg
          (SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
            (formalModuleQuotient I (a.unop + 1) G.obj)
            (formalModuleQuotient I (b.unop + 1) F.obj)) h
        dsimp only [Scheme.Modules] at h'
        simp only [SheafOfModules.sectionsMap_comp, homObjSectionsEquiv_map,
          Category.id_comp, Category.comp_id, s.property] at h'
        exact h'.symm }
  refine ⟨Φ, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro s s' h
    obtain ⟨s₀, _, hu⟩ := completion_internal_hom_sections_lift I F G e he
      (fun n ↦ (Φ s).hom.app n) (fun a b f ↦ ((Φ s).hom.naturality f).symm)
    apply (hu s (fun _ ↦ rfl)).trans
    symm
    apply hu s'
    intro n
    exact congrArg (fun α ↦ α.hom.app n) h.symm
  · intro α
    obtain ⟨s, hs, _⟩ := completion_internal_hom_sections_lift I F G e he
      (fun n ↦ α.hom.app n) (fun a b f ↦ (α.hom.naturality f).symm)
    refine ⟨s, ?_⟩
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact hs n

end AlgebraicGeometry
