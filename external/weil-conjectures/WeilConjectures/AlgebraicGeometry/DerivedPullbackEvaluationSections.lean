/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedTensorHomSectionsUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Sections of the normalized pointwise pullback evaluation

Source: Stacks Project, Cohomology, Tags 08I3, 079W, 08DJ and 08JA.
(blueprint: lem-pc-derived-pullback-evaluation-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem sectionsComparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive]
    (a : F ⊣ R) (m : F.CoreMonoidal)
    (QS : C ⥤ AddCommGrpCat) (QT : D ⥤ AddCommGrpCat)
    (γS : ∀ A, QS.obj A ≃+ (𝟙_ C ⟶ A))
    (γT : ∀ B, QT.obj B ≃+ (𝟙_ D ⟶ B))
    (hS : ∀ (A B : C) (f : A ⟶ B) (x : QS.obj A),
      γS B (QS.map f x) = γS A x ≫ f)
    (hT : ∀ (A B : D) (f : A ⟶ B) (x : QT.obj A),
      γT B (QT.map f x) = γT A x ≫ f) :
    ∃ z : R ⋙ QS ≅ QT,
      ∀ (A : C) (B : D) (d : F.obj A ⟶ B) (x : QS.obj A),
        γT B (z.hom.app B (QS.map (a.homEquiv A B d) x)) =
          m.εIso.hom ≫ F.map (γS A x) ≫ d := by
  let t (B : D) : (F.obj (𝟙_ C) ⟶ B) ≃+ (𝟙_ D ⟶ B) :=
    { toEquiv := Iso.homCongr m.εIso.symm (Iso.refl B)
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.comp_add] }
  let E (B : D) := (γS (R.obj B)).trans
    ((a.homAddEquiv (𝟙_ C) B).symm.trans ((t B).trans (γT B).symm))
  have hE (B : D) (x : QS.obj (R.obj B)) :
      γT B (E B x) = m.εIso.hom ≫ (a.homEquiv (𝟙_ C) B).symm (γS _ x) := by
    simp [E, t, Iso.homCongr]
  let z : R ⋙ QS ≅ QT := NatIso.ofComponents (fun B ↦ (E B).toAddCommGrpIso) (by
    intro B B' f
    ext x
    apply (γT B').injective
    change γT B' (E B' (QS.map (R.map f) x)) = γT B' (QT.map f (E B x))
    rw [hE, hT, hE, hS, a.homEquiv_naturality_right_symm]
    simp only [Category.assoc])
  refine ⟨z, ?_⟩
  intro A B d x
  change γT B (E B (QS.map (a.homEquiv A B d) x)) = _
  rw [hE, hS, a.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

private theorem evaluationPullback
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (m : F.CoreMonoidal)
    (HS : Cᵒᵖ × C ⥤ C) (HT : Dᵒᵖ × D ⥤ D)
    (qS : ∀ A K L, (A ⟶ HS.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (qT : ∀ A K L, (A ⟶ HT.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hS : ∀ (A A' K K' L L') (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ HS.obj (op K, L)),
      qS A' K' L' (a ≫ f ≫ HS.map (b.op, c)) = (a ⊗ₘ b) ≫ qS A K L f ≫ c)
    (hT : ∀ (A A' K K' L L') (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ HT.obj (op K, L)),
      qT A' K' L' (a ≫ f ≫ HT.map (b.op, c)) = (a ⊗ₘ b) ≫ qT A K L f ≫ c)
    (K L : C) (x : 𝟙_ C ⟶ HS.obj (op K, L)) :
    (λ_ (F.obj K)).inv ≫ qT _ (F.obj K) (F.obj L)
      (m.εIso.hom ≫ F.map x ≫
        (qT _ (F.obj K) (F.obj L)).symm
          ((m.μIso _ K).hom ≫ F.map (qS _ K L (𝟙 _)))) =
      F.map ((λ_ K).inv ≫ qS _ K L x) := by
  let := m.toMonoidal
  have hs := hS _ _ K K L L x (𝟙 K) (𝟙 L) (𝟙 _)
  have hiS : HS.map (show (op K, L) ⟶ (op K, L) from ((𝟙 K).op, 𝟙 L)) =
      𝟙 (HS.obj (op K, L)) := by
    simpa only [prod_id', ← op_id] using HS.map_id (op K, L)
  simp only [hiS, Category.comp_id] at hs
  have ht := hT _ _ (F.obj K) (F.obj K) (F.obj L) (F.obj L)
    (m.εIso.hom ≫ F.map x) (𝟙 _) (𝟙 _)
    ((qT _ (F.obj K) (F.obj L)).symm
      ((m.μIso _ K).hom ≫ F.map (qS _ K L (𝟙 _))))
  have hiT : HT.map (show (op (F.obj K), F.obj L) ⟶ (op (F.obj K), F.obj L) from
      ((𝟙 (F.obj K)).op, 𝟙 (F.obj L))) = 𝟙 (HT.obj (op (F.obj K), F.obj L)) := by
    simpa only [prod_id', ← op_id] using HT.map_id (op (F.obj K), F.obj L)
  simp only [hiT, Category.comp_id, Equiv.apply_symm_apply, Category.assoc] at ht
  rw [ht]
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [m.μIso_hom_natural_left_assoc]
  have hu : (λ_ (F.obj K)).inv ≫ m.εIso.hom ▷ F.obj K ≫
      (m.μIso (𝟙_ C) K).hom = F.map (λ_ K).inv :=
    Functor.LaxMonoidal.left_unitality_inv F K
  rw [← Category.assoc] at hu
  rw [← Category.assoc, ← Category.assoc, hu]
  rw [hs]
  simp only [tensorHom_id, Functor.map_comp]

private theorem evaluationSectionsFromUnits
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [R.Additive] (ha : Nonempty (F ⊣ R))
    (m : F.CoreMonoidal)
    (HS : Cᵒᵖ × C ⥤ C) (HT : Dᵒᵖ × D ⥤ D)
    (QS : C ⥤ AddCommGrpCat) (QT : D ⥤ AddCommGrpCat)
    (qS : ∀ A K L, (A ⟶ HS.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (qT : ∀ A K L, (A ⟶ HT.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hS : ∀ (A A' K K' L L') (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ HS.obj (op K, L)),
      qS A' K' L' (a ≫ f ≫ HS.map (b.op, c)) = (a ⊗ₘ b) ≫ qS A K L f ≫ c)
    (hT : ∀ (A A' K K' L L') (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ HT.obj (op K, L)),
      qT A' K' L' (a ≫ f ≫ HT.map (b.op, c)) = (a ⊗ₘ b) ≫ qT A K L f ≫ c)
    (bS :
    ∃ (γ : ∀ A : C,
        QS.obj A ≃+ (𝟙_ (C) ⟶ A))
      (e : ∀ P : Cᵒᵖ × C,
        QS.obj
          (HS.obj P) ≃+ (P.1.unop ⟶ P.2)),
      (∀ (A B : C) (f : A ⟶ B)
          (x : QS.obj A),
        γ B (QS.map f x) = γ A x ≫ f) ∧
      (∀ (P P' : Cᵒᵖ × C) (f : P ⟶ P')
          (x : QS.obj
              (HS.obj P)),
        e P' (QS.map
            (HS.map f) x) = f.1.unop ≫ e P x ≫ f.2) ∧
      (∀ (K L : C)
          (x : QS.obj
              (HS.obj (op K, L))),
        e (op K, L) x = (λ_ K).inv ≫ qS _ K L (γ _ x)))
    (bT :
    ∃ (γ : ∀ A : D,
        QT.obj A ≃+ (𝟙_ (D) ⟶ A))
      (e : ∀ P : Dᵒᵖ × D,
        QT.obj
          (HT.obj P) ≃+ (P.1.unop ⟶ P.2)),
      (∀ (A B : D) (f : A ⟶ B)
          (x : QT.obj A),
        γ B (QT.map f x) = γ A x ≫ f) ∧
      (∀ (P P' : Dᵒᵖ × D) (f : P ⟶ P')
          (x : QT.obj
              (HT.obj P)),
        e P' (QT.map
            (HT.map f) x) = f.1.unop ≫ e P x ≫ f.2) ∧
      (∀ (K L : D)
          (x : QT.obj
              (HT.obj (op K, L))),
        e (op K, L) x = (λ_ K).inv ≫ qT _ K L (γ _ x))) :
    ∃ (a : F ⊣ R)
      (z : R ⋙
          QS ≅
        QT)
      (eS : ∀ P : Cᵒᵖ × C,
        QS.obj
          (HS.obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : Dᵒᵖ × D,
        QT.obj
          (HT.obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : Cᵒᵖ × C) (f : P ⟶ P')
          (x : QS.obj
            (HS.obj P)),
        eS P' (QS.map
              (HS.map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : Dᵒᵖ × D) (f : P ⟶ P')
          (x : QT.obj
            (HT.obj P)),
        eT P' (QT.map
              (HT.map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ (K L : C)
          (x : QS.obj
            (HS.obj (op K, L))),
        eT (op (F.obj K), F.obj L)
          ((z.hom.app
              (HT.obj
                  (op (F.obj K), F.obj L)))
            (QS.map
              (a.homEquiv _ _
                ((qT _ (F.obj K) (F.obj L)).symm
                  ((m.μIso _ K).hom ≫
                    F.map (qS _ K L (𝟙 _))))) x)) =
          F.map (eS (op K, L) x)) := by
  obtain ⟨a⟩ := ha
  have : F.Additive := a.left_adjoint_additive
  obtain ⟨γS, eS, hγS, heS, hnS⟩ := bS
  obtain ⟨γT, eT, hγT, heT, hnT⟩ := bT
  obtain ⟨z, hz⟩ := sectionsComparison F R a m QS QT γS γT hγS hγT
  refine ⟨a, z, eS, eT, heS, heT, ?_⟩
  intro K L x
  rw [hnT, hz, hnS]
  exact evaluationPullback F m HS HT qS qT hS hT K L (γS _ x)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 2048 in
-- The derived tensor instances are repeated in the equivalences and comparisons.
/-- The pointwise transpose of pulled-back evaluation respects the canonical
identification of zeroth hypercohomology with derived morphisms.
This is a statement about elements, with no bifunctorial mate and no counit composite.

Source: Stacks Project, Cohomology, Remark 08I3, Lemma 079W, Lemma 08DJ and Tag 08JA.
(blueprint: lem-pc-derived-pullback-evaluation-sections).

Proof:
1. Extract the termwise tensor pullback and its left-derived comparison from the
   given monoidal model. Derive its underived pullback/direct-image adjunction on
   K-flat source and K-injective target complexes. Transport the left side by the
   model's left-derived comparison. This supplies a, normalized to that comparison.
2. Compute direct image and global sections on K-injective resolutions. Sections
   of direct image are sections on the source, giving z after zeroth cohomology.
   Identify H0 of the Hom complex with chain maps modulo homotopies, then with
   derived morphisms into the fixed K-injective resolution. These give eS and eT;
   composition of representatives proves both displayed naturality identities.
3. Resolve K and L by K-flat complexes and the target by the fixed K-injective
   resolution. The canonical tensor-Hom predicates identify evaluation with
   componentwise uncurrying. The monoidal-model predicate identifies its tensorator
   with termwise pullback on every total-tensor summand. Transposing evaluation
   after this tensorator and taking its adjoint therefore sends a degree-zero
   Hom cocycle phi to its termwise pullback. The z comparison removes direct image
   without changing that cocycle. Passing to homotopy classes gives the last
   identity. Common resolutions transport this identity to arbitrary K and L.
   No invertibility of an internal-Hom/counit composite is used. For an identity
   morphism the computation is the identity on cocycles; for zero objects or the
   empty scheme both sides are the zero morphism. -/
theorem exists_derivedPullback_evaluation_sections
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal)
    (qS : ∀ A K L : schemeDerivedCategory S,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology S)
        S.toRingedSpace.sheaf).obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hqS : IsCanonicalDerivedTensorHom S qS)
    (qT : ∀ A K L : schemeDerivedCategory T,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology T)
        T.toRingedSpace.sheaf).obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hqT : IsCanonicalDerivedTensorHom T qT) :
    ∃ (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (z : schemeDerivedDirectImage g ⋙
          ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf ≅
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)
      (eS : ∀ P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P)),
        eS P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P)),
        eT P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ (K L : schemeDerivedCategory S)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))),
        eT (op ((derivedPullback g).obj K), (derivedPullback g).obj L)
          ((z.hom.app
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).obj
                  (op ((derivedPullback g).obj K), (derivedPullback g).obj L)))
            ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).map
              (a.homEquiv _ _
                ((qT _ ((derivedPullback g).obj K) ((derivedPullback g).obj L)).symm
                  ((m.μIso _ K).hom ≫
                    (derivedPullback g).map (qS _ K L (𝟙 _))))) x)) =
          (derivedPullback g).map (eS (op K, L) x)) := by
  have : (schemeDerivedDirectImage g).Additive := by
    dsimp [schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage]
    infer_instance
  exact evaluationSectionsFromUnits (derivedPullback g) (schemeDerivedDirectImage g)
    (nonempty_derivedPullbackAdjunction.{u, w} g) m _ _ _ _ qS qT hqS.1 hqT.1
    (exists_derivedTensorHom_sections_unit.{u, w} S qS hqS)
    (exists_derivedTensorHom_sections_unit.{u, w} T qT hqT)

end AlgebraicGeometry
