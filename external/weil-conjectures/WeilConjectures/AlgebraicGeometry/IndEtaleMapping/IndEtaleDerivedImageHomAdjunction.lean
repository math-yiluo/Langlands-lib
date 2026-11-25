/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomComp

/-! # Global Hom and the derived direct-image adjunction

The isomorphisms retain the evaluation normalization of restriction. There is no
continuity assertion and no choice of mapping-complex representatives here.
Source: Bhatt--Scholze 6.3.16, adjunction step
(blueprint: lem-per-ind-etale-derived-image-hom-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- Naturality of a conjugate global-Hom comparison, in abstract form. All functors are
variables, so that the coherence computation happens with opaque functors.
The hypotheses are the counit normalizations of the comparisons, naturality of the
target counits, and compatibility of the left-adjoint comparisons with composition.
The coefficient variance `γ` of the target global Hom is a variable: when the lemma is
applied, `γ` matches the goal syntactically, so the kernel never compares `NatTrans.app` of
two definitionally equal but distinct transformations, which it does by unfolding the
derived functors. -/
private theorem homIso_naturality_of_counit
    {B DX DS DT : Type*} [Category* B] [Category* DX] [Category* DS] [Category* DT]
    [MonoidalCategory DX] [MonoidalCategory DS] [MonoidalCategory DT]
    {cX : B ⥤ DX} {cS : B ⥤ DS} {cT : B ⥤ DT}
    {GX : DXᵒᵖ ⥤ DX ⥤ B} {GS : DSᵒᵖ ⥤ DS ⥤ B} {GT : DTᵒᵖ ⥤ DT ⥤ B}
    (aX : ∀ E : DX, cX ⋙ tensorLeft E ⊣ GX.obj (op E))
    (aS : ∀ E : DS, cS ⋙ tensorLeft E ⊣ GS.obj (op E))
    (aT : ∀ E : DT, cT ⋙ tensorLeft E ⊣ GT.obj (op E))
    {ps : DX ⥤ DS} {ss : DS ⥤ DX} {pt : DX ⥤ DT} {st : DT ⥤ DX} {pq : DS ⥤ DT}
    (adjS : ps ⊣ ss) (adjT : pt ⊣ st) (c : pt ≅ ps ⋙ pq) (K M : DX)
    (τT : cT ⋙ tensorLeft (pt.obj K) ≅ (cX ⋙ tensorLeft K) ⋙ pt)
    (τS : cS ⋙ tensorLeft (ps.obj K) ≅ (cX ⋙ tensorLeft K) ⋙ ps)
    (τq : cT ⋙ tensorLeft (pq.obj (ps.obj K)) ≅ (cS ⋙ tensorLeft (ps.obj K)) ⋙ pq)
    (iT : (GX.obj (op K)).obj (st.obj (pt.obj M)) ⟶ (GT.obj (op (pt.obj K))).obj (pt.obj M))
    (iS : (GX.obj (op K)).obj (ss.obj (ps.obj M)) ⟶ (GS.obj (op (ps.obj K))).obj (ps.obj M))
    (R : (GS.obj (op (ps.obj K))).obj (ps.obj M) ⟶
      (GT.obj (op (pq.obj (ps.obj K)))).obj (pq.obj (ps.obj M)))
    (γ : GT.obj (op ((ps ⋙ pq).obj K)) ⟶ GT.obj (op (pt.obj K)))
    (hγ : γ = GT.map (c.hom.app K).op)
    (hT : (cT ⋙ tensorLeft (pt.obj K)).map iT ≫ (aT (pt.obj K)).counit.app (pt.obj M) =
      τT.hom.app ((GX.obj (op K)).obj (st.obj (pt.obj M))) ≫
        ((aX K).comp adjT).counit.app (pt.obj M))
    (hS : (cS ⋙ tensorLeft (ps.obj K)).map iS ≫ (aS (ps.obj K)).counit.app (ps.obj M) =
      τS.hom.app ((GX.obj (op K)).obj (ss.obj (ps.obj M))) ≫
        ((aX K).comp adjS).counit.app (ps.obj M))
    (hR : (cT ⋙ tensorLeft (pq.obj (ps.obj K))).map R ≫
        (aT (pq.obj (ps.obj K))).counit.app (pq.obj (ps.obj M)) =
      τq.hom.app ((GS.obj (op (ps.obj K))).obj (ps.obj M)) ≫
        pq.map ((aS (ps.obj K)).counit.app (ps.obj M)))
    (hG : ∀ {E E' N N' : DT} (f : E' ⟶ E) (g : N ⟶ N'),
      (cT ⋙ tensorLeft E').map ((GT.map f.op).app N ≫ (GT.obj (op E')).map g) ≫
          (aT E').counit.app N' =
        (f ▷ cT.obj ((GT.obj (op E)).obj N)) ≫ (aT E).counit.app N ≫ g)
    (hτ : ∀ Q : B, τT.hom.app Q ≫ c.hom.app (K ⊗ cX.obj Q) =
      (c.hom.app K ▷ cT.obj Q) ≫ τq.hom.app Q ≫ pq.map (τS.hom.app Q)) :
    (GX.obj (op K)).map ((adjT.homEquiv _ _) (c.hom.app (ss.obj (ps.obj M)) ≫
        pq.map (adjS.counit.app (ps.obj M)) ≫ c.inv.app M)) ≫ iT =
      iS ≫ R ≫ γ.app (pq.obj (ps.obj M)) ≫
        (GT.obj (op (pt.obj K))).map (c.inv.app M) := by
  subst hγ
  let Q₀ := (GX.obj (op K)).obj (ss.obj (ps.obj M))
  let W := τT.hom.app Q₀ ≫ c.hom.app (K ⊗ cX.obj Q₀) ≫
    pq.map (ps.map ((aX K).counit.app (ss.obj (ps.obj M)))) ≫
    pq.map (adjS.counit.app (ps.obj M)) ≫ c.inv.app M
  have hL : (cT ⋙ tensorLeft (pt.obj K)).map ((GX.obj (op K)).map ((adjT.homEquiv _ _)
      (c.hom.app (ss.obj (ps.obj M)) ≫ pq.map (adjS.counit.app (ps.obj M)) ≫ c.inv.app M)) ≫
        iT) ≫ (aT (pt.obj K)).counit.app (pt.obj M) = W := by
    rw [Functor.map_comp_assoc, hT, NatTrans.naturality_assoc, Adjunction.comp_counit_app,
      Functor.comp_map (cX ⋙ tensorLeft K) pt, ← Functor.map_comp_assoc,
      Adjunction.counit_naturality, Functor.map_comp_assoc]
    erw [← Adjunction.homEquiv_counit]
    erw [Equiv.symm_apply_apply]
    rw [NatTrans.naturality_assoc]
    rfl
  have hw {E E' : DT} (g : E' ⟶ E) {Q Q' : B} (h : Q ⟶ Q') {Z : DT}
      (k : E ⊗ cT.obj Q' ⟶ Z) :
      (cT ⋙ tensorLeft E').map h ≫ (g ▷ cT.obj Q') ≫ k =
        (g ▷ cT.obj Q) ≫ (cT ⋙ tensorLeft E).map h ≫ k :=
    whisker_exchange_assoc g (cT.map h) k
  have hR' : (cT ⋙ tensorLeft (pt.obj K)).map (iS ≫ R ≫
      (GT.map (c.hom.app K).op).app (pq.obj (ps.obj M)) ≫
        (GT.obj (op (pt.obj K))).map (c.inv.app M)) ≫
      (aT (pt.obj K)).counit.app (pt.obj M) = W := by
    rw [← Category.assoc iS, Functor.map_comp_assoc, hG]
    erw [hw]
    rw [Functor.map_comp_assoc]
    erw [reassoc_of% hR]
    rw [NatTrans.naturality_assoc, Functor.comp_map (cS ⋙ tensorLeft (ps.obj K)) pq,
      ← Functor.map_comp_assoc, hS, Adjunction.comp_counit_app]
    simp only [W, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hτ]
  apply ((aT (pt.obj K)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hL, hR']

/-- The global-Hom isomorphisms of derived adjunction are compatible with the
specified pullback-of-evaluation transition maps.

Source: Bhatt--Scholze 6.3.16, proof, adjunction; Stacks 08JA
(blueprint: lem-per-ind-etale-derived-image-hom-adjunction).

Proof: imageHomIso is the conjugate of the canonical monoidal and
constant-pullback comparisons under the global tensor-Hom and direct-image
adjunctions. To check naturality for f, apply these adjunction bijections. The
definition of imagePullback is pullback of the earlier
counit, while ExternalRHom.restriction is the transpose of pulled evaluation.
Naturality of the counit, the two triangle identities, and the constant and tensor
composition constraints identify the transposes. Inverse-image composition
then gives precisely the two displayed final normalization factors.
-/
theorem imageHomIso_naturality {T S : Over X} (f : T ⟶ S) :
    ((ExternalRHom.globalHom A X).obj (op K)).map (imagePullback A M f) ≫
      (imageHomIso A M K T).hom =
      (imageHomIso A M K S).hom ≫
        ExternalRHom.restriction A f.left
          ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
        ((ExternalRHom.globalHom A T.left).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
            f.w.symm).hom.app K).op).app
              ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
        ((ExternalRHom.globalHom A T.left).obj
          (op ((ExternalRHom.pull A T.hom).obj K))).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
              f.w.symm).inv.app M) :=
  homIso_naturality_of_counit (cX := ExternalRHom.constant A X)
    (cS := ExternalRHom.constant A S.left)
    (cT := ExternalRHom.constant A T.left) (GX := ExternalRHom.globalHom A X)
    (GS := ExternalRHom.globalHom A S.left) (GT := ExternalRHom.globalHom A T.left)
    (ps := ExternalRHom.pull A S.hom) (pt := ExternalRHom.pull A T.hom)
    (pq := ExternalRHom.pull A f.left)
    (ss := (lowerStar (ModuleCat.{u + 1} A) S.hom).rightDerivedFunctor)
    (st := (lowerStar (ModuleCat.{u + 1} A) T.hom).rightDerivedFunctor)
    (ExternalRHom.globalAdjunction A)
    (ExternalRHom.globalAdjunction A) (ExternalRHom.globalAdjunction A)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) S.hom)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom f.w.symm) K M
    (imageTensorIso A K T) (imageTensorIso A K S)
    (restrictTensorIso A f.left ((ExternalRHom.pull A S.hom).obj K))
    (imageHomIso A M K T).hom (imageHomIso A M K S).hom
    (ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M))
    _ rfl
    (imageHomIso_counit A K M T) (imageHomIso_counit A K M S)
    (restriction_counit A f.left _ _)
    (fun f g ↦ imageGlobalHom_counit_naturality A f g)
    (imageTensorIso_hom_app_comp A K f)

end AlgebraicGeometry.Etale.IndEtaleMapping
