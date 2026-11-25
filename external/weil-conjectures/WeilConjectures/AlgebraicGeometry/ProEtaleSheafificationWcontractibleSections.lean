/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation

import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension

/-!
# Sheafification on weakly contractible affine objects

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1); RefactorInstruction,
proof of Lemma point-eval
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The sheafification unit for the point Kan presheaf is invertible on weakly
contractible affines, naturally in the affine and in the coefficient sheaf.
The compatibility equation specifies the Kan-induced map associated to a coefficient
sheaf morphism. All equations are in the coefficient category, so they respect its
operations. This is a packaging of the conclusion, not an additional hypothesis.

Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, proof of Lemma point-eval
(auxiliary; not a blueprint node). -/
def PointLanSheafificationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    [HasWeakSheafify (Scheme.ProEt.topology X) C] : Prop :=
  ∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
    (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P),
    (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension →
    ∀ (U : X.ProEt), IsAffine U.left → PointLanWeaklyContractible X U →
      IsIso ((toSheafify (Scheme.ProEt.topology X) P).app (op U)) ∧
      (∀ (V : X.ProEt), IsAffine V.left → PointLanWeaklyContractible X V →
        ∀ f : V ⟶ U,
          P.map f.op ≫ (toSheafify (Scheme.ProEt.topology X) P).app (op V) =
            (toSheafify (Scheme.ProEt.topology X) P).app (op U) ≫
              (sheafify (Scheme.ProEt.topology X) P).map f.op) ∧
      (∀ (G : Sheaf (coherentTopology Profinite.{u}) C) (Q : X.ProEtᵒᵖ ⥤ C)
        (θ : G.obj ⟶ (profiniteToProEtOf X).op ⋙ Q),
        (Functor.LeftExtension.mk Q θ).IsPointwiseLeftKanExtension →
        ∀ (α : F ⟶ G) (β : P ⟶ Q),
          η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op β = α.hom ≫ θ →
          β.app (op U) ≫ (toSheafify (Scheme.ProEt.topology X) Q).app (op U) =
            (toSheafify (Scheme.ProEt.topology X) P).app (op U) ≫
              (sheafifyMap (Scheme.ProEt.topology X) β).app (op U))

-- Refine by finite affine pieces, then replace each piece by the singleton cover of
-- exists_affine_contractible_extension (Stacks 0983, 098H, 0990). This avoids needing
-- weak contractibility of arbitrary affine opens or clopen summands.
open CategoryTheory.Limits Scheme in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_refinement_large (X : Scheme.{u}) (U : X.ProEt) (hU : IsAffine U.left)
    (S : Sieve U) (hS : S ∈ Scheme.ProEt.topology X U) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (W : I → X.ProEt) (f : ∀ i, W i ⟶ U),
      (∀ i, IsAffine (W i).left) ∧ (∀ i, PointLanWeaklyContractible X (W i)) ∧
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology X U ∧ ∀ i, S (f i) := by
  classical
  let _ := hU
  obtain ⟨P, hP, hPS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (Scheme.ProEt.mem_precoverage_iff.1 hP)
  have hmem (i : 𝒰.I₀) :
      P.map (Scheme.ProEt.forget X ⋙ CategoryTheory.Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  obtain ⟨𝒱, g, hfin, _⟩ := QuasiCompactCover.exists_hom.{u + 1, u} 𝒰
  choose D hD φ hcover hcontract using
    fun j : 𝒱.I₀ ↦ Scheme.ProEt.exists_affine_contractible_extension (𝒱.X j)
  let (j : 𝒱.I₀) : CommRing (D j) := hD j
  let p (j : 𝒱.I₀) := Spec.map (CommRingCat.ofHom (φ j))
  have hp (j : 𝒱.I₀) : WeaklyEtale (p j) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ (hcover j) (by exact ⟨⟩)
  have (j : 𝒱.I₀) : WeaklyEtale (𝒱.f j) := 𝒱.map_prop j
  let W (j : 𝒱.I₀) : X.ProEt := Scheme.ProEt.mk (p j ≫ 𝒱.f j ≫ U.hom)
  let f (j : 𝒱.I₀) : W j ⟶ U := MorphismProperty.Over.homMk (p j ≫ 𝒱.f j)
  refine ⟨𝒱.I₀, hfin, W, f, ?_, ?_, ?_, ?_⟩
  · intro j
    exact inferInstanceAs (IsAffine (Spec _))
  · intro j
    exact hcontract j X (p j ≫ 𝒱.f j ≫ U.hom)
  · let E (j : 𝒱.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (𝒱.X j)) :=
      .singleton (p j) (hcover j)
    let B := 𝒱.cover.ofQuasiCompactCover.bind E
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows W f).map
      (Scheme.ProEt.forget X ⋙ CategoryTheory.Over.forget X) ∈ proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    have heq : Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (f j).left) =
        B.presieve₀ := by
      funext V q
      apply propext
      change _ ↔ Presieve.ofArrows B.X B.f q
      constructor
      · rintro ⟨j⟩
        exact Presieve.ofArrows.mk (i := (⟨j, PUnit.unit⟩ : B.I₀))
      · rintro ⟨⟨j, k⟩⟩
        exact ⟨j⟩
    change Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (f j).left) ∈ _
    rw [heq]
    exact B.mem₀
  · intro j
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : (W j).left ⟶ (Z (g.s₀ j)).left :=
      p j ≫ g.h₀ j ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ j)).left = (f j).left := by
      change (p j ≫ g.h₀ j ≫ eqToHom (hZ _).symm) ≫ (a (g.s₀ j)).left =
        p j ≫ 𝒱.f j
      rw [ha']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [g.w₀]
      rfl
    have hf : f j = MorphismProperty.Over.homMk d (by
        calc
          d ≫ (Z (g.s₀ j)).hom = d ≫ (a (g.s₀ j)).left ≫ U.hom := by
            rw [MorphismProperty.Over.w]
          _ = (f j).left ≫ U.hom := by rw [← Category.assoc, hd]
          _ = (W j).hom := MorphismProperty.Over.w (f j)) ≫ a (g.s₀ j) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hf]
    exact S.downward_closed (hPS _ _ (ha _)) _

open CategoryTheory.Limits Scheme in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_refinement (X : Scheme.{u}) (U : X.ProEt) (hU : IsAffine U.left)
    (S : Sieve U) (hS : S ∈ Scheme.ProEt.topology X U) :
    ∃ (I : Type u) (_ : Finite I) (W : I → X.ProEt) (f : ∀ i, W i ⟶ U),
      (∀ i, IsAffine (W i).left) ∧ (∀ i, PointLanWeaklyContractible X (W i)) ∧
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology X U ∧ ∀ i, S (f i) := by
  obtain ⟨I, hI, W, f, ha, hw, hcov, hf⟩ := finite_refinement_large X U hU S hS
  let e : ULift.{u} (Fin (Nat.card I)) ≃ I :=
    Equiv.ulift.trans (Finite.equivFin I).symm
  refine ⟨_, inferInstance, W ∘ e, fun i ↦ f (e i), fun i ↦ ha (e i),
    fun i ↦ hw (e i), ?_, fun i ↦ hf (e i)⟩
  simpa only [Sieve.ofArrows, Presieve.ofArrows_comp_eq_of_surjective f e.surjective]
    using hcov

-- Subcanonicity and sheaf uniqueness make the map from the covering coproduct epi.
-- Lift the identity through this epi using exactly PointLanWeaklyContractible.
open CategoryTheory.Limits Scheme in
set_option backward.isDefEq.respectTransparency false in
private theorem split_refinement (X : Scheme.{u}) (U : X.ProEt) (hU : IsAffine U.left)
    (wU : PointLanWeaklyContractible X U)
    (S : Sieve U) (hS : S ∈ Scheme.ProEt.topology X U) :
    ∃ (I : Type u) (_ : Finite I) (W : I → X.ProEt) (c : Cofan W),
      (∀ i, IsAffine (W i).left) ∧ (∀ i, PointLanWeaklyContractible X (W i)) ∧
      Nonempty (IsColimit c) ∧
      (∀ H : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
        Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
          fun i ↦ H.obj.map (c.inj i).op t)) ∧
      ∃ (p : c.pt ⟶ U) (σ : U ⟶ c.pt), σ ≫ p = 𝟙 U ∧ ∀ i, S (c.inj i ≫ p) := by
  classical
  let J := Scheme.ProEt.topology X
  obtain ⟨I, hI, W, f, ha, hw, hcov, hf⟩ := finite_refinement X U hU S hS
  have hqc (i : I) : CompactSpace (W i).left := by let _ := ha i; infer_instance
  have hqs (i : I) : QuasiSeparatedSpace (W i).left := by let _ := ha i; infer_instance
  obtain ⟨V, ι, e, hι, _, _, _, ⟨hr⟩, _, hsec, _, _⟩ :=
    Scheme.ProEt.finite_coproduct_evaluation.{u, u, u + 1} X I W hqc hqs
  let c : Cofan W := Cofan.mk V ι
  let yon := J.uliftYoneda.{u + 1}
  have hc : IsColimit c := isColimitOfReflects yon
    ((Cofan.isColimitMapCoconeEquiv yon W c).symm hr)
  let p : V ⟶ U := Cofan.IsColimit.desc hc f
  have hfac (i : I) : ι i ≫ p = f i := Cofan.IsColimit.fac hc f i
  have hp : Epi (yon.map p) := by
    constructor
    intro H g h hgh
    apply J.uliftYonedaEquiv.injective
    have hH := (isSheaf_iff_isSheaf_of_type J H.obj).mp H.property
    apply (hH.isSeparated _ hcov).ext
    rintro Z k ⟨T, a, _, ⟨i⟩, rfl⟩
    rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply]
    congr 1
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    congr 1
    have heq := congrArg (fun q ↦ yon.map (ι i) ≫ q) hgh
    simpa only [← Category.assoc, ← Functor.map_comp, hfac] using heq
  obtain ⟨s, hs⟩ := wU (yon.obj V) (yon.obj U) (yon.map p) hp (ULift.up (𝟙 U))
  let σ : U ⟶ V := s.down
  have hσ : σ ≫ p = 𝟙 U := by
    exact congrArg ULift.down hs
  refine ⟨I, hI, W, c, ha, hw, ⟨hc⟩, hsec, p, σ, hσ, ?_⟩
  intro i
  change S (ι i ≫ p)
  rw [hfac]
  exact hf i

open CategoryTheory.Limits Scheme in
private theorem product_transfer (X : Scheme.{u})
    (C : Type w) [Category.{v} C] (P : X.ProEtᵒᵖ ⥤ C)
    (I : Type u) (W : I → X.ProEt) (U : X.ProEt) (f : ∀ i, W i ⟶ U)
    (hc : IsColimit (Cofan.mk U f))
    (he : ∃ c : Cofan W, Nonempty (IsColimit c) ∧
      Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op)))) :
    Nonempty (IsLimit (Fan.mk (P.obj (op U)) (fun i ↦ P.map (f i).op))) := by
  obtain ⟨c, ⟨hc'⟩, ⟨hp⟩⟩ := he
  let e : c.pt ≅ U := hc'.coconePointUniqueUpToIso hc
  refine ⟨hp.ofIsoLimit (Cone.ext (P.mapIso e.symm.op) ?_)⟩
  intro i
  dsimp
  rw [← P.map_comp]
  change P.map (c.inj i.as).op = P.map (f i.as ≫ e.inv).op
  rw [show f i.as ≫ e.inv = c.inj i.as from
    hc'.comp_coconePointUniqueUpToIso_inv hc i]

open CategoryTheory.Limits Scheme in
private theorem fan_bijective {I : Type u} {A : Type (u + 1)}
    {B : I → Type (u + 1)} (f : ∀ i, A ⟶ B i)
    (h : IsLimit (Fan.mk A f)) : Function.Bijective (fun x i ↦ f i x) := by
  constructor
  · intro x y hxy
    have hh : (↾fun _ : PUnit.{u + 2} ↦ x) = (↾fun _ ↦ y) := by
      apply Fan.IsLimit.hom_ext h
      intro i
      ext t
      exact congrFun hxy i
    exact ConcreteCategory.congr_hom hh PUnit.unit
  · intro x
    refine ⟨Fan.IsLimit.lift h (fun i ↦ ↾fun _ : PUnit.{u + 2} ↦ x i) PUnit.unit, ?_⟩
    funext i
    exact ConcreteCategory.congr_hom (Fan.IsLimit.fac h _ i) PUnit.unit

-- The local-bijection theorem applies in each concrete coefficient category.
-- Glue representatives on the covering coproduct and pull them back along its section.
open CategoryTheory.Limits Scheme in
set_option backward.isDefEq.respectTransparency false in
private theorem unit_iso_of_refinement (X : Scheme.{u})
    (C : Type w) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type (u + 1)}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [(forget C).ReflectsIsomorphisms] [PreservesFiniteLimits (forget C)]
    [HasWeakSheafify (Scheme.ProEt.topology X) C]
    [(Scheme.ProEt.topology X).HasSheafCompose (forget C)]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective C]
    (P : X.ProEtᵒᵖ ⥤ C) (U : X.ProEt) (hU : IsAffine U.left)
    (wU : PointLanWeaklyContractible X U)
    (hprod : ∀ (I : Type u) [Finite I] (W : I → X.ProEt),
      (∀ i, IsAffine (W i).left) → (∀ i, PointLanWeaklyContractible X (W i)) →
      ∃ c : Cofan W, Nonempty (IsColimit c) ∧
        Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op)))) :
    IsIso ((toSheafify (Scheme.ProEt.topology X) P).app (op U)) := by
  let J := Scheme.ProEt.topology X
  let η := toSheafify J P
  have hb (I : Type u) [Finite I] (W : I → X.ProEt) (c : Cofan W)
      (ha : ∀ i, IsAffine (W i).left) (hw : ∀ i, PointLanWeaklyContractible X (W i))
      (hc : IsColimit c) :
      Function.Bijective (fun x : CC (P.obj (op c.pt)) ↦
        fun i ↦ P.map (c.inj i).op x) := by
    obtain ⟨h⟩ := product_transfer X C P I W c.pt c.inj
      (hc.ofIsoColimit (Cocone.ext (Iso.refl _))) (hprod I W ha hw)
    exact fan_bijective (fun i ↦ (forget C).map (P.map (c.inj i).op))
      (Fan.isLimitMapConeEquiv (forget C) _ _ (isLimitOfPreserves (forget C) h))
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    obtain ⟨I, hI, W, c, ha, hw, ⟨hc⟩, _, p, σ, hσ, hf⟩ :=
      split_refinement X U hU wU _ (Presheaf.equalizerSieve_mem J η x y hxy)
    have heq : P.map p.op x = P.map p.op y := by
      apply (hb I W c ha hw hc).1
      funext i
      have hi : P.map (c.inj i ≫ p).op x = P.map (c.inj i ≫ p).op y := hf i
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hi
    have heq' := congrArg (fun t ↦ P.map σ.op t) heq
    have hcomp : P.map p.op ≫ P.map σ.op = 𝟙 (P.obj (op U)) := by
      rw [← Functor.map_comp, ← op_comp, hσ]
      exact P.map_id (op U)
    simpa only [← ConcreteCategory.comp_apply, hcomp, ConcreteCategory.id_apply] using heq'
  · intro t
    obtain ⟨I, hI, W, c, ha, hw, ⟨hc⟩, hsec, p, σ, hσ, hf⟩ :=
      split_refinement X U hU wU _ (Presheaf.imageSieve_mem J η t)
    choose x hx using hf
    obtain ⟨s, hs⟩ := (hb I W c ha hw hc).2 x
    have heq : η.app (op c.pt) s = (sheafify J P).map p.op t := by
      apply (hsec ((sheafCompose J (forget C)).obj ((presheafToSheaf J C).obj P))).1
      funext i
      change (sheafify J P).map (c.inj i).op (η.app (op c.pt) s) =
        (sheafify J P).map (c.inj i).op ((sheafify J P).map p.op t)
      have hs' : P.map (c.inj i).op s = x i := congrFun hs i
      rw [← NatTrans.naturality_apply, hs', hx i]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    refine ⟨P.map σ.op s, ?_⟩
    rw [NatTrans.naturality_apply, heq]
    change (sheafify J P).map σ.op ((sheafify J P).map p.op t) = t
    have hcomp : (sheafify J P).map p.op ≫ (sheafify J P).map σ.op =
        𝟙 ((sheafify J P).obj (op U)) := by
      rw [← Functor.map_comp, ← op_comp, hσ]
      exact (sheafify J P).map_id (op U)
    rw [← ConcreteCategory.comp_apply, hcomp, ConcreteCategory.id_apply]

open CategoryTheory.Limits Scheme in
private theorem property_of_evaluation (X : Scheme.{u})
    (C : Type w) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type (u + 1)}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [(forget C).ReflectsIsomorphisms] [PreservesFiniteLimits (forget C)]
    [HasWeakSheafify (Scheme.ProEt.topology X) C]
    [(Scheme.ProEt.topology X).HasSheafCompose (forget C)]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective C]
    (heval : PointLanAffineEvaluationProperty X C) : PointLanSheafificationProperty X C := by
  obtain ⟨_, _, _, _, hprod⟩ := heval
  intro F P η hP U hU wU
  refine ⟨unit_iso_of_refinement X C P U hU wU (hprod F P η hP), ?_, ?_⟩
  · intro V _ _ f
    exact (toSheafify (Scheme.ProEt.topology X) P).naturality f.op
  · intro G Q θ _ _ β _
    exact NatTrans.congr_app (toSheafify_naturality (Scheme.ProEt.topology X) β) (op U)

/-- Sheafification preserves the point Kan presheaf's sections on every weakly
contractible affine, for sets, abelian groups and commutative rings. The canonical
isomorphisms are natural in both variables and preserve the coefficient operations.

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1); RefactorInstruction,
proof of Lemma point-eval
(auxiliary; not a blueprint node).

Proof (repair of the finite-refinement argument):
1. The point Kan evaluation lemma gives the finite restriction-product comparison
   only for families of weakly contractible affines, including the empty family.
   We will apply it to clopen pieces of U, not to arbitrary affine covering pieces.
2. Given any covering of U, its covering criterion gives finitely many affine
   arrows V_i → U refining it. Put V = coproduct V_i. Finite-coproduct evaluation
   and subcanonicity identify h_V with the coproduct of the h_{V_i}. The cover makes
   h_V → h_U epi by sheaf uniqueness. Weak contractibility lifts id_U to a section
   sigma : U → V. Put W_i = sigma^{-1}(V_i). These are disjoint clopen subschemes
   with coproduct U; each maps to V_i over U and is affine because U is affine.
   Each W_i is weakly contractible: for a set-sheaf epi A → B and b in B(W_i),
   write U = W_i disjoint-union Z and use finite-coproduct evaluation to glue b
   (in the B summand) with the terminal section on Z into (B coproduct 1)(U).
   The morphism A coproduct 1 → B coproduct 1 is epi. Lift on U using its weak
   contractibility, then restrict to W_i. Disjointness and pullback stability of
   sheaf coproducts force this restriction into A, giving the desired lift of b.
   Thus the W_i give a finite weakly contractible affine refinement. No covering
   arrow V_i is assumed weakly contractible. Empty pieces and the empty U are allowed.
3. Local sections of sheafification give representatives on a covering of U.
   Form the W_i of step 2 and restrict the representatives along W_i → V_i.
   Step 1, now with all its hypotheses verified, combines these into s in P(U),
   using the canonical isomorphism from the coproduct of W_i to U. The unit's
   naturality and sheaf uniqueness give eta(s) = t, proving surjectivity.
   For injectivity, equality after sheafification gives local equality on a cover.
   Apply step 2 to that cover; the restrictions of x and y agree on every W_i.
   Injectivity of the restriction-product comparison for this family gives x = y.
4. For algebraic coefficients, perform operations on local representatives. Local
   equality makes them well-defined and sheaf uniqueness glues them. Identities hold
   locally, and the universal property identifies this with algebra sheafification.
   Thus the bijection is an algebra isomorphism. Naturality of the unit gives both
   displayed naturality equations. -/
theorem proEtale_sheafification_wcontractible_sections (X : Scheme.{u}) :
    PointLanSheafificationProperty X (Type (u + 1)) ∧
    PointLanSheafificationProperty X AddCommGrpCat.{u + 1} ∧
    PointLanSheafificationProperty X CommRingCat.{u + 1} := by
  -- The implemented refinement uses contractible affine extensions instead of the
  obtain ⟨hType, hAb, hRing⟩ := point_lan_affine_evaluation X
  exact ⟨property_of_evaluation X (Type (u + 1)) hType,
    property_of_evaluation X AddCommGrpCat.{u + 1} hAb,
    property_of_evaluation X CommRingCat.{u + 1} hRing⟩

end AlgebraicGeometry.ProEtale
