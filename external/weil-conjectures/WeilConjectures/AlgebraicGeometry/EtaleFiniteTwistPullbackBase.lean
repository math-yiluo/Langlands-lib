/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
/-! Intermediate base package for finite Tate pullback.
(auxiliary; not a blueprint node). -/
/-- Strict intermediate package for the finite Tate pullback theorem. The construction first
chooses the primitive-root etale cover, identifies the roots sheaf there with the constant
cyclic sheaf, extends scalars to `A`, and forms signed tensor powers and duals. The normalized
adjunction, unit, tensor, evaluation, identity, composition and local-trivialization equations
are then checked on the local basis and descend by etale-cover detection. This intermediate
package is used by the parent theorem; its proof is the corresponding group of steps in the
parent blueprint and remains available as a named proof obligation.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM.
(auxiliary; not a blueprint node). -/
theorem etaleFiniteTwistPullback_base (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
      (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
      (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)),
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        (r v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (r v hT).hom).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) := by
  classical
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨l, hl, hlid, hlcomp⟩ := finiteEtaleTateLine_pullback_normalized A m hm hA
  let P (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :=
    finiteEtaleTateTensorFamily T m hm A hA hT
  let c {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
      (hT' : IsUnit (m : Γ(T', ⊤))) (a : ℤ) :
      (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
        finiteEtaleTateSheaf A m T' hA a :=
    IntTensorFamily.iso ((P T hT).map (Etale.upperStar (ModuleCat.{u + 1} A) v))
      (P T' hT') (l v hT) a
  have hc1 {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
      (hT' : IsUnit (m : Γ(T', ⊤))) : c v hT hT' 1 = l v hT :=
    IntTensorFamily.iso_one _ _ _
  have hcmul {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
      (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ) :
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map ((P T hT).addIso a b).hom ≫
        (c v hT hT' (a + b)).hom =
      Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v) _ _ ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫
          ((P T' hT').addIso a b).hom :=
    IntTensorFamily.map_iso_mul _ _ _ _ a b
  have hccomp {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
      (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
      (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ) :
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app _ ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
            c w hT' hT'' a := by
    symm
    apply IntTensorFamily.map_iso_unique_mul (P T hT)
      (Etale.upperStar (ModuleCat.{u + 1} A) (w ≫ v)) (P T'' hT'') (l (w ≫ v) hT)
      (fun a ↦ (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app _ ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ?_ ?_ a
    · simp only [hc1]
      convert (hlcomp v w hT hT').symm using 1; rfl
    · exact IntTensorFamily.comparison_comp_mul (P T hT) _ _ _ (P T' hT') (P T'' hT'')
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v)
        (Etale.upperStarComp_hom_app_tensor_comp_δ _ w v (w ≫ v) rfl)
        (c v hT hT') (c w hT' hT'') (hcmul v hT hT') (hcmul w hT' hT'')
  have hccompEq {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
      (wv : T'' ⟶ T) (hwv : wv = w ≫ v)
      (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
      (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ) :
      c wv hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v wv hwv).app _ ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
            c w hT' hT'' a := by
    subst wv
    exact hccomp v w hT hT' hT'' a
  have hcid (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ) :
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a) := by
    apply Iso.ext
    let F := Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 T)
    let s := Etale.upperStarId (ModuleCat.{u + 1} A) T
    let X := finiteEtaleTateSheaf A m T hA a
    let f := (c (𝟙 T) hT hT a).hom
    have hc : (Etale.upperStarComp (ModuleCat.{u + 1} A) (𝟙 T) (𝟙 T)
        (𝟙 T) (Category.id_comp _).symm).hom.app X ≫ F.map f ≫ f = f := by
      exact (congrArg Iso.hom (hccompEq (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp _).symm hT hT hT a)).symm
    have hmap : s.inv.app (F.obj X) ≫ F.map f ≫ f = f := by
      have hi := Etale.upperStarComp_id_left (ModuleCat.{u + 1} A) (𝟙 T)
      have hi' := congrArg (fun i ↦ i.hom.app X) hi
      have h := congrArg (fun t ↦ t ≫ F.map f ≫ f) hi'
      simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.rightUnitor_inv_app, Category.id_comp,
        Functor.whiskerLeft_app] using h.symm.trans hc
    have hn := s.inv.naturality f
    change f ≫ s.inv.app X = s.inv.app (F.obj X) ≫ F.map f at hn
    rw [← Category.assoc, ← hn, Category.assoc] at hmap
    have he : s.inv.app X ≫ f = 𝟙 _ := by
      apply (cancel_epi f).mp
      exact hmap.trans (Category.comp_id _).symm
    calc
      f = s.hom.app X ≫ s.inv.app X ≫ f := by simp
      _ = s.hom.app X := by rw [he, Category.comp_id]
  let r {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :=
    letI := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit m v hT
    asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)
  refine ⟨@r, @c, fun T hT ↦ (P T hT).addIso, ?_, ?_, ?_, ?_, ?_, ?_,
    hcid, hccomp, ?_, ?_, ?_, ?_, ?_, ?_, hcmul⟩
  · exact fun T hT ↦ finiteEtaleTateSheaf_localTrivial T m A hA hm hT
  · intro T T' v hT
    exact (upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι m v).symm
  · intro T T' v hT hT' W a z
    rw [hc1]
    exact hl v hT W a z
  · intro T T' v hT hT'
    apply Iso.ext
    have H := IntTensorFamily.map_iso_zero (P T hT)
      (Etale.upperStar (ModuleCat.{u + 1} A) v) (P T' hT') (l v hT)
    simp only [P, finiteEtaleTateTensorFamily_zeroIso, Iso.refl_hom,
      Category.comp_id] at H
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at H
    exact H.trans (Etale.upperStarConstantSheafIso_hom_app_tensorUnit
      (ModuleCat.{u + 1} A) v).symm
  · intro T T' v hT hT' n
    apply Iso.ext
    have H := hcmul v hT hT' (.ofNat (n + 1)) 1
    simp only [P, finiteEtaleTateTensorFamily_nat_one, Iso.refl_hom] at H
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at H
    erw [Category.comp_id] at H
    change (c v hT hT' (.ofNat (n + 2))).hom =
      Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v) _ _ ≫
        tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' 1).hom
    convert H using 1; rfl
  · intro T T' v hT hT' n
    have he (S : Scheme.{u}) (hS : IsUnit (m : Γ(S, ⊤))) :
        ((P S hS).mulIso (.ofNat (n + 1)) (.negSucc n) 0 (add_neg_cancel _)).hom =
          (ihom.ev (finiteEtaleTateSheaf A m S hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m S hA 0) :=
      finiteEtaleTateTensorFamily_eval S m hm A hA hS n
    have H := IntTensorFamily.map_iso_mul_eq (P T hT)
      (Etale.upperStar (ModuleCat.{u + 1} A) v) (P T' hT') (l v hT)
        (.ofNat (n + 1)) (.negSucc n) 0 (add_neg_cancel _)
    simpa only [he, P, finiteEtaleTateTensorFamily_obj] using H
  · exact fun T hT a ↦ finiteEtaleTateTensorFamily_zero_left T m hm A hA hT a
  · exact fun T hT a ↦ finiteEtaleTateTensorFamily_zero_right T m hm A hA hT a
  · exact fun T hT n ↦ finiteEtaleTateTensorFamily_nat_one T m hm A hA hT n
  · exact fun T hT a b d ↦ (P T hT).assoc a b d
  · exact fun T hT a b ↦ finiteEtaleTateTensorFamily_comm T m hm A hA hT a b
  · exact fun T hT n ↦ finiteEtaleTateTensorFamily_eval T m hm A hA hT n

end AlgebraicGeometry.Scheme
