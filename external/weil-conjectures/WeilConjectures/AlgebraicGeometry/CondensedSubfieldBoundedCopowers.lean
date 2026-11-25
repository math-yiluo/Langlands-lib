/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset

/-! # Bounded-below copowers for finite condensed coefficient fields

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1),
and coproducts as filtered colimits of finite subcoproducts.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

open CategoryTheory.Limits.CoproductsFromFiniteFiltered

private theorem preservesCoproductOfFiniteSubcoproducts
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasFiniteCoproducts C] {I : Type*} (f : I → C)
    [HasCoproduct f] (F : C ⥤ D) [F.Additive]
    (hc : IsColimit (F.mapCocone (finiteSubcoproductsCocone f))) :
    PreservesColimit (Discrete.functor f) F := by
  classical
  refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) ?_
  have hS (S : Finset (Discrete I)) : IsColimit (Cofan.mk
      (F.obj (∐ fun x : S ↦ f x.1.as)) fun a ↦ F.map (Sigma.ι (fun x : S ↦ f x.1.as) a)) :=
    (isColimitMapCoconeCofanMkEquiv F _ _).1 (isColimitOfPreserves F (coproductIsCoproduct _))
  let ι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete I)) :
      F.obj (∐ fun x : S ↦ f x.1.as) ⟶ s.pt :=
    (hS S).desc (Cofan.mk s.pt fun a ↦ s.inj a.1.as)
  have hι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete I)) (a : S) :
      F.map (Sigma.ι (fun x : S ↦ f x.1.as) a) ≫ ι s S = s.inj a.1.as :=
    (hS S).fac (Cofan.mk s.pt fun a ↦ s.inj a.1.as) ⟨a⟩
  let t (s : Cofan fun a ↦ F.obj (f a)) :
      Cocone (liftToFinsetObj (Discrete.functor f) ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := ι s
          naturality := fun S T h ↦ by
            refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
            dsimp
            rw [Category.comp_id, hι, ← F.map_comp_assoc, liftToFinsetObj_map]
            erw [colimit.ι_desc]
            exact hι s T ⟨a.1, h.down.down a.2⟩ } }
  have hfac (s : Cofan fun a ↦ F.obj (f a)) (a : I) :
      F.map (Sigma.ι f a) = F.map (Sigma.ι (fun x : ({⟨a⟩} : Finset (Discrete I)) ↦ f x.1.as)
        ⟨⟨a⟩, by simp⟩) ≫ F.map ((finiteSubcoproductsCocone f).ι.app {⟨a⟩}) := by
    rw [← F.map_comp, finiteSubcoproductsCocone_ι_app]
    erw [colimit.ι_desc]
    rfl
  refine (isColimitMapCoconeCofanMkEquiv F f (Sigma.ι f)).2
    (Cofan.IsColimit.mk _ (fun s ↦ hc.desc (t s)) (fun s a ↦ ?_) (fun s m hm ↦ ?_))
  · dsimp
    rw [hfac s a, Category.assoc]
    erw [hc.fac (t s) {⟨a⟩}]
    exact hι s _ _
  · refine hc.hom_ext fun S ↦ ?_
    erw [hc.fac (t s) S]
    refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
    dsimp
    rw [hι, ← F.map_comp_assoc, finiteSubcoproductsCocone_ι_app]
    erw [colimit.ι_desc]
    exact hm a.1.as

private theorem mapSigmaComparisonIsIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {I : Type*} (K : I → C) (F : C ⥤ D) (H : D ⥤ E)
    [HasCoproduct K] [HasCoproduct (fun i ↦ F.obj (K i))]
    [HasCoproduct (fun i ↦ H.obj (F.obj (K i)))]
    [PreservesColimit (Discrete.functor K) (F ⋙ H)]
    [PreservesColimit (Discrete.functor (fun i ↦ F.obj (K i))) H] :
    IsIso (H.map (sigmaComparison F K)) := by
  have : HasCoproduct (fun i ↦ (F ⋙ H).obj (K i)) :=
    inferInstanceAs (HasCoproduct (fun i ↦ H.obj (F.obj (K i))))
  have hσ : IsIso (sigmaComparison H (fun i ↦ F.obj (K i))) := inferInstance
  have he : sigmaComparison H (fun i ↦ F.obj (K i)) ≫ H.map (sigmaComparison F K) =
      sigmaComparison (F ⋙ H) K := by
    apply Sigma.hom_ext
    intro i
    rw [ι_comp_sigmaComparison_assoc, ← H.map_comp, ι_comp_sigmaComparison]
    exact (ι_comp_sigmaComparison (F ⋙ H) K i).symm
  have : IsIso (sigmaComparison H (fun i ↦ F.obj (K i)) ≫ H.map (sigmaComparison F K)) :=
    he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left (sigmaComparison H (fun i ↦ F.obj (K i))) _

private theorem coproductStrictlyGE
    {C : Type*} [Category* C] [Abelian C] {I : Type*}
    (K : I → CochainComplex C ℤ) [HasCoproduct K] (N : ℤ)
    [∀ i, (K i).IsStrictlyGE N] : (∐ K).IsStrictlyGE N := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hc := isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n)
    (coproductIsCoproduct K)
  exact hc.isZero_pt ((Functor.isZero_iff _).2 fun i ↦
    (K i.as).isZero_of_isStrictlyGE N n hn)

namespace AlgebraicGeometry.ProEtale.CondensedRing

noncomputable local instance (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

-- The explicit colimit and truncation transports elaborate in several large module categories.
set_option backward.isDefEq.respectTransparency false in
/-- Derived direct image commutes with copowers of one bounded-below complex.
Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1).
(auxiliary; not a blueprint node)

Proof: choose a strictly bounded-below complex representing M. Its finite subcoproducts
have the same lower bound, degree by degree. Their projections to good truncation are
isomorphisms, so the truncated filtered-colimit cocone is also a colimit of the original
diagram. Condensed qcqs pushforward continuity says that its image under Q, derived direct
image, and each homology functor is a colimit. An additive functor preserving the filtered
colimit of finite subcoproducts preserves their coproduct. Transport the representative
coproduct through Q and its chosen isomorphism to M. Homology preserves coproducts in the
Grothendieck derived category, so the image of the canonical direct-image comparison under
each homology functor is invertible by cancellation of the homology coproduct comparison.
The derived homology criterion concludes. Finite subsets of the empty set still form a
filtered category, so the same argument includes the empty copower. -/
theorem condensedSubfield_bounded_copower_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Type (u + 1))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (N : ℤ) [M.IsGE N]
    [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦
      R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj M)] :
    IsIso (Sigma.desc fun i : I ↦
      R((f)_*⟦Profinite.continuousMapRingObj E⟧).map
        (Sigma.ι (fun _ : I ↦ M) i)) := by
  classical
  let Λ := Profinite.continuousMapRingObj E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  have : HasColimitsOfSize.{u + 1, u + 1} A :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits A
  have : HasColimitsOfSize.{u + 1, u + 1} B :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits B
  have : HasColimitsOfShape (Discrete I) A :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} A (Discrete I)
  have : HasColimitsOfShape (Finset (Discrete I)) A :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} A (Finset (Discrete I))
  have : HasFiniteColimits A := hasFiniteColimits_of_hasColimitsOfSize.{u + 1, u + 1} A
  have hcomplex (J : Type (u + 1)) :
      HasColimitsOfShape (Discrete J) (CochainComplex A ℤ) := by
    have : HasColimitsOfShape (Discrete J) A :=
      HasColimitsOfShape.of_small.{u + 1, u + 1} A (Discrete J)
    refine ⟨fun F ↦ ?_⟩
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval A (.up ℤ) n) :=
      HasColimitsOfShape.has_colimit _
    exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩
  have : HasColimitsOfShape (Finset (Discrete I)) (CochainComplex A ℤ) := inferInstance
  have : HasColimitsOfShape (Finset (Discrete I)) B :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} B (Finset (Discrete I))
  obtain ⟨K, hK, ⟨e⟩⟩ := M.exists_iso_Q_obj_of_isGE N
  have (J : Type (u + 1)) : HasCoproduct (fun _ : J ↦ K) :=
    (hcomplex J).has_colimit _
  have (J : Type (u + 1)) (n : ℤ) : HasColimit
      (Discrete.functor (fun _ : J ↦ K) ⋙ HomologicalComplex.eval A (.up ℤ) n) := by
    have : HasColimitsOfShape (Discrete J) A :=
      HasColimitsOfShape.of_small.{u + 1, u + 1} A (Discrete J)
    exact HasColimitsOfShape.has_colimit _
  let D := liftToFinsetObj (Discrete.functor (fun _ : I ↦ K))
  have hD (S : Finset (Discrete I)) : (D.obj S).IsStrictlyGE N :=
    coproductStrictlyGE (fun _ : S ↦ K) N
  have hπ : IsIso (Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE N).πTruncGENatTrans A)) := by
    have : ∀ S, IsIso ((Functor.whiskerLeft D
        ((ComplexShape.embeddingUpIntGE N).πTruncGENatTrans A)).app S) :=
      fun S ↦ (CochainComplex.isIso_πTruncGE_iff _ N).2 (hD S)
    exact NatIso.isIso_of_isIso_app _
  have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE N).truncGEFunctor A) :=
    HasColimitsOfShape.has_colimit _
  have hc : IsColimit (condensedContinuityCocone D N) :=
    (IsColimit.precomposeHomEquiv (asIso (Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE N).πTruncGENatTrans A))) _).symm
      (colimit.isColimit _)
  have hcont (q : ℤ) : IsColimit ((DerivedCategory.Q ⋙
      R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor B q).mapCocone
        (condensedContinuityCocone D N)) := by
    have : HasColimit (D ⋙ DerivedCategory.Q ⋙
        R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor B q) :=
      HasColimitsOfShape.has_colimit _
    have hi := condensed_qcqs_pushforward_continuity Λ f D N
      (fun S n hn ↦ by
        have := hD S
        exact ((CochainComplex.isGE_iff _ N).1 inferInstance n hn).isZero_homology) q
    exact IsColimit.ofPointIso (colimit.isColimit _) (i := hi)
  have hpres (q : ℤ) : PreservesColimit (Discrete.functor (fun _ : I ↦ M))
      (R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor B q) := by
    let T := DerivedCategory.Q ⋙ R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor B q
    have : T.Additive := by dsimp only [T]; infer_instance
    have : PreservesColimit D T :=
      preservesColimit_of_preserves_colimit_cocone hc (hcont q)
    have : PreservesColimit (Discrete.functor (fun _ : I ↦ K)) T :=
      preservesCoproductOfFiniteSubcoproducts _ T
        (isColimitOfPreserves T (isColimitFiniteSubproductsCocone _))
    have : PreservesColimit (Discrete.functor (fun _ : I ↦ DerivedCategory.Q.obj K))
        (R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor B q) :=
      preservesColimit_of_preserves_colimit_cocone
        (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct (fun _ : I ↦ K)))
        ((isColimitMapCoconeCofanMkEquiv _ _ _).2
          ((isColimitMapCoconeCofanMkEquiv T _ _).1
            (isColimitOfPreserves T (coproductIsCoproduct (fun _ : I ↦ K)))))
    let eD : Discrete.functor (fun _ : I ↦ DerivedCategory.Q.obj K) ≅
        Discrete.functor (fun _ : I ↦ M) := Discrete.natIso fun _ ↦ e.symm
    exact preservesColimit_of_iso_diagram _ eD
  rw [DerivedCategory.isIso_iff]
  intro q
  have := hpres q
  have : HasColimitsOfShape (Discrete I) B :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} B (Discrete I)
  have : HasCoproducts.{u + 1} B := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} B (Discrete J)
  have : AB4OfSize.{u + 1} B := AB4.of_AB5 B
  exact mapSigmaComparisonIsIso (fun _ : I ↦ M) R((f)_*⟦Λ⟧)
    (DerivedCategory.homologyFunctor B q)

end AlgebraicGeometry.ProEtale.CondensedRing
