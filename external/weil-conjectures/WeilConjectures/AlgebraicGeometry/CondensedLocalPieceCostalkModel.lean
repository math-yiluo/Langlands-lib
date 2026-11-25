/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-! # A compatible strict costalk model for the Hom cocone of a locally closed piece -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance localPieceCostalkModelHasZeroMorphisms
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

private noncomputable def derivedHomAdjIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (E : B ⥤ A) (H : A ⥤ B) [E.Additive] [H.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ H) (P : B) (n : ℤ)
    [H.rightDerivedFunctor.CommShift ℤ] :
    shiftFunctor (DerivedCategory A) n ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.singleFunctor A 0).obj (E.obj P))) ≅
      H.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory B) n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P)) :=
  Functor.isoWhiskerLeft (shiftFunctor _ n)
      (preadditiveCoyoneda.mapIso ((E.mapDerivedCategorySingleFunctor 0).app P).op) ≪≫
    Functor.isoWhiskerLeft (shiftFunctor _ n)
      (adj.mapDerivedCategoryRightDerivedAdjunction.preadditiveCoyonedaObjIso
        ((DerivedCategory.singleFunctor B 0).obj P)) ≪≫
    Functor.isoWhiskerRight (H.rightDerivedFunctor.commShiftIso n)
      (preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P)))

private noncomputable def injectiveHomIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (E : B ⥤ A) (H : A ⥤ B) [E.Additive] [H.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ H) (P : B) (n : ℤ)
    [H.rightDerivedFunctor.CommShift ℤ]
    (K : CochainComplex A ℤ) [K.IsKInjective] :
    (shiftFunctor (DerivedCategory A) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor A 0).obj (E.obj P)))).obj
        (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory B) n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P))).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj K) :=
  (derivedHomAdjIso E H adj P n).app (DerivedCategory.Q.obj K) ≪≫
    (shiftFunctor _ n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor B 0).obj P))).mapIso (H.rightDerivedFunctorObjQIso K)

private theorem injectiveHomIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (E : B ⥤ A) (H : A ⥤ B) [E.Additive] [H.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ H) (P : B) (n : ℤ)
    [H.rightDerivedFunctor.CommShift ℤ]
    {K L : CochainComplex A ℤ} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    (shiftFunctor (DerivedCategory A) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor A 0).obj (E.obj P)))).map
        (DerivedCategory.Q.map f) ≫ (injectiveHomIso E H adj P n L).hom =
      (injectiveHomIso E H adj P n K).hom ≫
        (DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory B) n ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P))).map
            ((H.mapHomologicalComplex (.up ℤ)).map f) := by
  let V := shiftFunctor (DerivedCategory B) n ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P))
  dsimp only [injectiveHomIso, Iso.trans_hom, Functor.mapIso_hom]
  erw [← Category.assoc, (derivedHomAdjIso E H adj P n).hom.naturality]
  change ((derivedHomAdjIso E H adj P n).hom.app (DerivedCategory.Q.obj K) ≫
    V.map (H.rightDerivedFunctor.map (DerivedCategory.Q.map f))) ≫
      V.map (H.rightDerivedFunctorObjQIso L).hom = _
  rw [Category.assoc, ← V.map_comp, rightDerivedObjQIso_naturality,
    V.map_comp, ← Category.assoc]
  rfl

private theorem homCoconeOfInjectiveCocone
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    {I : Type*} [Category I]
    [HasColimitsOfShape I (CochainComplex A ℤ)]
    [HasColimitsOfShape I (CochainComplex B ℤ)]
    (E : B ⥤ A) (H : A ⥤ B) [E.Additive] [H.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ H) (P : B) (n : ℤ)
    (N J : I ⥤ CochainComplex A ℤ) (c : Cocone J)
    (α : N ⟶ J) (αv : colimit N ⟶ c.pt)
    (hα : ∀ s, colimit.ι N s ≫ αv = α.app s ≫ c.ι.app s)
    [∀ s, QuasiIso (α.app s)] [QuasiIso αv]
    [∀ s, (J.obj s).IsKInjective] [c.pt.IsKInjective]
    [QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c))] :
    let F := shiftFunctor (DerivedCategory A) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor A 0).obj (E.obj P)))
    let G := DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory B) n ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P))
    let L := J ⋙ H.mapHomologicalComplex (.up ℤ)
    ∃ (e : (N ⋙ DerivedCategory.Q) ⋙ F ≅ L ⋙ G)
      (v : F.obj (DerivedCategory.Q.obj (colimit N)) ≅ G.obj (colimit L)),
      ∀ s, F.map (DerivedCategory.Q.map (colimit.ι N s)) ≫ v.hom =
        e.hom.app s ≫ G.map (colimit.ι L s) := by
  let a := adj.mapDerivedCategoryRightDerivedAdjunction
  let _ := a.rightAdjointCommShift ℤ
  intro F G L
  let β : (J ⋙ DerivedCategory.Q) ⋙ F ≅ L ⋙ G :=
    NatIso.ofComponents (fun s ↦ injectiveHomIso E H adj P n (J.obj s))
      (fun f ↦ injectiveHomIso_naturality E H adj P n (J.map f))
  have : ∀ s, IsIso ((Functor.whiskerRight α DerivedCategory.Q).app s) :=
    fun s ↦ inferInstanceAs (IsIso (DerivedCategory.Q.map (α.app s)))
  have : IsIso (Functor.whiskerRight α DerivedCategory.Q) :=
    NatIso.isIso_of_isIso_app _
  let δ : (N ⋙ DerivedCategory.Q) ⋙ F ≅ (J ⋙ DerivedCategory.Q) ⋙ F :=
    Functor.isoWhiskerRight (asIso (Functor.whiskerRight α DerivedCategory.Q)) F
  let k := colimit.desc L ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)
  let V := shiftFunctor (DerivedCategory B) n ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor B 0).obj P))
  let vk := V.mapIso (asIso (DerivedCategory.Q.map k))
  let v := F.mapIso (asIso (DerivedCategory.Q.map αv)) ≪≫
    injectiveHomIso E H adj P n c.pt ≪≫ vk.symm
  refine ⟨δ ≪≫ β, v, ?_⟩
  intro s
  apply (cancel_mono vk.hom).1
  dsimp only [v, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [δ, vk, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom, Functor.mapIso_hom]
  change F.map (DerivedCategory.Q.map (colimit.ι N s)) ≫
      F.map (DerivedCategory.Q.map αv) ≫ (injectiveHomIso E H adj P n c.pt).hom =
    F.map (DerivedCategory.Q.map (α.app s)) ≫ β.hom.app s ≫
      G.map (colimit.ι L s) ≫ V.map (DerivedCategory.Q.map k)
  rw [← F.map_comp_assoc, ← DerivedCategory.Q.map_comp, hα,
    DerivedCategory.Q.map_comp, F.map_comp, Category.assoc,
    injectiveHomIso_naturality E H adj P n]
  congr 1
  change (injectiveHomIso E H adj P n (J.obj s)).hom ≫
      G.map ((H.mapHomologicalComplex (.up ℤ)).map (c.ι.app s)) =
    (injectiveHomIso E H adj P n (J.obj s)).hom ≫
      G.map (colimit.ι L s) ≫ G.map k
  rw [← G.map_comp, colimit.ι_desc]
  rfl

private theorem quasiIso_desc_mapCocone
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {I : Type*} [Category I] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesColimitsOfShape I H] (J : I ⥤ CochainComplex A ℤ) (c : Cocone J)
    [QuasiIso (colimit.desc J c)] :
    QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
  rw [← colimit.post_desc]
  infer_instance

private theorem closedAdjoint
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    Exists fun [_hclosed : PreservesFiniteColimits (CondensedRing.lowerStar Λ i)] ↦
      ∃ H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
        Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z),
        Nonempty (CondensedRing.lowerStar Λ i ⊣ H) := by
  let W : T.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace W :=
    W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hk : Set.range W.ι = (Set.range i)ᶜ := W.range_ι
  obtain ⟨hclosed, hr⟩ := CondensedRing.condensed_open_closed_recollement Λ i W.ι hk
  let _ := hclosed
  rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, _, H₀, hadd, hleft, ash, rest⟩
  let _ := hadd
  let _ := hleft
  exact ⟨hclosed, H₀, ⟨ash⟩⟩

-- Resolve the diagram in an abstract category, keeping the concrete sheaf-module
-- structures out of the resolution and colimit comparison calculations.
private theorem localPieceBoundedInjectiveCocone
    {A : Type*} [Category* A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (hNa : ∀ s, (N.obj s).IsStrictlyGE a) :
    ∃ (J : I ⥤ CochainComplex A ℤ) (c : Cocone J)
      (β : N ⟶ J) (βv : colimit N ⟶ c.pt),
      (∀ s, colimit.ι N s ≫ βv = β.app s ≫ c.ι.app s) ∧
      (∀ s, QuasiIso (β.app s)) ∧ QuasiIso βv ∧
      (∀ s, (J.obj s).IsStrictlyGE a) ∧ c.pt.IsStrictlyGE a ∧
      (∀ s r, Injective ((J.obj s).X r)) ∧ (∀ r, Injective (c.pt.X r)) ∧
      QuasiIso (colimit.desc J c) := by
  classical
  have hNcol : (colimit N).IsStrictlyGE a := colimit_isStrictlyGE N a hNa
  let Np : I ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift N (fun s ↦ ⟨a, hNa s⟩)
  let cp : Cocone Np :=
    { pt := ⟨colimit N, ⟨a, hNcol⟩⟩
      ι := { app s := ⟨colimit.ι N s⟩
             naturality s t f := by
               apply ObjectProperty.hom_ext
               exact (colimit.w N f).trans (Category.comp_id _).symm } }
  obtain ⟨J₀, η, hη, hJ₀⟩ := CondensedRing.functorialInjectiveEmbeddings (C := A)
  obtain ⟨R, α, hα, hRi, hRb⟩ :=
    CochainComplex.exists_functorial_bounded_injective_resolution J₀ η hη hJ₀
  let J := Np ⋙ R ⋙ CochainComplex.Plus.ι A
  let c : Cocone J := ((R ⋙ CochainComplex.Plus.ι A).mapCocone cp)
  let β : N ⟶ J := Functor.whiskerLeft Np α
  let βv : colimit N ⟶ c.pt := α.app cp.pt
  have hβ (s : I) : colimit.ι N s ≫ βv = β.app s ≫ c.ι.app s := by
    exact α.naturality (cp.ι.app s)
  have hJa (s : I) : (J.obj s).IsStrictlyGE a := hRb (Np.obj s) a (hNa s)
  have hca : c.pt.IsStrictlyGE a := hRb cp.pt a hNcol
  have hJi (s : I) (r : ℤ) : Injective ((J.obj s).X r) := hRi (Np.obj s) r
  have hci (r : ℤ) : Injective (c.pt.X r) := hRi cp.pt r
  have hβq (s : I) : QuasiIso (β.app s) := hα (Np.obj s)
  have hβvq : QuasiIso βv := hα cp.pt
  have hcolq : QuasiIso (colimMap β) :=
    (HomologicalComplex.quasiIso A (.up ℤ)).colimMap β (fun s ↦ hβq s)
  have heq : colimMap β ≫ colimit.desc J c = βv := by
    apply colimit.hom_ext
    intro s
    simpa only [ι_colimMap_assoc, colimit.ι_desc] using (hβ s).symm
  have hq : QuasiIso (colimit.desc J c) := by
    rw [← quasiIso_iff_comp_left (colimMap β) (colimit.desc J c), heq]
    exact hβvq
  exact ⟨J, c, β, βv, hβ, hβq, hβvq, hJa, hca, hJi, hci, hq⟩

private theorem localPieceCostalkModelModuleColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  infer_instance

private theorem localPieceCostalkModelComplexColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I (CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) := by
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- Internal module colimits require a larger typeclass search budget.
set_option synthInstance.maxSize 4096 in
/-- Transport the Hom cocone through j_! and i_* to a strict bounded-below diagram on U.
This does not assert that either Hom cocone is a colimit, and makes no finite-presentation
assumption on P.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), costalk and adjunction steps.
(auxiliary; not a blueprint node)

Proof: use the exceptional right adjoint of the closed pushforward and the exact
restriction along j. On the bounded-below derived categories, the two adjunctions
identify Hom(i_*j_!P[0],N[n]) with Hom(P[0],j^*Ri^!N[n]), naturally in N. Choose the
functorial bounded injective resolution at the common bound supplied by recollement,
apply the exceptional functor and j^* termwise, and use good truncation to obtain L.
Its terms vanish below a common bound. The recollement triangle identifies i_*Ri^!N
with Cone(N -> Rk_*k^*N)[-1], for the complementary quasi-compact open k.
Qcqs pushforward continuity and exact filtered colimits identify the termwise colimit
of these models with j^*Ri^! of the original colimit. Apply Hom(P[0],-[n]) to this
identification to obtain the vertex isomorphism. Naturality of both adjunctions gives
the diagram isomorphism and its leg equation. All isomorphisms use the original cocone
legs. Include the bounded-below derived categories fully faithfully into the ordinary
ones. The argument also applies to zero P and empty U or Z. -/
theorem condensed_local_piece_costalk_model
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((N.obj s).X r))
    (n : ℤ) :
    let F := shiftFunctor
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj P))))
    let G := condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n
    ∃ L : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ,
      (∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((L.obj s).X r)) ∧
      ∃ (e : (N ⋙ DerivedCategory.Q) ⋙ F ≅ L ⋙ G)
        (v : F.obj (DerivedCategory.Q.mapCocone (colimit.cocone N)).pt ≅
          G.obj (colimit.cocone L).pt),
        ∀ s : I, F.map ((DerivedCategory.Q.mapCocone (colimit.cocone N)).ι.app s) ≫ v.hom =
          e.hom.app s ≫ G.map ((colimit.cocone L).ι.app s) := by
  /- Proof: choose the exceptional right adjoint H₀ of exact closed pushforward and
  compose it with exact open restriction j*. Its exact left adjoint is i_*j_!.
  Their ordinary derived adjunction identifies the two shifted Hom functors.
  Construct functorial injective embeddings using the Grothendieck K-injective
  resolution functor. Resolve the whole diagram and its colimit cocone with one
  functorial bounded injective resolution preserving every strict lower bound.
  Let L be the result of applying j*H₀ degree by degree. Additive functors preserve
  the zero terms below the common bound. Exact filtered colimits make the
  resolution cocone a quasi-colimit. Closed-costalk injective continuity, followed
  by exact colimit-preserving j*, makes the corresponding L cocone a quasi-colimit.
  The natural right-derived-unit isomorphisms on K-injectives, together with the
  derived adjunction, give the diagram isomorphism. The same comparisons at the
  resolved colimit, followed by the inverse quasi-colimit comparison, give the
  vertex isomorphism. Naturality and the universal colimit-leg equation give the
  required identity on every original leg. This applies also to zero P and empty
  U or Z. -/
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let B := Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)
  have : HasColimitsOfShape I A := localPieceCostalkModelModuleColimits Λ T I
  have : HasExactColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I B := localPieceCostalkModelModuleColimits Λ U I
  have : HasColimitsOfShape I (CochainComplex A ℤ) :=
    localPieceCostalkModelComplexColimits Λ T I
  have : HasColimitsOfShape I (CochainComplex B ℤ) :=
    localPieceCostalkModelComplexColimits Λ U I
  obtain ⟨hclosed, H₀, ⟨ash⟩⟩ := closedAdjoint T Λ i
  let _ := hclosed
  have := ash.right_adjoint_additive
  let E := CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.lowerStar Λ i
  let H := H₀ ⋙ CondensedRing.upperStar Λ j
  let adj : E ⊣ H := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).comp ash
  obtain ⟨a, ha⟩ := hN
  have hNa (s : I) : (N.obj s).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ _).2 (ha s)
  have : IsGrothendieckAbelian.{u + 1} A := Mod.isGrothendieckAbelian _
  obtain ⟨J, c, β, βv, hβ, hβq, hβvq, hJa, hca, hJi, hci, hq⟩ :=
    localPieceBoundedInjectiveCocone N a hNa
  have hH₀ := condensed_closed_costalk_injective_continuity T Λ i H₀ ash J c a
    hJa hJi hca hci hq
  have : PreservesColimitsOfShape I (CondensedRing.upperStar Λ j) :=
    (CondensedRing.upperStarLowerStarAdjunction Λ j).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  -- Use the colimits of the target category without searching through the composite functor.
  have : HasColimit (J ⋙ H.mapHomologicalComplex (.up ℤ)) :=
    HasColimitsOfShape.has_colimit _
  have hH : QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
    exact quasiIso_desc_mapCocone (CondensedRing.upperStar Λ j)
      (J ⋙ H₀.mapHomologicalComplex (.up ℤ))
      ((H₀.mapHomologicalComplex (.up ℤ)).mapCocone c)
  have hJk (s : I) : (J.obj s).IsKInjective := by
    have := hJa s
    exact CochainComplex.isKInjective_of_injective (J.obj s) a
  have hck : c.pt.IsKInjective := by
    have := hca
    exact CochainComplex.isKInjective_of_injective c.pt a
  let L := J ⋙ H.mapHomologicalComplex (.up ℤ)
  refine ⟨L, ⟨a, ?_⟩, ?_⟩
  · intro s r hr
    exact H.map_isZero ((J.obj s).isZero_of_isStrictlyGE a r hr)
  · exact homCoconeOfInjectiveCocone E H adj P n N J c β βv hβ

end AlgebraicGeometry.ProEtale
