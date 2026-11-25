/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Derived change of rings with separate localization universes

Source: Stacks Project, sites-cohomology.tex, Tags 06YT, 06YY; derived.tex, Tag 06XN.
(auxiliary; not a blueprint node).
This is the same universal pair on cochain complexes, allowing different morphism
universes for the two derived categories. The ordinary functor is fixed on objects
and maps; the derived pair is determined up to its unique counit-compatible isomorphism.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wO wS
open CategoryTheory

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O S : Sheaf J CommRingCat.{r}} (φ : O ⟶ S)
  [HasDerivedCategory.{wO}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
  [HasDerivedCategory.{wS}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]

/-- A presentation of the derived change-of-rings universal pair, including its actual
ordinary scalar-extension functor, pointwise (everywhere defined) existence and its
canonical K-flat computations.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
structure DerivedChangeOfRingsCochainModel where
  /-- Ordinary sheafified extension of scalars. -/
  E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  /-- Its prescribed object function. -/
  obj_eq : ∀ M, E.obj M = changeOfRings φ M
  /-- Its prescribed map function. -/
  map_eq : ∀ {M N} (f : M ⟶ N), E.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHom φ M f ≫ eqToHom (obj_eq N).symm
  /-- Ordinary extension is additive. -/
  [additive : E.Additive]
  /-- Extension preserves quasi-isomorphisms between K-flat complexes. -/
  preserves : ∀ {P Q : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ℤ}
    (f : P ⟶ Q), CochainComplex.IsKFlatIndependentCoefficients (R := O) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := O) Q → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)
  /-- The derived extension. -/
  T : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ⥤
    DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
  /-- The derived extension is everywhere defined: the termwise extension followed by
  localization has a pointwise left derived functor. -/
  pointwise : (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
    (HomologicalComplex.quasiIso
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ))
  /-- Its universal counit on complexes. -/
  ε : DerivedCategory.Q ⋙ T ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Universal left-derived property. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Exactness as a triangulated functor. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  /-- The canonical counit computes derived extension on K-flat models. -/
  computes : ∀ P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := O) P → IsIso (ε.app P)

attribute [instance] DerivedChangeOfRingsCochainModel.additive

/-- Existence of derived extension with its natural K-flat model identifications, with
independent source and target localization universes.
Source: Stacks 06YT, 06YY and 06XN (auxiliary; not a blueprint node).
Proof: construct E by sectionwise scalar extension followed by module sheafification.
Its maps are the sheafifications of id tensor f, so E is additive. The cone of a
quasi-isomorphism between K-flat complexes is acyclic and K-flat; tensoring its
K-flat comparison with the new ring leaves it acyclic (06YT). Thus E preserves these
quasi-isomorphisms. Resolve every complex by a K-flat complex (06YS), and apply the
resolving-class construction (06XN), which gives the universal counit and its
invertibility on K-flat representatives, and its pointwise existence at every complex
(computed by a K-flat resolution, Stacks 05SV and 06XN). Precompose the homotopy-category
counit with the homotopy quotient and its localization comparison to obtain the displayed
cochain counit. This changes neither its universal property nor its K-flat components.
Ordinary extension preserves shifts and cones, so the derived functor is triangulated.
All constructions take place separately in the two selected localization categories;
no equality between their Hom universes is used. -/
theorem nonempty_derivedChangeOfRingsCochainModel :
    Nonempty (DerivedChangeOfRingsCochainModel.{u, v, r, wO, wS} φ) := by
  classical
  let A := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)
  let B := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  -- Only the ordinary-extension and invariance clauses of the existing theorem
  -- are needed. Standard derived categories make its common universe available;
  -- the resulting clauses mention neither chosen derived category.
  obtain ⟨E, hobj, hmap, hadd, hpres, _⟩ :
      ∃ (E : A ⥤ B) (hobj : ∀ M, E.obj M = changeOfRings φ M)
        (hmap : ∀ {M N} (f : M ⟶ N), E.map f =
          eqToHom (hobj M) ≫ changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
        (_ : E.Additive),
        (∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q),
          CochainComplex.IsKFlatIndependentCoefficients (R := O) P →
          CochainComplex.IsKFlatIndependentCoefficients (R := O) Q → QuasiIso f →
          QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) ∧ True := by
    let := HasDerivedCategory.standard A
    let := HasDerivedCategory.standard B
    obtain ⟨E, hobj, hmap, hadd, hpres, _⟩ :=
      derivedChangeOfRingsIndependentCoefficients φ
    exact ⟨E, hobj, hmap, hadd, hpres, trivial⟩
  let : E.Additive := hadd
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  -- K-flat representatives give a resolving class in the homotopy category.
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := O) K ∧
        (HomotopyCategory.quotient A (.up ℤ)).obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := O) K
    refine ⟨(HomotopyCategory.quotient A (.up ℤ)).obj L,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ⟨L, hL, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    let q := HomotopyCategory.quotient A (.up ℤ)
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf : QuasiIso f :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpres f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  -- Transfer the pointwise universal pair to complexes, preserving its counit.
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine ⟨{ E := E
            obj_eq := hobj
            map_eq := hmap
            additive := hadd
            preserves := hpres
            T := T
            pointwise := ?_
            ε := β
            universal := ?_
            triangulated := htri
            computes := ?_ }⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · exact ⟨hβ.isRightKanExtension⟩
  · intro K hK
    have := hcomp (q.obj K) ⟨K, hK, rfl⟩
    dsimp [β, α]
    infer_instance

end SheafOfModules
