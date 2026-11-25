/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
import all Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Sigma
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The induction invariant for finite-basis hypercovers

Source: Stacks Project, Hypercoverings, Tag 0DAV, the split-skeleton construction.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

private theorem cover_of_finite_enlargement
    {C : Type u} [Category.{v} C] (J : Precoverage C) (B : Set C)
    (hadjoin : ∀ (T : C) (I : Type (max u v)) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) {I A : Type (max u v)} [Finite I] [Finite A]
    (U : I → C) (f : ∀ i, U i ⟶ T) (hU : ∀ i, U i ∈ B)
    (hf : Presieve.ofArrows U f ∈ J T)
    (V : A → C) (g : ∀ a, V a ⟶ T) (hV : ∀ a, V a ∈ B)
    (hle : Presieve.ofArrows U f ≤ Presieve.ofArrows V g) :
    Presieve.ofArrows V g ∈ J T := by
  classical
  let W (s : Finset A) : I ⊕ {a : A // a ∈ s} → C :=
    Sum.elim U (fun a ↦ V a.val)
  let w (s : Finset A) : ∀ i, W s i ⟶ T :=
    Sum.rec f (fun a ↦ g a.val)
  let R (s : Finset A) := Presieve.ofArrows (W s) (w s)
  have hm (s : Finset A) (i) : R s (w s i) := Presieve.ofArrows.mk i
  have hW (s : Finset A) (i) : W s i ∈ B := by
    cases i with
    | inl i => exact hU i
    | inr a => exact hV a.val
  have hempty : R ∅ = Presieve.ofArrows U f := by
    apply le_antisymm
    · rintro Y h ⟨i⟩
      cases i with
      | inl i => exact ⟨i⟩
      | inr a => exact (Finset.notMem_empty a.val a.property).elim
    · rintro Y h ⟨i⟩
      exact ⟨Sum.inl i⟩
  have hinsert (a : A) (s : Finset A) : R (insert a s) = R s ⊔ Presieve.singleton (g a) := by
    apply le_antisymm
    · rintro Y h ⟨i⟩
      cases i with
      | inl i => exact Or.inl ⟨Sum.inl i⟩
      | inr j =>
        rcases j with ⟨j, hj⟩
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          exact Or.inr Presieve.singleton.mk
        · exact Or.inl (hm s (Sum.inr ⟨j, hj⟩))
    · intro Y h hh
      rcases hh with hh | hh
      · rcases hh with ⟨i⟩
        cases i with
        | inl i => exact ⟨Sum.inl i⟩
        | inr j => exact hm (insert a s) (Sum.inr ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      · rcases hh with ⟨⟩
        exact hm (insert a s) (Sum.inr ⟨a, Finset.mem_insert_self a s⟩)
  have hs (s : Finset A) : R s ∈ J T := by
    induction s using Finset.induction_on with
    | empty => simpa only [hempty] using hf
    | @insert a s ha ih =>
      rw [hinsert]
      exact hadjoin T _ (W s) (w s) (hW s) ih (V a) (hV a) (g a)
  let _ : Fintype A := Fintype.ofFinite A
  have hall : R Finset.univ = Presieve.ofArrows V g := by
    apply le_antisymm
    · rintro Y h ⟨i⟩
      cases i with
      | inl i => exact hle _ _ ⟨i⟩
      | inr a => exact ⟨a.val⟩
    · rintro Y h ⟨a⟩
      exact hm Finset.univ (Sum.inr ⟨a, Finset.mem_univ a⟩)
  simpa only [hall] using hs Finset.univ

private def familyIndices {D : Type u} [Category.{v} D] :
    FormalCoproduct.{max u v} D ⥤ Type (max u v) where
  obj X := X.I
  map f := ↾f.f

private theorem familyIndices_terminal {D : Type u} [Category.{v} D] [HasTerminal D] :
    PreservesLimit (Functor.empty.{0} (FormalCoproduct.{max u v} D)) familyIndices := by
  apply preservesLimit_of_preserves_limit_cone
    (FormalCoproduct.isTerminalIncl (⊤_ D) terminalIsTerminal)
  exact (isLimitMapConeEmptyConeEquiv _ _).symm Types.isTerminalPUnit

private theorem familyIndices_pullback {D : Type u} [Category.{v} D] [HasPullbacks D]
    {X Y Z : FormalCoproduct.{max u v} D} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) familyIndices := by
  let pb := fun i : Function.Pullback f.f g.f ↦
    pullback.cone (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2)
  let c := FormalCoproduct.pullbackCone f g pb
  apply preservesLimit_of_preserves_limit_cone
    (FormalCoproduct.isLimitPullbackCone f g pb (fun _ ↦ pullback.isLimit _ _))
  exact (c.isLimitMapConeEquiv familyIndices).symm
    (Types.pullbackLimitCone (↾f.f) (↾g.f)).isLimit

private theorem familyIndices_finite {D : Type u} [Category.{v} D]
    [HasTerminal D] [HasPullbacks D] : PreservesFiniteLimits (familyIndices (D := D)) := by
  have := familyIndices_terminal (D := D)
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (familyIndices (D := D)) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : ∀ (X Y Z : FormalCoproduct.{max u v} D) (f : X ⟶ Z) (g : Y ⟶ Z),
      PreservesLimit (cospan f g) familyIndices := fun _ _ _ f g ↦
    familyIndices_pullback f g
  have : PreservesLimitsOfShape WalkingCospan (familyIndices (D := D)) :=
    ⟨fun {F} ↦ preservesLimit_of_iso_diagram _ (diagramIsoCospan F).symm⟩
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

private theorem finite_family_limit
    {D : Type u} [Category.{v} D] [HasTerminal D] [HasPullbacks D]
    {J : Type} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FormalCoproduct.{max u v} D) (hF : ∀ j, Finite (F.obj j).I)
    (c : Cone F) (hc : IsLimit c) : Finite c.pt.I := by
  have := familyIndices_finite (D := D)
  have h := isLimitOfPreserves familyIndices hc
  let e := Types.isLimitEquivSections h
  have : ∀ j, Finite ((F ⋙ familyIndices).obj j) := hF
  exact Finite.of_injective e e.injective

namespace FormalSplitAttachment

private abbrev BoundaryIndex (n : ℕ) :=
  CostructuredArrow (SimplexCategory.Truncated.inclusion n) (SimplexCategory.mk (n + 1))

private theorem boundaryIndex_finite (n : ℕ) : Finite (BoundaryIndex n) := by
  let f (a : BoundaryIndex n) :
      Σ r : Fin (n + 1), (SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :=
    ⟨⟨a.left.obj.len, Nat.lt_succ_of_le a.left.property⟩, a.hom⟩
  have : ∀ r : Fin (n + 1),
      Finite (SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :=
    fun _ ↦ inferInstance
  apply Finite.of_injective f
  rintro ⟨⟨a, ha⟩, ar, ah⟩ ⟨⟨b, hb⟩, br, bh⟩ h
  have hab : a = b := SimplexCategory.ext (congrArg (fun x ↦ x.1.val) h)
  subst b
  have hh : ah = bh := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst bh
  congr
  exact Subsingleton.elim _ _

@[instance_reducible] private noncomputable def boundaryIndex_finCategory (n : ℕ) :
    FinCategory (BoundaryIndex n) where
  fintypeObj := @Fintype.ofFinite _ (boundaryIndex_finite n)
  fintypeHom a b := by
    have : Finite (a.left.obj ⟶ b.left.obj) := inferInstance
    have : Finite (a ⟶ b) := Finite.of_injective (fun f ↦ f.left.hom) (by
      intro f g h
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      exact h)
    exact Fintype.ofFinite _

private def boundaryDiagram {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated D n) : (BoundaryIndex n)ᵒᵖ ⥤ D :=
  (CostructuredArrow.proj _ _).op ⋙ K

private def coneToBoundary {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) n)
    (c : Cone (boundaryDiagram K)) : BoundaryCone K c.pt where
  projection q α := c.π.app (op (CostructuredArrow.mk (Y := degree q) α))
  naturality q r α β := by
    exact c.w (CostructuredArrow.homMk
      (f' := CostructuredArrow.mk (Y := degree r) β)
      (f := CostructuredArrow.mk (Y := degree q) (α ≫ β))
      (SimplexCategory.Truncated.Hom.tr α
        (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt)) rfl).op

private def boundaryToCone {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) n)
    {M : FormalCoproduct.{max u v} D} (p : BoundaryCone K M) : Cone (boundaryDiagram K) where
  pt := M
  π :=
    { app a := p.projection ⟨a.unop.left.obj.len, Nat.lt_succ_of_le a.unop.left.property⟩
        a.unop.hom
      naturality {a b} f := by
        have h := p.naturality
          ⟨b.unop.left.obj.len, Nat.lt_succ_of_le b.unop.left.property⟩
          ⟨a.unop.left.obj.len, Nat.lt_succ_of_le a.unop.left.property⟩
          f.unop.left.hom a.unop.hom
        dsimp [operator] at h
        rw [show f.unop.left.hom ≫ a.unop.hom = b.unop.hom from
          CostructuredArrow.w f.unop] at h
        dsimp [boundaryDiagram]
        rw [Category.id_comp]
        exact h.symm }

private theorem matching_of_isLimit {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) n)
    (c : Cone (boundaryDiagram K)) (hc : IsLimit c) : IsMatching K (coneToBoundary K c) := by
  intro T p
  refine ⟨hc.lift (boundaryToCone K p), ?_, ?_⟩
  · intro q α
    exact hc.fac (boundaryToCone K p) (op (CostructuredArrow.mk (Y := degree q) α))
  · intro f hf
    apply hc.uniq (boundaryToCone K p) f
    intro a
    exact hf ⟨a.unop.left.obj.len, Nat.lt_succ_of_le a.unop.left.property⟩ a.unop.hom

private def properFaceToBoundary (n : ℕ) :
    SimplicialObject.ProperFaceCategory (n + 1) ⥤ BoundaryIndex n where
  obj a := CostructuredArrow.mk (S := SimplexCategory.Truncated.inclusion n)
    (Y := (⟨a.obj.left, Nat.le_of_lt_succ a.property.1⟩ : SimplexCategory.Truncated n))
    a.obj.hom
  map {a b} f := CostructuredArrow.homMk
    (SimplexCategory.Truncated.Hom.tr f.hom.left
      (Nat.le_of_lt_succ a.property.1) (Nat.le_of_lt_succ b.property.1)) (Over.w f.hom)

private theorem properFaceToBoundary_final (n : ℕ) :
    (properFaceToBoundary n).Final := by
  refine ⟨fun a ↦ ?_⟩
  let r : SimplicialObject.ProperFaceCategory (n + 1) :=
    ⟨Over.mk (image.ι a.hom),
      lt_of_le_of_lt (SimplexCategory.len_le_of_epi (factorThruImage a.hom))
        (Nat.lt_succ_of_le a.left.property),
      SimplexCategory.mono_iff_injective.mp (inferInstance : Mono (image.ι a.hom))⟩
  let u : a ⟶ (properFaceToBoundary n).obj r := CostructuredArrow.homMk
    (SimplexCategory.Truncated.Hom.tr (factorThruImage a.hom) a.left.property
      (Nat.le_of_lt_succ r.property.1)) (image.fac a.hom)
  let z : StructuredArrow a (properFaceToBoundary n) := StructuredArrow.mk u
  have hz : IsInitial z := by
    refine IsInitial.ofUniqueHom (fun b ↦ ?_) (fun b f ↦ ?_)
    · have : Mono b.right.obj.hom :=
        SimplexCategory.mono_iff_injective.mpr b.right.property.2
      let F : MonoFactorisation a.hom :=
        { I := b.right.obj.left
          m := b.right.obj.hom
          e := b.hom.left.hom
          fac := CostructuredArrow.w b.hom }
      let g : r ⟶ b.right := ObjectProperty.homMk
        (Over.homMk (image.lift F) (image.lift_fac F))
      refine StructuredArrow.homMk g ?_
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      exact image.fac_lift F
    · apply StructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      have : Mono b.right.obj.hom :=
        SimplexCategory.mono_iff_injective.mpr b.right.property.2
      apply (cancel_mono b.right.obj.hom).mp
      exact (Over.w f.right.hom).trans (Over.w _).symm
  exact isConnected_of_isInitial _ hz

private theorem isLimit_boundaryToCone {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) n)
    {M : FormalCoproduct.{max u v} D} (c : BoundaryCone K M) (hc : IsMatching K c) :
    Nonempty (IsLimit (boundaryToCone K c)) := by
  classical
  let lift (s : Cone (boundaryDiagram K)) := (hc s.pt (coneToBoundary K s)).choose
  have fac (s : Cone (boundaryDiagram K)) (q : Fin (n + 1))
      (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
      lift s ≫ c.projection q α = (coneToBoundary K s).projection q α :=
    (hc s.pt (coneToBoundary K s)).choose_spec.1 q α
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s a
    exact fac s ⟨a.unop.left.obj.len, Nat.lt_succ_of_le a.unop.left.property⟩ a.unop.hom
  · intro s f hf
    apply (hc s.pt (coneToBoundary K s)).choose_spec.2
    intro q α
    exact hf (op (CostructuredArrow.mk (Y := degree q) α))

private theorem exists_finite_boundary
    {D : Type u} [Category.{v} D] [HasFiniteLimits D] {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) n)
    (hK : ∀ q : Fin (n + 1), Finite (term K q).I) :
    ∃ (M : FormalCoproduct.{max u v} D) (c : BoundaryCone K M),
      Finite M.I ∧ IsMatching K c := by
  have := boundaryIndex_finCategory n
  have : HasFiniteLimits (FormalCoproduct.{max u v} D) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let c := limit.cone (boundaryDiagram K)
  have hc := limit.isLimit (boundaryDiagram K)
  refine ⟨c.pt, coneToBoundary K c, ?_, matching_of_isLimit K c hc⟩
  apply finite_family_limit _ _ c hc
  intro a
  exact hK ⟨a.unop.left.obj.len, Nat.lt_succ_of_le a.unop.left.property⟩

end FormalSplitAttachment

end CategoryTheory

namespace CategoryTheory.FormalSplitAttachment

/-- Include the proper faces of a retained degree into the truncated simplex category.
Source: Stacks Project, Tags 0186 and 0DAV.
(auxiliary; not a blueprint node) -/
def faceInclusion {n : ℕ} (q : Fin (n + 1)) :
    SimplicialObject.ProperFaceCategory q.val ⥤ SimplexCategory.Truncated n where
  obj a := ⟨a.obj.left, Nat.le_trans (Nat.le_of_lt a.property.1)
    (Nat.le_of_lt_succ q.isLt)⟩
  map {a b} f := SimplexCategory.Truncated.Hom.tr f.hom.left
    (Nat.le_trans (Nat.le_of_lt a.property.1) (Nat.le_of_lt_succ q.isLt))
    (Nat.le_trans (Nat.le_of_lt b.property.1) (Nat.le_of_lt_succ q.isLt))

/-- The proper-face diagram of a truncated simplicial object in a retained degree.
Source: Stacks Project, Tags 0186 and 0DAV.
(auxiliary; not a blueprint node) -/
def faceDiagram {D : Type u} [Category.{v} D] {n : ℕ}
    (K : SimplicialObject.Truncated D n) (q : Fin (n + 1)) :
    (SimplicialObject.ProperFaceCategory q.val)ᵒᵖ ⥤ D :=
  (faceInclusion q).op ⋙ K

/-- A finite split truncation with basis components and covering matching maps.
No matching data are required to be chosen coherently between truncations: the universal
property transfers each degree's matching cone when the tower is assembled.
Source: Stacks Project, Tags 0DAV and 01G5.
(auxiliary; not a blueprint node) -/
def IsFiniteBasisTruncation {C : Type u} [Category.{v} C]
    (J : Precoverage C) (B : Set C) (T : C) {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) n) : Prop :=
  IsSplit K ∧ ∀ q : Fin (n + 1),
    Finite (term K q).I ∧
    (∀ i : (term K q).I, ((term K q).obj i).left ∈ B) ∧
    ∃ (M : Cone (faceDiagram K q)) (μ : term K q ⟶ M.pt),
      (q.val = 0 → M.pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T))) ∧
      Nonempty (IsLimit M) ∧
      (∀ a : SimplicialObject.ProperFaceCategory q.val,
        μ ≫ M.π.app (op a) =
          K.map (SimplexCategory.Truncated.Hom.tr a.obj.hom
            (Nat.le_trans (Nat.le_of_lt a.property.1) (Nat.le_of_lt_succ q.isLt))
            (Nat.le_of_lt_succ q.isLt)).op) ∧
      (∀ j : M.pt.I,
        Presieve.ofArrows
          (fun i : {i : (term K q).I // μ.f i = j} ↦ ((term K q).obj i.val).left)
          (fun i : {i : (term K q).I // μ.f i = j} ↦
            (μ.φ i.val).left ≫
              eqToHom (congrArg (fun k ↦ (M.pt.obj k).left) i.property)) ∈
          J (M.pt.obj j).left)

private def FamilyCovers {C : Type u} [Category.{v} C] (J : Precoverage C)
    {T : C} {X Y : FormalCoproduct.{max u v} (Over T)} (f : X ⟶ Y) : Prop :=
  ∀ j : Y.I,
    Presieve.ofArrows
      (fun i : {i : X.I // f.f i = j} ↦ (X.obj i.val).left)
      (fun i : {i : X.I // f.f i = j} ↦ (f.φ i.val).left ≫
        eqToHom (congrArg (fun k ↦ (Y.obj k).left) i.property)) ∈ J (Y.obj j).left

private theorem basis_attached {C : Type u} [Category.{v} C] {B : Set C} {T : C}
    {n : ℕ} (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) n)
    (V : FormalCoproduct.{max u v} (Over T))
    (hK : ∀ (q : Fin (n + 1)) (i : (term K q).I), ((term K q).obj i).left ∈ B)
    (hV : ∀ i : V.I, (V.obj i).left ∈ B)
    {X : FormalCoproduct.{max u v} (Over T)} (t : attachedFamily K V = X) :
    ∀ i : X.I, (X.obj i).left ∈ B := by
  subst X
  intro i
  cases i with
  | inl i => exact hV i
  | inr a => exact hK a.1 a.2.2.val

private theorem covers_attached {C : Type u} [Category.{v} C]
    (J : Precoverage C) (B : Set C)
    (hadjoin : ∀ (T : C) (I : Type (max u v)) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    {T : C} {n : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) n)
    (V : FormalCoproduct.{max u v} (Over T)) [Finite V.I]
    {X M : FormalCoproduct.{max u v} (Over T)} (t : attachedFamily K V = X)
    [Finite X.I] (b : X ⟶ M) (hB : ∀ i : X.I, (X.obj i).left ∈ B)
    (hv : FamilyCovers J (newInclusion K V ≫ eqToHom t ≫ b)) : FamilyCovers J b := by
  subst X
  simp only [eqToHom_refl, Category.id_comp] at hv
  intro j
  apply cover_of_finite_enlargement J B hadjoin (M.obj j).left
    (fun i : {i : V.I // (newInclusion K V ≫ b).f i = j} ↦ (V.obj i.val).left)
    (fun i ↦ ((newInclusion K V ≫ b).φ i.val).left ≫
      eqToHom (congrArg (fun k ↦ (M.obj k).left) i.property))
    (fun i ↦ hB (Sum.inl i.val)) (hv j)
    (fun i : {i : (attachedFamily K V).I // b.f i = j} ↦
      ((attachedFamily K V).obj i.val).left)
    (fun i ↦ (b.φ i.val).left ≫
      eqToHom (congrArg (fun k ↦ (M.obj k).left) i.property))
    (fun i ↦ hB i.val)
  rintro Y f ⟨i⟩
  have h := Presieve.ofArrows.mk
    (Y := fun i : {i : (attachedFamily K V).I // b.f i = j} ↦
      ((attachedFamily K V).obj i.val).left)
    (f := fun i ↦ (b.φ i.val).left ≫
      eqToHom (congrArg (fun k ↦ (M.obj k).left) i.property))
    ⟨Sum.inl i.val, i.property⟩
  simpa [newInclusion] using h

/-- Extend a finite split basis hypercover truncation by one degree.
Source: Stacks Project, Hypercoverings, Tag 0DAV, construction of the extension and
the paragraph proving that the new matching map covers; Tag 01G2, finite limits in SR.
(auxiliary; not a blueprint node)

Proof: Work in C/T, which has terminal object id_T and pullbacks. Finite families have
finite boundary limits: the boundary category of all operators from retained degrees
is finite. The index-set functor preserves terminal objects and pullbacks, hence finite
limits, so the limit M of this diagram has finite index set. Its cone supplies IsMatching.
The proper-face inclusion into this boundary category is final: for any operator, its
injective image factor is an initial object among its factorizations through proper
faces. Restricting the boundary limit along the opposite inclusion therefore gives
the required proper-face matching limit.
For each component of M choose the finite B-cover supplied by hcover; their finite disjoint
union V maps componentwise to M. Apply exists_split_truncated_extension to K, M and V.
The new term is V together with the finitely many old normalized degeneracy copies, so
every component belongs to B and its index set is finite. The supplied boundary map has
the required projections. Its fibre over each matching component consists of the chosen
cover together with finitely many old arrows; apply hadjoin successively to those arrows.
This proves the new matching cover, including empty covers and empty matching families.
The old-degree matching cones and covers transport along the restriction equality, so
all earlier conditions, including the prescribed degree-zero point, are preserved.
-/
theorem exists_finite_basis_truncation_extension
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : Precoverage C)
    (B : Set C)
    (hcover : ∀ T : C, ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ T),
      Finite I ∧ (∀ i : I, U i ∈ B) ∧ Presieve.ofArrows U f ∈ J T)
    (hadjoin : ∀ (T : C) (I : Type (max u v)) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) (n : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) n)
    (hK : IsFiniteBasisTruncation J B T K) :
    ∃ L : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) (n + 1),
      (SimplicialObject.Truncated.trunc _ (n + 1) n).obj L = K ∧
        IsFiniteBasisTruncation J B T L := by
  classical
  have : HasFiniteLimits (Over T) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨M, c, hM, hc⟩ := exists_finite_boundary K (fun q ↦ (hK.2 q).1)
  have : Finite M.I := hM
  choose I U f hI hB hf using fun j : M.I ↦ hcover (M.obj j).left
  let V : FormalCoproduct.{max u v} (Over T) :=
    ⟨Σ j : M.I, I j, fun p ↦ Over.mk (f p.1 p.2 ≫ (M.obj p.1).hom)⟩
  let v : V ⟶ M := ⟨Sigma.fst, fun p ↦ Over.homMk (f p.1 p.2) rfl⟩
  have : Finite V.I := inferInstance
  have hVB (i : V.I) : (V.obj i).left ∈ B := hB i.1 i.2
  have hv : FamilyCovers J v := by
    intro j
    have he : Presieve.ofArrows
        (fun i : {i : V.I // v.f i = j} ↦ (V.obj i.val).left)
        (fun i : {i : V.I // v.f i = j} ↦ (v.φ i.val).left ≫
          eqToHom (congrArg (fun k ↦ (M.obj k).left) i.property)) =
        Presieve.ofArrows (U j) (f j) := by
      apply le_antisymm
      · rintro W g ⟨⟨⟨j', i⟩, hi⟩⟩
        change j' = j at hi
        subst j'
        simpa [v] using (Presieve.ofArrows.mk (Y := U j) (f := f j) i)
      · rintro W g ⟨i⟩
        have h := Presieve.ofArrows.mk
          (Y := fun i : {i : V.I // v.f i = j} ↦ (V.obj i.val).left)
          (f := fun i : {i : V.I // v.f i = j} ↦ (v.φ i.val).left ≫
            eqToHom (congrArg (fun k ↦ (M.obj k).left) i.property))
          ⟨⟨j, i⟩, rfl⟩
        simpa [v] using h
    rw [he]
    exact hf j
  obtain ⟨L, e, t, b, hsplit, hfinite, hnondeg, hproj, hnew, hold⟩ :=
    exists_split_truncated_extension K (fun q ↦ (hK.2 q).1) hK.1 c hc V v
  refine ⟨L, e, hsplit, ?_⟩
  have hmem (q : Fin (n + 2)) (i : (term L q).I) : ((term L q).obj i).left ∈ B := by
    by_cases hq : q.val < n + 1
    · let q' : Fin (n + 1) := ⟨q.val, hq⟩
      have ht : term K q' = term L q :=
        (Functor.congr_obj e (op (degree q'))).symm
      have hm := (hK.2 q').2.1
      rw [ht] at hm
      exact hm i
    · have hq' : q = ⟨n + 1, Nat.lt_succ_self _⟩ := by
        apply Fin.ext
        dsimp
        have hlt := q.isLt
        omega
      subst q
      exact basis_attached K V (fun q i ↦ (hK.2 q).2.1 i) hVB t i
  have hb : FamilyCovers J b := by
    have hbase : FamilyCovers J (newInclusion K V ≫ eqToHom t ≫ b) := by
      rw [hnew]
      exact hv
    have : Finite (term L ⟨n + 1, Nat.lt_succ_self _⟩).I := hfinite _
    exact covers_attached J B hadjoin K V t b (hmem _) hbase
  subst K
  intro q
  by_cases hq : q.val < n + 1
  · exact (hK.2 ⟨q.val, hq⟩)
  · have hq' : q = ⟨n + 1, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      have hlt := q.isLt
      omega
    subst q
    refine ⟨hfinite _, hmem _ , ?_⟩
    have hf := properFaceToBoundary_final n
    obtain ⟨hlim⟩ := isLimit_boundaryToCone _ c hc
    let P := (boundaryToCone _ c).whisker (properFaceToBoundary n).op
    have hP : Nonempty (IsLimit P) :=
      ⟨(Functor.Initial.isLimitWhiskerEquiv (properFaceToBoundary n).op _).symm hlim⟩
    refine ⟨P, b, ?_, hP, ?_, hb⟩
    · intro h
      omega
    · intro a
      have h := hproj ⟨a.obj.left.len, a.property.1⟩ a.obj.hom
      exact h.trans (Category.comp_id _)

end CategoryTheory.FormalSplitAttachment
