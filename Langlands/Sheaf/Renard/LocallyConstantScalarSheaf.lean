import Langlands.Sheaf.Renard.LocallyConstantScalarPresheaf
import Langlands.Sheaf.Renard.GermSectionSheaf
import Langlands.Sheaf.Equivariant.LocallyConstant

/-! # Intrinsic locally constant scalar sheaves on every chosen basis -/

open CategoryTheory Opposite TopologicalSpace

universe u r w

namespace Langlands.Sheaf.Renard.LocallyConstantScalar

variable {X : Type u} [TopologicalSpace X]

/-- Literal compatibility identifies actual values by refining the open overlap. -/
theorem compatible_value (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} (U : ι → BasisOpen B)
    (s : ∀ i, Sections (rawPresheaf B R) (U i))
    (hs : Compatible (rawPresheaf B R) U s) (i j : ι)
    (x : X) (hxi : x ∈ (U i).obj) (hxj : x ∈ (U j).obj) :
    (s i).toFun ⟨x, hxi⟩ = (s j).toFun ⟨x, hxj⟩ := by
  obtain ⟨W, hxW, hW⟩ := B.exists_subset ((U i).obj ⊓ (U j).obj) ⟨hxi, hxj⟩
  exact congrArg (fun z : LocallyConstant W.obj R => z ⟨x, hxW⟩)
    (hs i j W (hW.trans inf_le_left) (hW.trans inf_le_right))

/-- Choose a cover member at each actual point of the covered open. -/
noncomputable def glueFunction (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (rawPresheaf B R) (U i)) : V.obj → R :=
  fun x => (s (Classical.choose (hU.2 x.val x.property))).toFun
    ⟨x.val, Classical.choose_spec (hU.2 x.val x.property)⟩

/-- The chosen pointwise function agrees with each original cover member. -/
theorem glueFunction_eq (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (rawPresheaf B R) (U i))
    (hs : Compatible (rawPresheaf B R) U s) (i : ι)
    (x : V.obj) (hxi : x.val ∈ (U i).obj) :
    glueFunction B R hU s x = (s i).toFun ⟨x.val, hxi⟩ :=
  compatible_value B R U s hs (Classical.choose (hU.2 x.val x.property)) i x.val
    (Classical.choose_spec (hU.2 x.val x.property)) hxi

/-- Reuse the generic local-constancy predicate on the actual cover members. -/
theorem glueFunction_isLocallyConstant (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (rawPresheaf B R) (U i))
    (hs : Compatible (rawPresheaf B R) U s) :
    IsLocallyConstant (glueFunction B R hU s) := by
  apply (Langlands.Sheaf.Equivariant.LocallyConstantSheaf.localPredicate X R).locality
    (glueFunction B R hU s)
  intro x
  obtain ⟨i, hxi⟩ := hU.2 x.val x.property
  refine ⟨(U i).obj, hxi, homOfLE (hU.1 i), ?_⟩
  change IsLocallyConstant (fun y : (U i).obj =>
    glueFunction B R hU s ⟨y.val, hU.1 i y.property⟩)
  have heq : (fun y : (U i).obj =>
      glueFunction B R hU s ⟨y.val, hU.1 i y.property⟩) = (s i).toFun := by
    funext y
    exact glueFunction_eq B R hU s hs i ⟨y.val, hU.1 i y.property⟩ y.property
  rw [heq]
  exact (s i).isLocallyConstant

/-- The actual locally constant amalgamation, without an input gluing assumption. -/
noncomputable def glue (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (rawPresheaf B R) (U i))
    (hs : Compatible (rawPresheaf B R) U s) : LocallyConstant V.obj R :=
  ⟨glueFunction B R hU s, glueFunction_isLocallyConstant B R hU s hs⟩

/-- Restriction equations hold on every member of the original indexed cover. -/
theorem glue_restrict (B : OpenBasis X) (R : Type r) [Ring R]
    {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (rawPresheaf B R) (U i))
    (hs : Compatible (rawPresheaf B R) U s) (i : ι) :
    restrict R (hU.1 i) (glue B R hU s hs) = s i := by
  apply LocallyConstant.ext
  intro x
  exact glueFunction_eq B R hU s hs i ⟨x.val, hU.1 i x.property⟩ x.property

/-- Intrinsic unique gluing holds for every independently sized indexed cover. -/
theorem familySheafCondition (B : OpenBasis X) (R : Type r) [Ring R] :
    FamilySheafCondition.{u,max u r,w} (rawPresheaf B R) := by
  intro ι V U hU s hs
  refine ⟨glue B R hU s hs, fun i => glue_restrict B R hU s hs i, ?_⟩
  intro t ht
  apply LocallyConstant.ext
  intro x
  obtain ⟨i, hxi⟩ := hU.2 x.val x.property
  have heq := congrArg (fun z : LocallyConstant (U i).obj R => z ⟨x.val, hxi⟩) (ht i)
  exact heq.trans (glueFunction_eq B R hU s hs i x hxi).symm

/-- This is the literal published intrinsic set-cover sheaf condition. -/
theorem sheafCondition (B : OpenBasis X) (R : Type r) [Ring R] :
    SheafCondition (rawPresheaf B R) :=
  FamilySheafCondition.sheafCondition (rawPresheaf B R) (familySheafCondition B R)

/-- Empty-cover gluing gives the published normalization, retaining empty opens. -/
theorem isNormalized (B : OpenBasis X) (R : Type r) [Ring R] :
    IsNormalized (rawPresheaf B R) :=
  SheafCondition.isNormalized (rawPresheaf B R) (sheafCondition B R)

/-- The actual normalized underlying abelian presheaf on the chosen basis. -/
def normalizedPresheaf (B : OpenBasis X) (R : Type r) [Ring R] :
    Presheaf.{u,max u r} B :=
  ⟨rawPresheaf B R, isNormalized B R⟩

/-- An intrinsic scalar sheaf package: the actual abelian sheaf underlying the ring presheaf. -/
def basisSheaf (B : OpenBasis X) (R : Type r) [Ring R] : BasisSheaf.{u,max u r} B :=
  ⟨normalizedPresheaf B R, sheafCondition B R⟩

/-- The forgetful identification is literal equality of the underlying functors. -/
theorem basisSheaf_forget (B : OpenBasis X) (R : Type r) [Ring R] :
    (basisSheaf B R).obj.obj = basisRingPresheaf B R ⋙ forget₂ RingCat AddCommGrpCat := rfl

/-- The published canonical basis of all actual opens gives the all-open scalar sheaf. -/
def allOpenSheaf (X : Type u) [TopologicalSpace X] (R : Type r) [Ring R] :
    BasisSheaf.{u,max u r} (allOpenBasis X) :=
  basisSheaf (allOpenBasis X) R

@[simp]
theorem allOpenSheaf_sections (R : Type r) [Ring R] (U : Opens X) :
    Sections (allOpenSheaf X R).obj.obj (allOpen U) =
      AddCommGrpCat.of (LocallyConstant U R) := rfl

@[simp]
theorem allOpenSheaf_restriction (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V) :
    (restriction (allOpenSheaf X R).obj.obj (U := allOpen U) (V := allOpen V) h).hom =
      (restrict R h).toAddMonoidHom := rfl

/-- The canonical lift of actual opens to the published all-open basis category. -/
def allOpenFunctor (X : Type u) [TopologicalSpace X] : Opens X ⥤ BasisOpen (allOpenBasis X) where
  obj := allOpen
  map f := basisHom f.le

/-- The all-open basis ring presheaf identifies with the original ring presheaf by identity maps. -/
def allOpenRingPresheafIso (X : Type u) [TopologicalSpace X] (R : Type r) [Ring R] :
    (allOpenFunctor X).op ⋙ basisRingPresheaf (allOpenBasis X) R ≅ ringPresheaf X R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V f; rfl)

/-- Unique gluing on actual opens, with explicit restriction equations on the original family. -/
theorem allOpen_unique_gluing (R : Type r) [Ring R] {ι : Type w}
    (V : Opens X) (U : ι → Opens X)
    (hU : (∀ i, U i ≤ V) ∧ ∀ x ∈ V, ∃ i, x ∈ U i)
    (s : ∀ i, LocallyConstant (U i) R)
    (hs : Compatible (rawPresheaf (allOpenBasis X) R) (fun i => allOpen (U i)) s) :
    ∃! t : LocallyConstant V R, ∀ i, restrict R (hU.1 i) t = s i :=
  familySheafCondition (allOpenBasis X) R ι (allOpen V) (fun i => allOpen (U i)) hU s hs

end Langlands.Sheaf.Renard.LocallyConstantScalar
