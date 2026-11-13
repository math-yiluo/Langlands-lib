import Langlands.Cohomology.AbelianSheafPullbackComposition
import Langlands.AlgebraicGeometry.Picard.UnitH1MorphismPullback
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction

/-! # Square-zero unit boundaries under a morphism of thickenings -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismObstructionNaturality

open NilpotentUnitReduction SquareZeroUnitKernels StructureKernelModule
open SquareZeroUnitExactSequence SquareZeroUnitCohomology UnitSheafPushforward
open Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic
open Langlands.Cohomology AbelianSheafCohomologyPullback AbelianSheafH1Pullback
open AbelianSheafPullbackComposition UnitCechH1Comparison
open Langlands.Scheme.Modules
open Langlands.SchemeModule

lemma unitsReduction_comp {A B C : Scheme.{u}} (a : B ⟶ A) (b : C ⟶ B) :
    unitsReduction a ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} a.base).map
        (unitsReduction b) = unitsReduction (b ≫ a) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro x
  rfl

lemma unitsReduction_congr {A B : Scheme.{u}} (a b : B ⟶ A) (h : a = b) :
    unitsReduction a ≫ eqToHom
        (congrArg (fun t : B ⟶ A =>
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} t.base).obj (unitSheaf B)) h) =
      unitsReduction b := by
  subst b
  simp

lemma pushforwardMap_congr {A B : Scheme.{u}} (a b : B ⟶ A) (h : a = b)
    {F : A.toTopCat.Sheaf AddCommGrpCat.{u}} {G : B.toTopCat.Sheaf AddCommGrpCat.{u}}
    (k : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} a.base).obj G)
    (n : ℕ) (x : Sheaf.H.{u} F n) :
    pushforwardMap b.base
        (k ≫ eqToHom (congrArg (fun t : B ⟶ A =>
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} t.base).obj G) h)) n x =
      pushforwardMap a.base k n x := by
  subst b
  simp

variable {X X' Y Y' : Scheme.{u}} (f : X' ⟶ X)
  (i : Y ⟶ X) (i' : Y' ⟶ X') (g : Y' ⟶ Y) (w : i' ≫ f = g ≫ i)

/-- The actual quotient-unit arrow, transported along the commuting square. -/
def sequenceQuotientMap :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction g) ≫
    eqToHom (congrArg (fun t : Y' ⟶ X =>
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} t.base).obj (unitSheaf Y')) w.symm)

lemma sequenceQuotientMap_comm :
    unitsReduction f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).map (unitsReduction i') =
      unitsReduction i ≫ sequenceQuotientMap f i i' g w := by
  rw [unitsReduction_comp]
  dsimp only [sequenceQuotientMap]
  rw [← Category.assoc, unitsReduction_comp]
  exact (unitsReduction_congr (g ≫ i) (i' ≫ f) w.symm).symm

variable [IsClosedImmersion i] [IsClosedImmersion i']
  (hi : i.ker ^ 2 = ⊥) (hi' : i'.ker ^ 2 = ⊥)
  (k : kernelModule i ⟶ (Scheme.Modules.pushforward f).obj (kernelModule i'))
  (hk : k ≫ (Scheme.Modules.pushforward f).map (kernelModuleι i') =
    kernelModuleι i ≫ unitToPushforwardUnit f)

include hk in
lemma sequenceKernelMap_comm :
    (toAbSheaf X).map k ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).map (schemeOneAdd i' hi') =
      schemeOneAdd i hi ≫ unitsReduction f := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.toMul.injective
  apply Units.ext
  have ha := congrArg (fun q : kernelModule i ⟶
    (Scheme.Modules.pushforward f).obj (structureModule X') => q.app U.unop a) hk
  change (k.app U.unop a).val = (f.app U.unop).hom a.val at ha
  change 1 + (k.app U.unop a).val = (f.app U.unop).hom (1 + a.val)
  rw [ha, map_add, map_one]

/-- The actual morphism of unit sequences for a morphism of square-zero thickenings. -/
def unitSequenceMap : schemeUnitSequence i hi ⟶
    (schemeUnitSequence i' hi').map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base) :=
  ShortComplex.homMk ((toAbSheaf X).map k) (unitsReduction f)
    (sequenceQuotientMap f i i' g w) (sequenceKernelMap_comm f i i' hi hi' k hk)
    (sequenceQuotientMap_comm f i i' g w)

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
lemma quotientPushforwardMap_comp (n : ℕ)
    (a : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y)) n) :
    pushforwardMap i'.base (B := unitSheaf Y') (𝟙 _) n
        (pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a) =
      pushforwardMap g.base (B := unitSheaf Y') (unitsReduction g) n (pushforwardMap i.base (B := unitSheaf Y) (𝟙 _) n a) := by
  have h₁ := pushforwardMap_comp f.base i'.base n
    (A := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y))
    (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y'))
    (C := unitSheaf Y') (sequenceQuotientMap f i i' g w) (𝟙 _) a
  have hc₁ : compositeCoefficientMap f.base i'.base
      (sequenceQuotientMap f i i' g w) (𝟙 _) = sequenceQuotientMap f i i' g w := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro x
    rfl
  rw [hc₁] at h₁
  have h₂ := pushforwardMap_comp i.base g.base n
    (A := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y))
    (B := unitSheaf Y) (C := unitSheaf Y') (𝟙 _) (unitsReduction g) a
  have hc₂ : compositeCoefficientMap i.base g.base
      (A := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y))
      (B := unitSheaf Y) (C := unitSheaf Y') (𝟙 _) (unitsReduction g) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction g) := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro x
    rfl
  rw [hc₂] at h₂
  calc
    _ = pushforwardMap (i'.base ≫ f.base) (B := unitSheaf Y') (sequenceQuotientMap f i i' g w) n a := h₁
    _ = pushforwardMap (g.base ≫ i.base) (B := unitSheaf Y')
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction g)) n a :=
      pushforwardMap_congr (g ≫ i) (i' ≫ f) w.symm
        (F := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y))
        (G := unitSheaf Y')
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction g)) n a
    _ = pushforwardMap g.base (B := unitSheaf Y') (unitsReduction g) n
        (pushforwardMap i.base (B := unitSheaf Y) (𝟙 _) n a) := h₂.symm

/-- The quotient arrow induces the actual pullback on unit cohomology in every degree. -/
lemma quotientCohomologyComparison (n : ℕ)
    (a : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (unitSheaf Y)) n) :
    nilpotentUnitsCohomologyPushforwardEquiv i' ⟨2, hi'⟩ n
        (pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a) =
      UnitH1MorphismPullback.cohomologyMap g n
        (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n a) := by
  have h₁ := pushforwardMap_id_eq_equiv (nilpotentClosedImmersionTopIso i' ⟨2, hi'⟩)
    n (unitSheaf Y') (pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a)
  have h₂ := pushforwardMap_id_eq_equiv (nilpotentClosedImmersionTopIso i ⟨2, hi⟩)
    n (unitSheaf Y) a
  change pushforwardMap i'.base (B := unitSheaf Y') (𝟙 _) n
      (pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a) =
    nilpotentUnitsCohomologyPushforwardEquiv i' ⟨2, hi'⟩ n
      (pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a) at h₁
  change pushforwardMap i.base (B := unitSheaf Y) (𝟙 _) n a =
    nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n a at h₂
  change _ = pushforwardMap g.base (B := unitSheaf Y') (unitsReduction g) n
    (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n a)
  rw [← h₁, ← h₂]
  exact quotientPushforwardMap_comp f i i' g w n a

/-- Actual ideal cohomology transported by the direct-image kernel coefficient arrow. -/
def idealCohomologyMap (n : ℕ) : idealCohomology i n →+ idealCohomology i' n :=
  (idealCohomologyAddEquiv i' n).toAddMonoidHom.comp
    ((pushforwardMap f.base ((toAbSheaf X).map k) n).comp
      (idealCohomologyAddEquiv i n).symm.toAddMonoidHom)

include w hk in
/-- Naturality of the actual square-zero boundary under a morphism of thickenings. -/
lemma boundaryMap_naturality (n : ℕ) (y : unitCohomology Y n) :
    boundaryMap i' hi' n (UnitH1MorphismPullback.cohomologyMap g n y) =
      idealCohomologyMap f i i' k (n + 1) (boundaryMap i hi n y) := by
  let a := (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y
  have hq : pushforwardMap f.base (B := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i'.base).obj (unitSheaf Y')) (sequenceQuotientMap f i i' g w) n a =
      (nilpotentUnitsCohomologyPushforwardEquiv i' ⟨2, hi'⟩ n).symm
        (UnitH1MorphismPullback.cohomologyMap g n y) := by
    apply (nilpotentUnitsCohomologyPushforwardEquiv i' ⟨2, hi'⟩ n).injective
    simpa only [a, AddEquiv.apply_symm_apply] using
      quotientCohomologyComparison f i i' g w hi hi' n a
  have hd := pushforwardMap_δ f.base
    (schemeUnitSequence_shortExact i hi) (schemeUnitSequence_shortExact i' hi')
    (unitSequenceMap f i i' g w hi hi' k hk) n (n + 1) rfl a
  change idealCohomologyAddEquiv i' (n + 1)
      (Sheaf.H.δ (schemeUnitSequence_shortExact i' hi') n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i' ⟨2, hi'⟩ n).symm
          (UnitH1MorphismPullback.cohomologyMap g n y))) =
    idealCohomologyAddEquiv i' (n + 1)
      (pushforwardMap f.base ((toAbSheaf X).map k) (n + 1)
        ((idealCohomologyAddEquiv i (n + 1)).symm
          (idealCohomologyAddEquiv i (n + 1)
            (Sheaf.H.δ (schemeUnitSequence_shortExact i hi) n (n + 1) rfl a))))
  rw [AddEquiv.symm_apply_apply, ← hq]
  exact congrArg (idealCohomologyAddEquiv i' (n + 1)) hd.symm

variable [CompactSpace Y] [CompactSpace Y']

include w hk in
/-- The actual Picard obstruction commutes with the actual sheaf-cohomology kernel map. -/
lemma obstructionMap_naturality (y : Group Y) :
    SquareZeroPicardObstruction.obstructionMap i' hi' (Group.pullback g y) =
      idealCohomologyMap f i i' k 2 (SquareZeroPicardObstruction.obstructionMap i hi y) := by
  change boundaryMap i' hi' 1 (Group.unitCohomologyAddEquiv Y' (Group.pullback g y)) = _
  rw [Group.unitCohomologyAddEquiv_pullback_morphism]
  exact boundaryMap_naturality f i i' g w hi hi' k hk 1 _

end Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismObstructionNaturality
