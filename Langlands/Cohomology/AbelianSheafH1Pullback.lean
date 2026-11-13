import Langlands.Cohomology.AbelianSheafCohomologyPullback
import Langlands.Cohomology.AbelianSheafH1Pushforward

/-! # Arbitrary-map compatibility of the Čech-to-H¹ comparison -/

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafH1Pullback

open Cech AbelianSheafCechH1 AbelianSheafH1Naturality
open AbelianSheafCohomologyPullback AbelianSheafH1Pushforward

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private lemma homEquiv_uniq_inv_comp
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R)
    {A : C} {B : D} (f : L.obj A ⟶ B) :
    b.homEquiv _ _ ((a.leftAdjointUniq b).inv.app A ≫ f) =
      a.homEquiv _ _ f := by
  simp only [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

lemma pushforwardMap_factor {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (n : ℕ) (x : Sheaf.H.{u} A n) :
    pushforwardMap f k n x =
      pushforwardMap f (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)) n
        (Sheaf.H.map k n x) := by
  unfold pushforwardMap
  rw [pullbackMap_naturality_left,
    ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id]

lemma pushforwardMap_id_equiv₀ (B : X.Sheaf AddCommGrpCat.{u})
    (x : Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) 0) :
    Sheaf.H.equiv₀ B (isTerminalTop (α := Opens X))
        (pushforwardMap f (𝟙 _) 0 x) =
      Sheaf.H.equiv₀ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
        (isTerminalTop (α := Opens Y)) x := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)).2 x
  simp only [pushforwardMap, pullbackMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens X))).homEquiv _ _
          ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
              _ _).symm a)) =
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens Y))).homEquiv _ _ a)
  apply congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have hh := homEquiv_uniq_inv_comp
      ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens Y))).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f))
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens X)))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
        _ _).symm a)
  rw [Adjunction.comp_homEquiv] at hh
  change (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X))).homEquiv _ _
        ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
            _ _).symm a) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens Y))).homEquiv _ _
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
            _ _).symm a)) at hh
  simpa only [Equiv.apply_symm_apply] using hh

lemma pushforwardMap_equiv₀ {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (x : Sheaf.H.{u} A 0) :
    Sheaf.H.equiv₀ B (isTerminalTop (α := Opens X)) (pushforwardMap f k 0 x) =
      k.hom.app (op ⊤) (Sheaf.H.equiv₀ A (isTerminalTop (α := Opens Y)) x) := by
  rw [pushforwardMap_factor, pushforwardMap_id_equiv₀, ← Sheaf.H.equiv₀_naturality]

lemma pushforwardMap_equiv₀_symm {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (s : A.obj.obj (op ⊤)) :
    pushforwardMap f k 0 ((Sheaf.H.equiv₀ A (isTerminalTop (α := Opens Y))).symm s) =
      (Sheaf.H.equiv₀ B (isTerminalTop (α := Opens X))).symm (k.hom.app (op ⊤) s) := by
  apply (Sheaf.H.equiv₀ B (isTerminalTop (α := Opens X))).injective
  rw [pushforwardMap_equiv₀, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Adjoint the components of a map into a pushed short complex. -/
def adjointComplexMap
    {S : ShortComplex (Y.Sheaf AddCommGrpCat.{u})}
    {T : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (φ : S ⟶ T.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)) :
    S.map (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) ⟶ T where
  τ₁ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
    _ _).symm φ.τ₁
  τ₂ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
    _ _).symm φ.τ₂
  τ₃ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
    _ _).symm φ.τ₃
  comm₁₂ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv_naturality_right_square S.f φ.τ₂ φ.τ₁ T.f φ.comm₁₂.symm).symm
  comm₂₃ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv_naturality_right_square S.g φ.τ₃ φ.τ₂ T.g φ.comm₂₃.symm).symm

/-- Connecting maps commute with the direct-image coefficient convention. -/
lemma pushforwardMap_δ
    {S : ShortComplex (Y.Sheaf AddCommGrpCat.{u})}
    {T : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    (n m : ℕ) (h : n + 1 = m) (x : Sheaf.H.{u} S.X₃ n) :
    pushforwardMap f φ.τ₁ m (Sheaf.H.δ hS n m h x) =
      Sheaf.H.δ hT n m h (pushforwardMap f φ.τ₃ n x) :=
  pullbackMap_δ f hS hT (adjointComplexMap f φ) n m h x

section Representatives

variable {ι : Type w} {U : ι → Opens Y}
  {S : ShortComplex (Y.Sheaf AddCommGrpCat.{u})}
  {T : ShortComplex (X.Sheaf AddCommGrpCat.{u})}

/-- Map a representative into a pushed short complex and then to the preimage cover. -/
def transportRepresentative
    (φ : S ⟶ T.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    {z : C S.X₁.1 U 1} (r : Representative (S := S) z) :
    Representative (S := T)
      (CechPullback.cochains f T.X₁.1 U 1 (map U φ.τ₁.hom 1 z)) :=
  AbelianSheafH1Pushforward.transportRepresentative f (mapRepresentative φ r)

/-- Transport takes the value of a representative to its cohomological pullback. -/
lemma transportRepresentative_value (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    {z : C S.X₁.1 U 1} (r : Representative (S := S) z) :
    (transportRepresentative f φ r).value hT =
      pushforwardMap f φ.τ₁ 1 (r.value hS) := by
  unfold Representative.value
  rw [pushforwardMap_δ f hS hT φ, pushforwardMap_equiv₀_symm]
  rfl

end Representatives

local instance pushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

/-- Extend a coefficient arrow to the chosen injective sequences. -/
def injectiveScPushforwardMap {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) :
    AbelianSheafFlasque.injectiveSc A ⟶
      (AbelianSheafFlasque.injectiveSc B).map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  let ψ := Injective.factorThru (k ≫ P.map (Injective.ι B)) (Injective.ι A)
  have hψ : Injective.ι A ≫ ψ = k ≫ P.map (Injective.ι B) :=
    Injective.comp_factorThru _ _
  have hz : Injective.ι A ≫ (ψ ≫ P.map (cokernel.π (Injective.ι B))) = 0 := by
    rw [← Category.assoc, hψ, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero]
  exact
    { τ₁ := k
      τ₂ := ψ
      τ₃ := cokernel.desc _ _ hz
      comm₁₂ := hψ.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }

@[simp]
lemma injectiveScPushforwardMap_τ₁ {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) :
    (injectiveScPushforwardMap f k).τ₁ = k := rfl

/-- The finite-cover Čech-to-H¹ comparison commutes with arbitrary continuous pullback. -/
theorem comparisonHom_pullback {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    {ι : Type w} [Finite ι] (U : ι → Opens Y) (hcov : ⊤ ≤ iSup U)
    (x : CechH1 A.1 U) :
    comparisonHom B (fun i => (Opens.map f).obj (U i))
        (preimage_fullCover f U hcov)
        (CechPullback.h1Equiv f B.1 U (mapHom U k.hom x)) =
      pushforwardMap f k 1 (comparisonHom A U hcov x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let : TopCat.Sheaf.IsFlasque (Injective.under A) :=
      AbelianSheafFlasque.isFlasque_of_injective (Injective.under A)
    let r := chosenRepresentative (S := AbelianSheafFlasque.injectiveSc A) hcov z
    rw [mapHom_mk, CechPullback.h1Equiv_mk]
    rw [comparisonHom_eq_value _ _ _ _
      (transportRepresentative f (injectiveScPushforwardMap f k) r),
      comparisonHom_eq_value _ _ _ _ r]
    exact transportRepresentative_value f (AbelianSheafFlasque.injectiveSc_shortExact A)
      (AbelianSheafFlasque.injectiveSc_shortExact B) (injectiveScPushforwardMap f k) r

end Langlands.Cohomology.AbelianSheafH1Pullback

