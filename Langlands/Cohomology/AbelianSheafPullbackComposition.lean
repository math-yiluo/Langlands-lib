import Langlands.Cohomology.AbelianSheafH1Pullback

/-! # Composition and homeomorphism normalization of sheaf-cohomology pullback -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafPullbackComposition

open AbelianSheafCohomologyPullback AbelianSheafH1Pullback
open Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Z ⟶ X)

/-- Compose coefficient arrows in the direct-image convention. -/
def compositeCoefficientMap {A : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}} {C : Z.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (l : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj C) :
    A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (g ≫ f)).obj C :=
  k ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map l

/-- Cohomology pullbacks compose with the actual composite coefficient arrow. -/
lemma pushforwardMap_comp (n : ℕ)
    {A : Y.Sheaf AddCommGrpCat.{u}} {B : X.Sheaf AddCommGrpCat.{u}}
    {C : Z.Sheaf AddCommGrpCat.{u}}
    (k : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (l : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj C)
    (x : Sheaf.H.{u} A n) :
    pushforwardMap g l n (pushforwardMap f k n x) =
      pushforwardMap (g ≫ f) (compositeCoefficientMap f g k l) n x := by
  induction n generalizing A B C with
  | zero =>
    apply (Sheaf.H.equiv₀ C (isTerminalTop (α := Opens Z))).injective
    rw [pushforwardMap_equiv₀, pushforwardMap_equiv₀, pushforwardMap_equiv₀]
    rfl
  | succ n ih =>
    let S := AbelianSheafFlasque.injectiveSc A
    let T := AbelianSheafFlasque.injectiveSc B
    let V := AbelianSheafFlasque.injectiveSc C
    have hS := AbelianSheafFlasque.injectiveSc_shortExact A
    have hT := AbelianSheafFlasque.injectiveSc_shortExact B
    have hV := AbelianSheafFlasque.injectiveSc_shortExact C
    let φ := injectiveScPushforwardMap f k
    let ψ := injectiveScPushforwardMap g l
    let χ : S ⟶ V.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (g ≫ f)) :=
      φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapShortComplex.map ψ
    have hx : Sheaf.H.map S.f (n + 1) x = 0 := Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₁ hS x hx rfl
    rw [← ha]
    change pushforwardMap g ψ.τ₁ (n + 1)
        (pushforwardMap f φ.τ₁ (n + 1) (Sheaf.H.δ hS n (n + 1) rfl a)) =
      pushforwardMap (g ≫ f) χ.τ₁ (n + 1) (Sheaf.H.δ hS n (n + 1) rfl a)
    rw [pushforwardMap_δ f hS hT φ, pushforwardMap_δ g hT hV ψ,
      pushforwardMap_δ (g ≫ f) hS hV χ]
    exact congrArg (Sheaf.H.δ hV n (n + 1) rfl) (ih φ.τ₃ ψ.τ₃ a)

variable (e : X ≅ Y)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

/-- The general pullback is the published cohomology equivalence for a homeomorphism. -/
lemma pushforwardMap_id_eq_equiv (n : ℕ) (B : X.Sheaf AddCommGrpCat.{u})
    (x : Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj B) n) :
    pushforwardMap e.hom (𝟙 _) n x = cohomologyPushforwardEquiv e B n x := by
  induction n generalizing B with
  | zero =>
    apply (Sheaf.H.equiv₀ B (isTerminalTop (α := Opens X))).injective
    rw [pushforwardMap_id_equiv₀, cohomologyPushforwardEquiv_equiv₀]
  | succ n ih =>
    let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom
    let S := AbelianSheafFlasque.injectiveSc B
    have hS := AbelianSheafFlasque.injectiveSc_shortExact B
    let φ : S.map P ⟶ S.map P := 𝟙 _
    have : Injective (S.map P).X₂ := by
      change Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj
        (Injective.under B))
      infer_instance
    have hx : Sheaf.H.map (S.map P).f (n + 1) x = 0 := Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₁ (hS.map_of_exact P) x hx rfl
    rw [← ha]
    change pushforwardMap e.hom φ.τ₁ (n + 1)
        (Sheaf.H.δ (hS.map_of_exact P) n (n + 1) rfl a) = _
    rw [pushforwardMap_δ e.hom (hS.map_of_exact P) hS φ,
      cohomologyPushforwardEquiv_δ e hS]
    exact congrArg (Sheaf.H.δ hS n (n + 1) rfl) (ih S.X₃ a)

end Langlands.Cohomology.AbelianSheafPullbackComposition
