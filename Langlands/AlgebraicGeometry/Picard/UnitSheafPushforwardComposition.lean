import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardNaturality
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Composition of actual sheaf cohomology pushforward -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

namespace Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

variable {X Y Z : TopCat.{u}} (e : X ≅ Y) (f : Y ≅ Z)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) f).isEquivalence_functor

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (e ≪≫ f).hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) (e ≪≫ f)).isEquivalence_functor

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (e ≪≫ f).hom).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The successive published comparisons along two homeomorphisms. -/
def cohomologyPushforwardCompositeEquiv (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)) n ≃+
      Sheaf.H.{u} F n :=
  (cohomologyPushforwardEquiv f
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n).trans
      (cohomologyPushforwardEquiv e F n)

/-- The published pushforward comparisons compose in every cohomological degree. -/
lemma cohomologyPushforwardEquiv_comp (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)) n) :
    cohomologyPushforwardEquiv e F n
        (cohomologyPushforwardEquiv f
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n x) =
      cohomologyPushforwardEquiv (e ≪≫ f) F n x := by
  induction n generalizing F with
  | zero =>
    apply (Sheaf.H.equiv₀ F (isTerminalTop (α := Opens X))).injective
    rw [cohomologyPushforwardEquiv_equiv₀, cohomologyPushforwardEquiv_equiv₀,
      cohomologyPushforwardEquiv_equiv₀]
    rfl
  | succ n ih =>
    let Pe := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom
    let Pf := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom
    let P := Pe ⋙ Pf
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    have : Injective (S.map P).X₂ := by
      change Injective
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj
            (Injective.under F)))
      infer_instance
    have hx : Sheaf.H.map (S.map P).f (n + 1) x = 0 :=
      Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₁ (hS.map_of_exact P) x hx rfl
    rw [← ha]
    have hδf := cohomologyPushforwardEquiv_δ f (hS.map_of_exact Pe)
      n (n + 1) rfl a
    calc
      _ = cohomologyPushforwardEquiv e F (n + 1)
          (Sheaf.H.δ (hS.map_of_exact Pe) n (n + 1) rfl
            (cohomologyPushforwardEquiv f (Pe.obj S.X₃) n a)) :=
        congrArg (cohomologyPushforwardEquiv e F (n + 1)) hδf
      _ = Sheaf.H.δ hS n (n + 1) rfl
          (cohomologyPushforwardEquiv e S.X₃ n
            (cohomologyPushforwardEquiv f (Pe.obj S.X₃) n a)) :=
        cohomologyPushforwardEquiv_δ e hS n (n + 1) rfl _
      _ = Sheaf.H.δ hS n (n + 1) rfl
          (cohomologyPushforwardEquiv (e ≪≫ f) S.X₃ n a) := by rw [ih]
      _ = _ := (cohomologyPushforwardEquiv_δ (e ≪≫ f) hS n (n + 1) rfl a).symm

/-- Successive comparison is the published comparison for the composite homeomorphism. -/
lemma cohomologyPushforwardCompositeEquiv_eq (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    cohomologyPushforwardCompositeEquiv e f F n =
      cohomologyPushforwardEquiv (e ≪≫ f) F n := by
  ext x
  exact cohomologyPushforwardEquiv_comp e f F n x

end Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
