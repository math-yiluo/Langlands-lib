import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Representable closed immersions and thickenings

Geometric conditions are tested on every actual represented scheme pullback.
Finite order means that a single exponent works for every scheme test.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}

/-- A representable transformation whose every represented projection is a closed immersion. -/
def IsClosedImmersion (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S) f

/-- A representable closed immersion that is geometrically surjective, without an order bound. -/
def IsThickening (f : F ⟶ G) : Prop :=
  IsClosedImmersion f ∧ IsSurjective f

/-- An nth-order thickening has kernel power n + 1 zero on every represented scheme square. -/
def IsNthOrderThickening (n : ℕ) (f : F ⟶ G) : Prop :=
  IsThickening f ∧
    ∀ ⦃U V : Over S⦄ (g : (schemeYoneda S).obj U ⟶ G)
      (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U),
      IsPullback a ((schemeYoneda S).map p) f g → (p.left).ker ^ (n + 1) = ⊥

/-- First order is nth order for n = 1, so every represented kernel has square zero. -/
abbrev IsFirstOrderThickening (f : F ⟶ G) : Prop :=
  IsNthOrderThickening 1 f

/-- One finite order bound is chosen before all actual scheme tests. -/
def IsFiniteOrderThickening (f : F ⟶ G) : Prop :=
  ∃ n : ℕ, IsNthOrderThickening n f

/-- A closed immersion is representable by actual schemes. -/
theorem IsClosedImmersion.representable (hf : IsClosedImmersion f) :
    IsRepresentableMorphism f :=
  hf.1

/-- Every projection in a represented square of a closed immersion is a scheme closed immersion. -/
theorem IsClosedImmersion.projection (hf : IsClosedImmersion f) {U V : Over S}
    (g : (schemeYoneda S).obj U ⟶ G) (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) :
    _root_.AlgebraicGeometry.IsClosedImmersion p.left :=
  hf.2 g a p h

/-- The chosen represented projection of any representability witness is a closed immersion. -/
theorem IsClosedImmersion.pullback_closedImmersion (hf : IsClosedImmersion f)
    (hr : IsRepresentableMorphism f) {U : Over S} (g : (schemeYoneda S).obj U ⟶ G) :
    _root_.AlgebraicGeometry.IsClosedImmersion (hr.snd g).left :=
  hf.projection g (hr.fst g) (hr.snd g) (hr.isPullback g)

/-- A thickening is a closed immersion. -/
theorem IsThickening.closedImmersion (hf : IsThickening f) : IsClosedImmersion f :=
  hf.1

/-- A thickening is geometrically surjective on represented scheme tests. -/
theorem IsThickening.surjective (hf : IsThickening f) : IsSurjective f :=
  hf.2

/-- A thickening is representable by actual schemes. -/
theorem IsThickening.representable (hf : IsThickening f) : IsRepresentableMorphism f :=
  hf.closedImmersion.representable

/-- Every represented projection of a thickening is a scheme closed immersion. -/
theorem IsThickening.projection_closedImmersion (hf : IsThickening f) {U V : Over S}
    (g : (schemeYoneda S).obj U ⟶ G) (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) :
    _root_.AlgebraicGeometry.IsClosedImmersion p.left :=
  hf.closedImmersion.projection g a p h

/-- Every represented projection of a thickening is surjective on scheme points. -/
theorem IsThickening.projection_surjective (hf : IsThickening f) {U V : Over S}
    (g : (schemeYoneda S).obj U ⟶ G) (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) : Surjective p.left :=
  hf.surjective.projection g a p h

/-- The chosen represented projection of a thickening is surjective on scheme points. -/
theorem IsThickening.pullback_surjective (hf : IsThickening f)
    (hr : IsRepresentableMorphism f) {U : Over S} (g : (schemeYoneda S).obj U ⟶ G) :
    Surjective (hr.snd g).left :=
  hf.projection_surjective g (hr.fst g) (hr.snd g) (hr.isPullback g)

/-- An nth-order thickening is a thickening. -/
theorem IsNthOrderThickening.thickening {n : ℕ} (hf : IsNthOrderThickening n f) :
    IsThickening f :=
  hf.1

/-- An nth-order thickening is representable by actual schemes. -/
theorem IsNthOrderThickening.representable {n : ℕ} (hf : IsNthOrderThickening n f) :
    IsRepresentableMorphism f :=
  hf.thickening.representable

/-- The target kernel ideal-sheaf power vanishes in every represented square. -/
theorem IsNthOrderThickening.kernel_pow_eq {n : ℕ} (hf : IsNthOrderThickening n f)
    {U V : Over S} (g : (schemeYoneda S).obj U ⟶ G)
    (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) : (p.left).ker ^ (n + 1) = ⊥ :=
  hf.2 g a p h

/-- Kernel-power vanishing holds for the pullback chosen by any representability witness. -/
theorem IsNthOrderThickening.pullback_kernel_pow_eq {n : ℕ}
    (hf : IsNthOrderThickening n f) (hr : IsRepresentableMorphism f)
    {U : Over S} (g : (schemeYoneda S).obj U ⟶ G) :
    ((hr.snd g).left).ker ^ (n + 1) = ⊥ :=
  hf.kernel_pow_eq g (hr.fst g) (hr.snd g) (hr.isPullback g)

/-- A first-order thickening is a thickening. -/
theorem IsFirstOrderThickening.thickening (hf : IsFirstOrderThickening f) :
    IsThickening f :=
  hf.1

/-- Every represented projection of a first-order thickening has square-zero kernel. -/
theorem IsFirstOrderThickening.kernel_sq_eq (hf : IsFirstOrderThickening f)
    {U V : Over S} (g : (schemeYoneda S).obj U ⟶ G)
    (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) : (p.left).ker ^ 2 = ⊥ :=
  IsNthOrderThickening.kernel_pow_eq hf g a p h

/-- A finite-order thickening is a thickening, by its single uniform-order witness. -/
theorem IsFiniteOrderThickening.thickening (hf : IsFiniteOrderThickening f) :
    IsThickening f := by
  obtain ⟨n, hn⟩ := hf
  exact hn.thickening

end Langlands.AlgebraicGeometry.AlgebraicSpace
