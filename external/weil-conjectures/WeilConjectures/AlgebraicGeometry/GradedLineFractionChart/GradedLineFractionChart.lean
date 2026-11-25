/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedLineMap
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Spectrum charts of a graded line map

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: def-trf-graded-line-fraction-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- An affine base chart, an affine framed source chart, and a positive-degree denominator.
Source: Stacks, Tags 01NK and 01O9 (blueprint: def-trf-graded-line-fraction-chart). -/
structure GradedLineFractionChart {S T : Scheme.{u}} (h : T ⟶ S)
    (A : S.GradedAlgebraData) (L : T.Modules) where
  U : S.affineOpens
  W : T.affineOpens
  hWU : W.1 ≤ h ⁻¹ᵁ U.1
  l : Γ(L, W.1)
  hl : IsFreeGenerator l
  d : ℕ
  hd : 0 < d
  e : A.grading U d

/-- A family of frame coefficients; its defining equations are imposed separately.
Source: Stacks, Tags 01NK and 01O9 (blueprint: def-trf-graded-line-fraction-chart). -/
abbrev GradedLineFractionCoefficients {S T : Scheme.{u}} (h : T ⟶ S)
    (A : S.GradedAlgebraData) (L : T.Modules) :=
  ∀ (U : S.affineOpens) (W : T.affineOpens),
    W.1 ≤ h ⁻¹ᵁ U.1 → Γ(L, W.1) → (n : ℕ) → A.grading U n → Γ(T, W.1)

namespace GradedLineFractionChart

variable {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
  (c : GradedLineFractionCoefficients h A L)

/-- The coefficient at the chosen denominator.
Source: Stacks, Tag 01NK (blueprint: def-trf-graded-line-fraction-chart). -/
abbrev coefficient (i : GradedLineFractionChart h A L) : Γ(T, i.W.1) :=
  c i.U i.W i.hWU i.l i.d i.e

/-- The affine spectrum of the ordinary localization at the denominator coefficient.
Source: Stacks, Tag 01NK (blueprint: def-trf-graded-line-fraction-chart). -/
noncomputable abbrev domain (i : GradedLineFractionChart h A L) : Scheme.{u} :=
  Spec (.of (Localization.Away (coefficient c i)))

/-- Its canonical open immersion into the source scheme.
Source: Stacks, Tag 01NK (blueprint: def-trf-graded-line-fraction-chart). -/
noncomputable def source (i : GradedLineFractionChart h A L) : domain c i ⟶ T :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(T, i.W.1) (Localization.Away (coefficient c i)))) ≫
      i.W.2.isoSpec.inv ≫ i.W.1.ι

instance (i : GradedLineFractionChart h A L) : IsOpenImmersion (source c i) := by
  dsimp only [source]
  infer_instance

/-- The candidate map from a fraction chart to relative Proj.
Source: Stacks, Tags 01NK and 01O9 (blueprint: def-trf-graded-line-fraction-chart). -/
noncomputable def target
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (coefficient c i))
    (i : GradedLineFractionChart h A L) : domain c i ⟶ A.relProj :=
  Spec.map (CommRingCat.ofHom (ρ i)) ≫
    Proj.awayι (A.grading i.U) i.e.val i.e.property i.hd ≫ A.relProjι i.U

/-- The fraction equation, including exponent zero and nilpotent denominators.
Source: Stacks, Tag 01NK (blueprint: def-trf-graded-line-fraction-chart). -/
def FractionFormula
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (coefficient c i)) : Prop :=
  ∀ (i : GradedLineFractionChart h A L) (n : ℕ) (a : A.grading i.U (n • i.d)),
    ρ i (HomogeneousLocalization.Away.mk (A.grading i.U) i.e.property n a.val a.property) =
      Localization.mk (c i.U i.W i.hWU i.l (n • i.d) a)
        (⟨coefficient c i ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (coefficient c i))

end GradedLineFractionChart

end AlgebraicGeometry.Scheme.Modules
