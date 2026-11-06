import Langlands.Representation.Category.SmoothPartAdjunction
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Small colimits under normalized Jacquet restriction

After forgetting the Levi action, the normalized Jacquet functor is ordinary
coinvariants of the restricted algebraic action. This proves small colimit
preservation without a radical unimodularity or compactness assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uG uH uV u

namespace Langlands.SmoothRep

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Forget the smooth action while retaining its actual complex module. -/
abbrev forgetToModule : SmoothRep.{0, uG, uV} ℂ G ⥤ ModuleCat.{uV} ℂ :=
  toRep ⋙ forget₂ (Rep.{uV} ℂ G) (ModuleCat ℂ)

instance forgetToModule_reflectsColimits :
    ReflectsColimitsOfSize.{uV, uV} (forgetToModule.{uG, uV} G) := by
  dsimp only [forgetToModule]
  infer_instance

instance forgetToModule_preservesColimits [IsTopologicalGroup G] :
    PreservesColimitsOfSize.{uV, uV} (forgetToModule.{uG, uV} G) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (toRep : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uV} ℂ G) :=
    (toRepSmoothPartAdjunction ℂ G).leftAdjoint_preservesColimits
  dsimp only [forgetToModule]
  infer_instance

variable {G} {H : Type uH} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Same-carrier smooth pullback preserves small colimits. -/
instance pullbackFunctor_preservesColimits (e : H ≃ₜ* G) :
    PreservesColimitsOfSize.{uV, uV} (pullbackFunctor.{uG, uH, uV} e) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (pullbackFunctor.{uG, uH, uV} e ⋙ forgetToModule H) :=
    inferInstanceAs (PreservesColimitsOfSize.{uV, uV} (forgetToModule G))
  exact preservesColimits_of_reflects_of_preserves _ (forgetToModule H)

/-- Open-kernel scalar twisting preserves small colimits. -/
instance twistFunctor_preservesColimits (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    PreservesColimitsOfSize.{uV, uV} (twistFunctor.{0, uG, uV} χ hχ) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (twistFunctor.{0, uG, uV} χ hχ ⋙ forgetToModule G) :=
    inferInstanceAs (PreservesColimitsOfSize.{uV, uV} (forgetToModule G))
  exact preservesColimits_of_reflects_of_preserves _ (forgetToModule G)

end Langlands.SmoothRep

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Forgetting the normalized Jacquet action leaves ordinary algebraic coinvariants. -/
def normalizedJacquetForgetIso (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    normalizedJacquetFunctor.{uG, uV} U M hU hMU ⋙ SmoothRep.forgetToModule M ≅
      SmoothRep.toRep ⋙ Rep.resFunctor U.subtype ⋙ Rep.coinvariantsFunctor ℂ U :=
  NatIso.ofComponents
    (fun A => (Jacquet.Localization.trivialEquiv A.representation U M hMU).toLinearEquiv.toModuleIso)
    (by
      intro A B f
      ext q
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 q
      rfl)

/-- Normalized Jacquet restriction preserves colimits of small diagrams. -/
instance normalizedJacquetFunctor_preservesColimits (U M : Subgroup G)
    (hU : IsClosed (U : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    PreservesColimitsOfSize.{uV, uV} (normalizedJacquetFunctor.{uG, uV} U M hU hMU) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (SmoothRep.toRep : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uV} ℂ G) :=
    (SmoothRep.toRepSmoothPartAdjunction ℂ G).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{uV, uV}
      (normalizedJacquetFunctor.{uG, uV} U M hU hMU ⋙ SmoothRep.forgetToModule M) :=
    preservesColimits_of_natIso (normalizedJacquetForgetIso U M hU hMU).symm
  exact preservesColimits_of_reflects_of_preserves _ (SmoothRep.forgetToModule M)

end Langlands.Aubert.General

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- The actual Levi-point Jacquet functor preserves small colimits. -/
instance leviJacquetFunctor_preservesColimits (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    PreservesColimitsOfSize.{uV, uV} (leviJacquetFunctor.{u, uV} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  dsimp only [leviJacquetFunctor, jacquetFunctor]
  infer_instance

end Langlands.Aubert.General.RepresentedParabolic
