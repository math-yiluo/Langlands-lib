import Langlands.GroupScheme.AntiAffine
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent

/-! # Comparison of an affinization with an affine fpqc quotient -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsAffinization

variable {k : Type u} [Field k]
  {G Q H : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ Q}
  (hq : IsAffinization q) (q₀ : G ⟶ H) [IsAffine H.X.left]
  [Flat q₀.hom.hom.left] [Surjective q₀.hom.hom.left] [QuasiCompact q₀.hom.hom.left]
  (hk : kernelι q₀ ≫ q = 0)

/-- An affine fpqc quotient whose full kernel is killed by a supplied
actual affinization is canonically isomorphic to its affine target. -/
def fpqcComparisonIso : H ≅ Q := by
  let t : H ⟶ Q := FpqcHomDescent.hom q₀ q hk
  have ht : q₀ ≫ t = q := FpqcHomDescent.fac q₀ q hk
  have htΓ : t.hom.hom.left.appTop ≫ q₀.hom.hom.left.appTop = q.hom.hom.left.appTop := by
    rw [← Scheme.Hom.comp_appTop]
    exact congrArg (fun a => a.hom.hom.left.appTop) ht
  have : IsIso q.hom.hom.left.appTop := hq.isIso_appTop
  have hqΓ : Function.Bijective q.hom.hom.left.appTop.hom :=
    ConcreteCategory.bijective_of_isIso q.hom.hom.left.appTop
  have h₀inj : Function.Injective q₀.hom.hom.left.appTop.hom :=
    Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi q₀.hom.hom.left
  have h₀surj : Function.Surjective q₀.hom.hom.left.appTop.hom := by
    intro x
    obtain ⟨y, hy⟩ := hqΓ.2 x
    refine ⟨t.hom.hom.left.appTop.hom y, ?_⟩
    exact (congrArg (fun a : Γ(Q.X.left, ⊤) ⟶ Γ(G.X.left, ⊤) => a.hom y) htΓ).trans hy
  have : IsIso q₀.hom.hom.left.appTop :=
    (ConcreteCategory.isIso_iff_bijective q₀.hom.hom.left.appTop).mpr ⟨h₀inj, h₀surj⟩
  have : IsIso (t.hom.hom.left.appTop ≫ q₀.hom.hom.left.appTop) := by
    rw [htΓ]
    infer_instance
  have : IsIso t.hom.hom.left.appTop := (isIso_comp_right_iff _ _).mp this
  have : IsAffine Q.X.left := hq.isAffine
  have : IsIso t.hom.hom.left :=
    (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme.{u})).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget _).map t.hom.hom) := ‹IsIso t.hom.hom.left›
  have : IsIso t.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map t.hom) := ‹IsIso t.hom.hom›
  have : IsIso t.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map t) := ‹IsIso t.hom›
  have : IsIso t := isIso_of_reflects_iso t (Grp.forget₂Mon _)
  exact asIso t

/-- The comparison isomorphism recovers the specified affinization
homomorphism after the actual fpqc quotient projection. -/
@[reassoc]
theorem fpqcComparisonIso_fac : q₀ ≫ (hq.fpqcComparisonIso q₀ hk).hom = q :=
  FpqcHomDescent.fac q₀ q hk

end Langlands.GroupScheme.IsAffinization
