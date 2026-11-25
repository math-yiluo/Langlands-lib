/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso

/-! # Local frame atlases for realization base change

## References

* Stacks Project, Tags 01NQ, 01NR and 01OB
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A common frame atlas for the two realization pullback quotients: the pulled-back source
quotient and the target quotient after the canonical pullback coherence of
`projectiveBundleThetaQuotientLaw` have, on a common cover, matching free generators with equal
transitions and equal local coefficients. -/
structure ProjectiveBundleRealizationPullbackAtlas
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data) where
  ι : Type u
  U : ι → D'.A.data.relProj.Opens
  s : ∀ i, Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L, U i)
  t : ∀ i, Γ(D'.L, U i)
  cover : ⨆ i, U i = ⊤
  s_generator : ∀ i, Scheme.Modules.IsFreeGenerator (s i)
  t_generator : ∀ i, Scheme.Modules.IsFreeGenerator (t i)
  transition : ∀ i j (V : D'.A.data.relProj.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (a c : Γ(D'.A.data.relProj, V)),
      a • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
          (homOfLE hi).op (s i) =
        c • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
          (homOfLE hj).op (s j) →
      a • D'.L.presheaf.map (homOfLE hi).op (t i) =
        c • D'.L.presheaf.map (homOfLE hj).op (t j)
  coefficients : ∀ i (V : D'.A.data.relProj.Opens) (hi : V ≤ U i)
      (m : Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F), V)),
      ∃ c : Γ(D'.A.data.relProj, V),
        ((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app V m =
          c • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
            (homOfLE hi).op (s i) ∧
        (((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
          (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
          ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
          (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app V m =
          c • D'.L.presheaf.map (homOfLE hi).op (t i)

/-- If the base-change map `b` is compatible with the degree-one sections via `e` (hypothesis
`hb`), then the two realization pullback quotients admit a common frame atlas. -/
theorem exists_projectiveBundleRealizationPullbackAtlas
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x))))) :
    Nonempty (ProjectiveBundleRealizationPullbackAtlas D D' g e b) := by
  sorry

end AlgebraicGeometry
