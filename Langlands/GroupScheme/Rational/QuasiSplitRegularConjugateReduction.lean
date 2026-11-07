import Langlands.GroupScheme.Rational.AlgebraicClosureCover
import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugateStatement
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalStatement
import Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisStatement
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Reduction of rational strongly regular representatives to two prerequisites -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace QuasiSplitRegularConjugate

/-- Restricting a base point of a pullback to a test is the test's canonical cover point
followed by the corresponding original point. -/
theorem baseChangePointsEquiv_toUnit_comp {S S' : Scheme.{u}} (b : S' ⟶ S)
    (G : GroupScheme S) (Z : Over S') (z : Over.mk b ⟶ G.X) :
    baseChangePointsEquiv b G Z (toUnit Z ≫ (baseChangeBasePointsEquiv b G).symm z) =
      LocalGroupIso.baseChangeTestPoint (U := Over.mk b) Z ≫ z := by
  apply Over.OverMorphism.ext
  have h := baseChangeBasePointsEquiv_left b G ((baseChangeBasePointsEquiv b G).symm z)
  rw [MulEquiv.apply_symm_apply] at h
  rw [baseChangePointsEquiv_left, Over.comp_left, Category.assoc, ← h]
  change (toUnit Z).left ≫ _ = Z.hom ≫ _
  congr 1

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The point of `G` over the cover that `e` at the identity point carries to `y`. -/
def coverPoint
    (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X :=
  (e.toFun (𝟙 _)).symm (toUnit _ ≫ y)

/-- At every point `w` of the cover, `e` carries the restriction of the cover point to the
restriction of `y`. -/
theorem toFun_comp_coverPoint
    (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X) {Z : Over (Spec (CommRingCat.of K))}
    (w : Z ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    e.toFun w (w ≫ coverPoint e y) = toUnit Z ≫ y := by
  have h := e.naturality w (𝟙 _) (coverPoint e y)
  rw [Category.comp_id] at h
  rw [h, coverPoint, MulEquiv.apply_symm_apply, ← Category.assoc, comp_toUnit]

/-- The centralizer of the cover point in `G_L` lies in the base change of the torus `S`,
transported to `G_L` by the recovered base-change isomorphism. -/
theorem centralizer_coverPoint
    (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X)
    (S : GroupScheme (Spec (CommRingCat.of K))) (j : S ⟶ H)
    (hy : ∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ y) = (toUnit Z ≫ y) * c → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c)
    {Z : Over (Spec (CommRingCat.of L))}
    (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X)
    (hc : c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm (coverPoint e y)) =
      (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm (coverPoint e y)) * c) :
    ∃ s : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj S).X,
      s ≫ ((baseChange _).map j ≫ e.toBaseChangeIso.inv).hom.hom = c := by
  have hΨ := congrArg (baseChangePointsEquiv _ G Z) hc
  rw [map_mul, map_mul, baseChangePointsEquiv_toUnit_comp] at hΨ
  have hΦ := congrArg (e.toFun (LocalGroupIso.baseChangeTestPoint Z)) hΨ
  rw [map_mul, map_mul, toFun_comp_coverPoint] at hΦ
  have hp : baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap K L))) H Z
      (c ≫ e.toBaseChangeIso.hom.hom.hom) =
        e.toFun (LocalGroupIso.baseChangeTestPoint Z)
          (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap K L))) G Z c) :=
    e.toBaseChangeIso_hom_points Z c
  rw [← hp] at hΦ
  obtain ⟨s, hs⟩ := hy _ hΦ
  refine ⟨(baseChangePointsEquiv _ S Z).symm s, ?_⟩
  have hj : (baseChangePointsEquiv _ S Z).symm s ≫
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map j).hom.hom =
      c ≫ e.toBaseChangeIso.hom.hom.hom := by
    apply (baseChangePointsEquiv _ H Z).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, hs]
  rw [Grp.comp_hom_hom, ← Category.assoc]
  erw [hj]
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id]
  rfl

/-- Every Galois conjugate of the cover point is conjugate to it over the algebraic closure
of `L`: the discrepancy at `(𝟙, σ)` acts on `σ ≫ z` to give `z`, and it lifts along the central
isogeny there. -/
theorem coverPoint_galoisStable {A : GroupScheme (Spec (CommRingCat.of K))}
    (π : G ⟶ A) (hπ : IsCentralIsogeny π) (a : AutomorphicAction A G)
    (ha : ∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X),
      a.act (h ≫ π.hom.hom) g = h * g * h⁻¹)
    (ξ : Cocycle A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (he : e.HasDiscrepancy a ξ) (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X)
    (σ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
      (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
      h * (q ≫ coverPoint e y) * h⁻¹ = q ≫ σ ≫ coverPoint e y := by
  have hact : a.act (ξ.toFun (𝟙 _) σ) (σ ≫ coverPoint e y) = coverPoint e y := by
    apply (e.toFun (𝟙 _)).injective
    rw [he (𝟙 _) σ, toFun_comp_coverPoint, coverPoint, MulEquiv.apply_symm_apply]
  let q := algebraicClosureCoverPoint K L
  let p := q ≫ ξ.toFun (𝟙 _) σ
  have : LocallyOfFinitePresentation π.hom.hom.left := hπ.locallyOfFinitePresentation
  have : Surjective π.hom.hom.left := hπ.surjective
  obtain ⟨l, hl⟩ := Langlands.exists_point_lift_of_locallyOfFiniteType_surjective
    π.hom.hom.left p.left
  let h₀ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))) ⟶ G.X :=
    Over.homMk l (by
      change l ≫ G.X.hom = _
      rw [← Over.w π.hom.hom, ← Category.assoc, hl]
      exact Over.w p)
  have hh₀ : h₀ ≫ π.hom.hom = p := Over.OverMorphism.ext hl
  have hconj : q ≫ coverPoint e y = h₀ * (q ≫ σ ≫ coverPoint e y) * h₀⁻¹ := by
    rw [← ha, hh₀, ← a.naturality, hact]
  refine ⟨AlgebraicClosure L, inferInstance, inferInstance, q, h₀⁻¹, ?_⟩
  rw [hconj]
  group

end QuasiSplitRegularConjugate

open QuasiSplitRegularConjugate in
/-- **Conditional reduction.** The rational strongly regular representative theorem for inner
twists of simply connected quasi-split groups follows from the Galois-stable class theorem
and the finite Galois descent of conjugacy. -/
theorem quasiSplitSimplyConnectedRegularConjugate_of_classRational
    (h₁ : QuasiSplitRegularClassRationalStatement.{u})
    (h₃ : RegularConjugateFiniteGaloisStatement.{u}) :
    QuasiSplitSimplyConnectedRegularConjugateStatement.{u} := by
  intro K L _ _ _ _ _ G A hsc hqs π hπ a ha ξ H e he y S j hS hj hy
  have hS' : IsTorus ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj S) :=
    hS.baseChange
  have hj' : IsClosedSubgroup
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map j ≫
        e.toBaseChangeIso.inv) :=
    IsClosedSubgroup.comp (IsClosedSubgroup.baseChange _ hj)
      (IsClosedSubgroup.of_iso e.toBaseChangeIso.symm)
  obtain ⟨x, E, _, _, q, g, hg⟩ := h₁ K L G hsc hqs (coverPoint e y) _ _ hS' hj'
    (fun c hc => centralizer_coverPoint e y S j hy c hc)
    (fun σ => coverPoint_galoisStable π hπ a ha ξ e he y σ)
  obtain ⟨T, i, hT, hi, hx, L', _, _, _, _, r, g', hg'⟩ :=
    h₃ K L G hqs.isConnectedReductive (coverPoint e y) _ _ hS' hj'
      (fun c hc => centralizer_coverPoint e y S j hy c hc) x E q g hg
  refine ⟨x, T, i, hT, hi, hx, L', inferInstance, inferInstance, inferInstance, inferInstance,
    r, g', ?_⟩
  rw [hg', toFun_comp_coverPoint]

end Langlands.GroupScheme
