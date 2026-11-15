import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityStatement
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.SmoothConnectedKernelCocharacters
import Langlands.GroupScheme.Torus.SplitCocharacterGeneration
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Derived.CocenterQuotientStructuralReduction
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.TorsorCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Proof: rational surjectivity of torus quotients with torus kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusQuotientRationalSurjectivity

/-- An epimorphism of split tori over a field whose kernel is smooth and connected is
surjective on rational points: every target point is a product of cocharacter values, and
every target cocharacter lifts. -/
theorem rationalPoints_surjective_of_split {K : Type u} [Field K]
    {T Q : CommGroupScheme (Spec (CommRingCat.of K))}
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q)
    [Epi (CommGroupScheme.groupHom f)]
    [Smooth (kernel (CommGroupScheme.groupHom f)).X.hom]
    [ConnectedSpace (kernel (CommGroupScheme.groupHom f)).X.left] :
    Function.Surjective (rationalPoints.map (CommGroupScheme.groupHom f)) := by
  intro t
  obtain ⟨J, _, ν, hν⟩ := hQ.exists_cocharacterPoints_prod
  obtain ⟨x, hx⟩ := hν t
  refine ⟨∏ j, CocharacterUniformizer.cocharacterPoints K T
    (hT.cocharacterLiftOfSmoothConnectedKernel hQ f (ν j)) (x j), ?_⟩
  rw [map_prod, hx]
  refine Finset.prod_congr rfl fun j _ => ?_
  conv_rhs => rw [← hT.cocharacterLiftOfSmoothConnectedKernel_comp hQ f (ν j)]
  simp only [CocharacterUniformizer.cocharacterPoints, MonoidHom.comp_apply,
    rationalPoints.map_apply, Category.assoc]
  rfl

variable {k : Type u} [Field k]

/-- After base change to a field `L` over which two tori `B` and `C` split, a scheme-surjective
homomorphism `q : B ⟶ C` with torus kernel is surjective on `L`-rational points. -/
theorem baseChange_rationalPoints_surjective
    {B C : GroupScheme (Spec (CommRingCat.of k))} (hB : IsTorus B) (hC : IsTorus C)
    (q : B ⟶ C) (hq : Surjective q.hom.hom.left) (hker : IsTorus (kernel q))
    (L : Type u) [Field L] [Algebra k L]
    (hBL : IsSplitTorus (GaloisPointComparison.baseChanged k L B))
    (hCL : IsSplitTorus (GaloisPointComparison.baseChanged k L C)) :
    Function.Surjective (rationalPoints.map
      ((GroupScheme.baseChange (GaloisPointComparison.baseMap k L)).map q)) := by
  let b := GaloisPointComparison.baseMap k L
  let F := GroupScheme.baseChange b
  let Bc : CommGroupScheme (Spec (CommRingCat.of k)) := { B with comm := hB.isCommMonObj }
  let Cc : CommGroupScheme (Spec (CommRingCat.of k)) := { C with comm := hC.isCommMonObj }
  let f : Bc ⟶ Cc := Additive.ofMul q
  let fL := (CommGroupScheme.baseChange b).map f
  have hqL : Surjective (F.map q).hom.hom.left := by
    have : Surjective q.hom.hom.left := hq
    exact MorphismProperty.of_isPullback (baseChange_map_isPullback b q).flip inferInstance
  let : Epi (CommGroupScheme.groupHom fL) :=
    hBL.isTorus.epi_of_surjective_hom hCL.isTorus (F.map q) hqL
  have hK : IsTorus (kernel (F.map q)) :=
    IsTorus.of_iso (kernelBaseChangeIso b q).symm (hker.baseChange (K := L))
  let : Smooth (kernel (CommGroupScheme.groupHom fL)).X.hom := hK.smooth
  let : ConnectedSpace (kernel (CommGroupScheme.groupHom fL)).X.left := hK.connectedSpace
  exact rationalPoints_surjective_of_split (T := (CommGroupScheme.baseChange b).obj Bc)
    (Q := (CommGroupScheme.baseChange b).obj Cc) hBL hCL fL

end TorusQuotientRationalSurjectivity

open TorusQuotientRationalSurjectivity in
/-- **Rational surjectivity of torus quotients with torus kernel.** Over a field with trivial
torus cocycles on finite Galois covers, a scheme-surjective homomorphism of tori whose
scheme-theoretic kernel is a torus is surjective on rational points. -/
theorem torusQuotientRationalSurjectivity :
    TorusQuotientRationalSurjectivityStatement.{u} := by
  intro k _ hcoc B C hB hC q hq hker c
  let E := hB.commonFiniteGaloisSplitting hC
  let L := E.carrier
  let b := GaloisPointComparison.baseMap k L
  let S := Spec (CommRingCat.of k)
  -- A lift of `c` over the common splitting field `L`.
  obtain ⟨bL, hbL⟩ := baseChange_rationalPoints_surjective hB hC q hq hker L
    E.split_left E.split_right (baseChangeSectionHom b C c)
  let U : Over S := Over.mk b
  let π : U ⟶ Over.mk (𝟙 S) := Over.homMk b (Category.comp_id b)
  let b₁ : U ⟶ B.X := baseChangeBasePointsEquiv b B bL
  have hb₁ : b₁ ≫ q.hom.hom = π ≫ c := by
    rw [← baseChangeBasePointsEquiv_comp]
    change baseChangeBasePointsEquiv b C (rationalPoints.map _ bL) = π ≫ c
    rw [hbL]
    exact (baseChangeBasePointsEquiv b C).apply_symm_apply _
  have hπ : ∀ {Z : Over S} (a a' : Z ⟶ U), a ≫ π = a' ≫ π := by
    intro Z a a'
    apply Over.OverMorphism.ext
    have ha := Over.w a
    have ha' := Over.w a'
    simp only [Over.comp_left]
    exact ha.trans ha'.symm
  -- The coboundary of `b₁` takes values in the kernel of `q`.
  have hmem : ∀ {Z : Over S} (a a' : Z ⟶ U), ∃ y : Z ⟶ (kernel q).X,
      y ≫ (kernelι q).hom.hom = (Cocycle.coboundary b₁).toFun a a' := by
    intro Z a a'
    have h1 : (Cocycle.coboundary b₁).toFun a a' ≫ q.hom.hom = 1 := by
      change ((a ≫ b₁) * (a' ≫ b₁)⁻¹) ≫ q.hom.hom = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hb₁,
        ← Category.assoc, ← Category.assoc, hπ a a', mul_inv_cancel]
    exact SubgroupFunctor.mem_range.1 ((mem_range_kernelι_iff q _).2 h1)
  let ξ := (Cocycle.coboundary b₁).lift (kernelι q) hmem
  obtain ⟨g, hg⟩ := hcoc (kernel q) hker L ξ
  let fk : U ⟶ B.X := g ≫ (kernelι q).hom.hom
  have hfk : ∀ {Z : Over S} (a a' : Z ⟶ U),
      (a ≫ b₁) * (a' ≫ b₁)⁻¹ = (a ≫ fk) * (a' ≫ fk)⁻¹ := by
    intro Z a a'
    have h2 := Cocycle.lift_toFun (Cocycle.coboundary b₁) (kernelι q) hmem a a'
    change ξ.toFun a a' ≫ (kernelι q).hom.hom = (a ≫ b₁) * (a' ≫ b₁)⁻¹ at h2
    rw [hg a a', MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc] at h2
    exact h2.symm
  have hfq : fk ≫ q.hom.hom = 1 :=
    (mem_range_kernelι_iff q fk).1 (SubgroupFunctor.mem_range.2 ⟨g, rfl⟩)
  -- The corrected lift agrees on any two points of the cover.
  let b₂ : U ⟶ B.X := fk⁻¹ * b₁
  have hb₂ : ∀ {Z : Over S} (a a' : Z ⟶ U), a ≫ b₂ = a' ≫ b₂ := by
    intro Z a a'
    simp only [b₂, MonObj.comp_mul, GrpObj.comp_inv]
    have h := hfk a a'
    calc (a ≫ fk)⁻¹ * (a ≫ b₁)
        = (a ≫ fk)⁻¹ * ((a ≫ b₁) * (a' ≫ b₁)⁻¹) * (a' ≫ b₁) := by group
      _ = (a ≫ fk)⁻¹ * ((a ≫ fk) * (a' ≫ fk)⁻¹) * (a' ≫ b₁) := by rw [h]
      _ = (a' ≫ fk)⁻¹ * (a' ≫ b₁) := by group
  have hb₂q : b₂ ≫ q.hom.hom = π ≫ c := by
    simp only [b₂, MonObj.mul_comp, GrpObj.inv_comp, hfq, hb₁, inv_one, one_mul]
  have : EffectiveEpi U.hom := by
    obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc k L
    change EffectiveEpi b
    infer_instance
  obtain ⟨s, hs, hsec⟩ := exists_section_of_forall_eq b₂ hb₂
  refine ⟨Over.homMk s (by simpa using hsec), ?_⟩
  rw [rationalPoints.map_apply]
  apply Over.OverMorphism.ext
  change s ≫ q.hom.hom.left = c.left
  rw [← cancel_epi U.hom, ← Category.assoc, hs]
  exact congrArg CommaMorphism.left hb₂q

end Langlands.GroupScheme
