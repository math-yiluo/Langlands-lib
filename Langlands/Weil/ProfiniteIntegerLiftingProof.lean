import Langlands.Weil.ProfiniteIntegerLifting
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section

namespace Langlands.Weil

open CategoryTheory ProfiniteGrp

universe u v

private def finiteKernel {H : Type v} [Group H] [Finite H]
    (f : Degree →* H) : FiniteIndexNormalSubgroup Degree :=
  FiniteIndexNormalSubgroup.ofSubgroup f.ker

private def liftFinite {H : Type v} [Group H] [Finite H] [TopologicalSpace H]
    (f : Degree →* H) : ProfiniteIntegers →ₜ* H where
  toFun x := QuotientGroup.lift f.ker f (by intro x hx; exact hx) (x.val (finiteKernel f))
  map_one' := map_one _
  map_mul' x y := map_mul _ _ _
  continuous_toFun := by
    let Q := (ProfiniteCompletion.diagram (GrpCat.of Degree)).obj (finiteKernel f)
    have : Finite Q := by
      change Finite (Degree ⧸ f.ker)
      infer_instance
    have : DiscreteTopology Q := inferInstance
    let π : ProfiniteIntegers →ₜ* Q :=
      ((limitCone (ProfiniteCompletion.diagram (GrpCat.of Degree))).π.app (finiteKernel f)).hom
    exact (continuous_of_discreteTopology (f := fun q : Q =>
      QuotientGroup.lift f.ker f (by intro x hx; exact hx) q)).comp π.continuous

private theorem liftFinite_frobenius {H : Type v} [Group H] [Finite H]
    [TopologicalSpace H] (f : Degree →* H) (n : Degree) :
    liftFinite f (frobenius n) = f n := rfl

variable (P : ProfiniteGrp.{u}) (f : Degree →* P)

private def component (U : OpenNormalSubgroup P) :
    ProfiniteIntegers →ₜ* (ProfiniteGrp.diagram P).obj U :=
  have : Finite ((ProfiniteGrp.diagram P).obj U) := by
    change Finite (P ⧸ U.toSubgroup)
    infer_instance
  liftFinite ((QuotientGroup.mk' U.toSubgroup).comp f)

private theorem component_frobenius (U : OpenNormalSubgroup P) (n : Degree) :
    component P f U (frobenius n) = (toLimitFun P (f n)).val U := rfl

private def liftToLimit : ProfiniteIntegers →ₜ* limit (ProfiniteGrp.diagram P) where
  toFun x :=
    ⟨fun U => component P f U x, by
      intro U V g
      have h :
          (fun z => (ProfiniteGrp.diagram P).map g (component P f U z)) =
            component P f V := by
        apply (ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).equalizer
          (((ProfiniteGrp.diagram P).map g).hom.continuous.comp
            (component P f U).continuous) (component P f V).continuous
        funext n
        change (ProfiniteGrp.diagram P).map g (component P f U (frobenius n)) =
          component P f V (frobenius n)
        rw [component_frobenius, component_frobenius]
        exact (toLimitFun P (f n)).property g
      exact congrFun h x⟩
  map_one' := by
    apply Subtype.ext
    funext U
    exact map_one (component P f U)
  map_mul' x y := by
    apply Subtype.ext
    funext U
    exact map_mul (component P f U) x y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_pi (fun U => (component P f U).continuous)

private def liftProfinite : ProfiniteIntegers →ₜ* P :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (continuousMulEquivLimittoFiniteQuotientFunctor P).symm).comp (liftToLimit P f)

private theorem liftProfinite_frobenius (n : Degree) :
    liftProfinite P f (frobenius n) = f n := by
  apply (continuousMulEquivLimittoFiniteQuotientFunctor P).injective
  change (continuousMulEquivLimittoFiniteQuotientFunctor P)
    ((continuousMulEquivLimittoFiniteQuotientFunctor P).symm
      (liftToLimit P f (frobenius n))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  exact component_frobenius P f U n

/-- The genuine small profinite integers extend homomorphisms into compact
Hausdorff nonarchimedean groups in every target universe. -/
theorem profiniteIntegerLifting : ProfiniteIntegerLifting.{u} := by
  intro G _ _ _ _ _ f
  let P := ProfiniteGrp.of G
  let F : ProfiniteIntegers →ₜ* G := liftProfinite P f
  have hF : F.toMonoidHom.comp frobenius.toMonoidHom = f := by
    apply MonoidHom.ext
    intro n
    exact liftProfinite_frobenius P f n
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  apply ContinuousMonoidHom.ext
  intro x
  apply congrFun ((ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).equalizer
    F'.continuous F.continuous ?_) x
  funext n
  exact (DFunLike.congr_fun hF' n).trans (DFunLike.congr_fun hF n).symm

end Langlands.Weil
