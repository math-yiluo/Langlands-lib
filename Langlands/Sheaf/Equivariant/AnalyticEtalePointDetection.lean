import Langlands.Sheaf.Equivariant.AnalyticCompactSupport
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Detection on every analytic étale object by field-valued point germs -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {R : Type (max u (v + 1) uL)} [CommRing R]

/-- If every ordinary point of an étale object is field-valued, its sections
are detected by all germs at field-valued lifts to that object. -/
theorem eq_of_etalePointGerms_eq
    (U : EtaleSite X) (hU : Function.Surjective (pointProjection L U.left))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s t : F.obj.obj (op U))
    (hst : ∀ (x : (localizedFieldPointFunctor L).obj X)
      (p : (etalePoints L h x).fiber.obj U),
      (etalePoints L h x).toPresheafFiber U p F.obj s =
        (etalePoints L h x).toPresheafFiber U p F.obj t) :
    s = t := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  let S : Sieve U :=
    { arrows := fun _ f => F.obj.map f.op s = F.obj.map f.op t
      downward_closed := by
        intro V W f hf g
        rw [op_comp, F.obj.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, hf] }
  have hS : S ∈ etaleTopology X U := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    obtain ⟨p, hp⟩ := hU y
    let x := (localizedFieldPointFunctor L).map U.hom p
    let q : (etalePoints L h x).fiber.obj U := ULift.up ⟨p, rfl⟩
    obtain ⟨V, f, r, hr, heq⟩ :=
      ((etalePoints L h x).toPresheafFiber_eq_iff' U q s t).mp (hst x q)
    refine ⟨V, f, heq, pointProjection L V.left r.down.1, ?_⟩
    change localizedSpaceFunctor.map f.left (pointProjection L V.left r.down.1) = y
    rw [← pointProjection_map]
    have hr' : (localizedFieldPointFunctor L).map f.left r.down.1 = p :=
      congrArg (fun a => a.down.1) hr
    exact (congrArg (pointProjection L U.left) hr').trans hp
  let es : ModuleCat.of R R ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)
  let et : ModuleCat.of R R ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  have he : es = et := by
    apply F.property.hom_ext ⟨S, hS⟩
    intro I
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simpa [es, et, map_smul] using congrArg (fun a => r • a) I.hf
  have := congrArg (fun f : ModuleCat.of R R ⟶ F.obj.obj (op U) => f (1 : R)) he
  simpa [es, et] using this

/-- Surjectivity over every étale object makes the actual point fibres
jointly faithful on all module-valued sheaves. -/
theorem etalePointFibers_jointlyFaithful_of_objectwise_surjective
    (hU : ∀ U : EtaleSite X, Function.Surjective (pointProjection L U.left)) :
    JointlyFaithful (fun x => (etalePoints L h x).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R)) := by
  constructor
  intro F G f g hfg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply eq_of_etalePointGerms_eq L h U.unop (hU U.unop) G
  intro x p
  have he := congrArg (fun k =>
    k ((etalePoints L h x).toPresheafFiber U.unop p F.obj s)) (hfg x)
  change (etalePoints L h x).presheafFiber.map f.hom
      ((etalePoints L h x).toPresheafFiber U.unop p F.obj s) =
    (etalePoints L h x).presheafFiber.map g.hom
      ((etalePoints L h x).toPresheafFiber U.unop p F.obj s) at he
  simpa only [GrothendieckTopology.Point.toPresheafFiber_naturality_apply] using he

end Langlands.Sheaf.Equivariant.Analytic
