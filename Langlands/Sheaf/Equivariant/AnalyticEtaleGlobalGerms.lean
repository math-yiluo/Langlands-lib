import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison

/-!
# Detection of global étale sections by field-valued point germs

If every underlying point is the image of an `L`-valued point, the point
germs detect global sections. The proof uses the covering definition of
the analytic étale site and the filtered-colimit description of a germ.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {R : Type (max u (v + 1) uL)} [CommRing R]

/-- The lift of an `L`-valued point to the identity object of the étale site. -/
def etaleSelfPoint (x : (localizedFieldPointFunctor L).obj X) :
    (etalePoints L h x).fiber.obj (etaleSelf X) :=
  ULift.up ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩

/-- Global germs of a module-valued étale sheaf, indexed by `L`-valued points. -/
def etaleGlobalGermMap (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    F.obj.obj (op (etaleSelf X)) →ₗ[R]
      ∀ x, ((etalePoints L h x).presheafFiber (A := ModuleCat.{max u (v + 1) uL} R)).obj
        F.obj where
  toFun s x := (etalePoints L h x).toPresheafFiber (etaleSelf X) (etaleSelfPoint L h x) F.obj s
  map_add' s t := by ext x; exact map_add _ _ _
  map_smul' r s := by ext x; exact map_smul _ _ _

/-- Vanishing of all global point germs implies vanishing of the section. -/
theorem eq_zero_of_etaleGlobalGermMap_eq_zero
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) (hs : etaleGlobalGermMap L h F s = 0) :
    s = 0 := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  let S : Sieve (etaleSelf X) :=
    { arrows := fun _ f => F.obj.map f.op s = 0
      downward_closed := by
        intro U V f hf g
        rw [op_comp, F.obj.map_comp, ModuleCat.comp_apply, hf, map_zero] }
  have hS : S ∈ etaleTopology X (etaleSelf X) := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    obtain ⟨x, hx⟩ := hX y
    have hxg :
        (etalePoints L h x).toPresheafFiber (etaleSelf X) (etaleSelfPoint L h x) F.obj s =
          (etalePoints L h x).toPresheafFiber (etaleSelf X) (etaleSelfPoint L h x) F.obj 0 := by
      simpa [etaleGlobalGermMap] using congrFun hs x
    obtain ⟨U, f, p, hp, hz⟩ :=
      ((etalePoints L h x).toPresheafFiber_eq_iff' _ _ s 0).mp hxg
    refine ⟨U, f, ?_, pointProjection L U.left p.down.1, ?_⟩
    · simpa only [map_zero] using hz
    · change localizedSpaceFunctor.map f.left (pointProjection L U.left p.down.1) = y
      rw [← pointProjection_map]
      have hp' : (localizedFieldPointFunctor L).map f.left p.down.1 = x :=
        congrArg (fun q => q.down.1) hp
      exact (congrArg (pointProjection L X) hp').trans hx
  let e : ModuleCat.of R R ⟶ F.obj.obj (op (etaleSelf X)) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)
  have he : e = 0 := by
    apply F.property.hom_ext ⟨S, hS⟩
    intro I
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simpa [e, map_smul] using congrArg (fun t => r • t) I.hf
  have := congrArg (fun f : ModuleCat.of R R ⟶ F.obj.obj (op (etaleSelf X)) => f (1 : R)) he
  simpa [e] using this

/-- The family of field-valued point germs detects equality of global sections. -/
theorem etaleGlobalGermMap_injective
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    Function.Injective (etaleGlobalGermMap L h F) := by
  intro s t hst
  apply sub_eq_zero.mp
  apply eq_zero_of_etaleGlobalGermMap_eq_zero L h hX F
  rw [map_sub, hst, sub_self]

/-- The support of a global section is empty exactly when the section is zero,
provided every underlying point is the image of an `L`-valued point. -/
theorem support_etaleSelf_eq_empty_iff
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) :
    support (etalePoints L h) F.obj s = ∅ ↔ s = 0 := by
  constructor
  · intro hs
    apply eq_zero_of_etaleGlobalGermMap_eq_zero L h hX F s
    funext x
    by_contra hx
    have hm : x ∈ support (etalePoints L h) F.obj s :=
      ⟨etaleSelfPoint L h x, hx⟩
    simp only [hs, Set.mem_empty_iff_false] at hm
  · rintro rfl
    exact support_zero F.obj (etaleSelf X)

end Langlands.Sheaf.Equivariant.Analytic
