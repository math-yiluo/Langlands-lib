import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleCohomology
import Langlands.Cohomology.LeftExactHomology
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Germs of ordinary higher direct images from the actual analytic étale site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The lifted actual ordinary points detect ordinary-open sheaf sections. -/
theorem eq_of_underlyingTopologyPointGerms_eq
    (U : Opens (localizedSpaceFunctor.obj X))
    (F : TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X))
    (s t : F.obj.obj (op U))
    (hst : ∀ (y : localizedSpaceFunctor.obj X) (hy : y ∈ U),
      (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U ⟨⟨hy⟩⟩ F.obj s =
        (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U ⟨⟨hy⟩⟩ F.obj t) :
    s = t := by
  let S : Sieve U :=
    { arrows := fun _ f => F.obj.map f.op s = F.obj.map f.op t
      downward_closed := by
        intro V W f hf g
        rw [op_comp, F.obj.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, hf] }
  have hS : S ∈ Opens.grothendieckTopology (localizedSpaceFunctor.obj X) U := by
    intro y hy
    obtain ⟨V, f, p, _, heq⟩ :=
      ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber_eq_iff'
        U ⟨⟨hy⟩⟩ s t).mp (hst y hy)
    exact ⟨V, f, heq, p.down.down⟩
  let es : ModuleCat.of R R ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)
  let et : ModuleCat.of R R ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  have he : es = et := by
    apply F.property.hom_ext ⟨S, hS⟩
    intro A
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simpa [es, et, map_smul] using congrArg (fun a => r • a) A.hf
  have he' := congrArg (fun f : ModuleCat.of R R ⟶ F.obj.obj (op U) => f (1 : R)) he
  simpa [es, et] using he'

/-- Ordinary point fibers are jointly faithful without any analytic separation assumption. -/
theorem underlyingTopologyPointFibers_jointlyFaithful :
    JointlyFaithful (fun y => (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R)) := by
  constructor
  intro F H f g hfg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply eq_of_underlyingTopologyPointGerms_eq.{u, v, uL} X R U.unop H
  intro y hy
  have he := congrArg (fun k => k
    ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U.unop ⟨⟨hy⟩⟩ F.obj s)) (hfg y)
  change (underlyingTopologyPoint.{u, v, uL} X y).presheafFiber.map f.hom
      ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U.unop ⟨⟨hy⟩⟩ F.obj s) =
    (underlyingTopologyPoint.{u, v, uL} X y).presheafFiber.map g.hom
      ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U.unop ⟨⟨hy⟩⟩ F.obj s) at he
  simpa only [GrothendieckTopology.Point.toPresheafFiber_naturality_apply] using he

/-- Derive ordinary direct image followed by its actual ordinary-point fiber. -/
def etaleUnderlyingGermCohomology (y : localizedSpaceFunctor.obj X) (q : ℕ) :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := underlyingTopology_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI : (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive :=
    etaleUnderlyingSheaf_additive.{u, v, uL} X R
  let P := (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
    (A := ModuleCat.{max u (v + 1) uL} R)
  haveI : P.Additive := Functor.additive_of_preserves_binary_products P
  (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R) ⋙ P).rightDerived q

/-- Exactness of the actual ordinary point fiber commutes it with right-derived
ordinary direct image. This asserts no local Galois interpretation. -/
def etaleUnderlyingGermDerivedIso (y : localizedSpaceFunctor.obj X) (q : ℕ) :
    etaleUnderlyingGermCohomology.{u, v, uL} X R y q ≅
      etaleUnderlyingHigherDirectImage.{u, v, uL} X R q ⋙
        (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
          (A := ModuleCat.{max u (v + 1) uL} R) := by
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := underlyingTopology_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI : (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive :=
    etaleUnderlyingSheaf_additive.{u, v, uL} X R
  let P := (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
    (A := ModuleCat.{max u (v + 1) uL} R)
  haveI : P.Additive := Functor.additive_of_preserves_binary_products P
  haveI : P.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels P
  exact @asIso _ _ _ _
    (Langlands.Cohomology.LeftExactHomology.derivedNatTrans P
      (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)) q)
    (Langlands.Cohomology.LeftExactHomology.isIso_derivedNatTrans P
      (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)) q)

/-- An ordinary higher direct image vanishes exactly when all its actual ordinary
germ cohomology modules vanish. -/
theorem isZero_etaleUnderlyingHigherDirectImage_iff_germCohomology
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    IsZero ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R q).obj F) ↔
      ∀ y : localizedSpaceFunctor.obj X,
        IsZero ((etaleUnderlyingGermCohomology.{u, v, uL} X R y q).obj F) := by
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  constructor
  · intro hz y
    let P := (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R)
    exact (P.map_isZero hz).of_iso ((etaleUnderlyingGermDerivedIso.{u, v, uL} X R y q).app F)
  · intro hz
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (underlyingTopologyPointFibers_jointlyFaithful.{u, v, uL} X R).map_injective
    intro y
    have hy : IsZero ((underlyingTopologyPoint.{u, v, uL} X y).sheafFiber.obj
        ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R q).obj F)) :=
      (hz y).of_iso ((etaleUnderlyingGermDerivedIso.{u, v, uL} X R y q).app F).symm
    exact hy.eq_of_src _ _

end Langlands.Sheaf.Equivariant.Analytic
