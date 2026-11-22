import Langlands.Geometry.FormalGroup.AdicAffineNilpAlgebraMaps
import Langlands.Geometry.FormalGroup.NilpFormalScheme

/-! # Zariski gluing for the affine formal spectrum -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory

namespace Langlands.FormalGroup

variable {R : Type u} [CommRing R] {π : R}

namespace Nilp.IsZariskiLocal

/-- Principal-open gluing is invariant under a natural isomorphism. -/
theorem of_iso {F G : Nilp.{u, u} R π ⥤ Type v} (e : F ≅ G)
    (h : Nilp.IsZariskiLocal G) : Nilp.IsZariskiLocal F := by
  intro B s hs points compat
  let q (a : s) := e.hom.app (B.localizationAway a.val) (points a)
  have hq (a b : s) : G.map (B.toLocalizationOverlapLeft a.val b.val) (q a) =
      G.map (B.toLocalizationOverlapRight a.val b.val) (q b) := by
    dsimp only [q]
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, compat]
  obtain ⟨y, hy, hu⟩ := h B s hs q hq
  refine ⟨e.inv.app B y, ?_, ?_⟩
  · intro a
    rw [← NatTrans.naturality_apply, hy a]
    exact Iso.hom_inv_id_apply (e.app (B.localizationAway a.val)) (points a)
  · intro z hz
    have he : e.hom.app B z = y := by
      apply hu
      intro a
      rw [← NatTrans.naturality_apply, hz a]
    exact (Iso.hom_inv_id_apply (e.app B) z).symm.trans (congrArg (e.inv.app B) he)

end Nilp.IsZariskiLocal

namespace AdicAffineChart

variable (C : AdicAffineChart π)

/-- Continuous algebra maps to discrete affine tests glue on principal-open covers. -/
theorem continuousPointFunctor_isZariskiLocal : Nilp.IsZariskiLocal C.continuousPointFunctor := by
  classical
  intro B s hs points compat
  have hglue (x : C.algebra) : ∃ y : B.obj, ∀ a : s,
      algebraMap B.obj (Localization.Away a.val) y = (points a).val x := by
    refine (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
      (fun a => (points a).val x) (fun a b => ?_)).exists
    exact congrArg (fun z : C.ContinuousPoint (B.localizationAway (a.val * b.val)) => z.val x)
      (compat a b)
  choose g hg using hglue
  have detect {x y : B.obj} (h : ∀ a : s,
      algebraMap B.obj (Localization.Away a.val) x =
        algebraMap B.obj (Localization.Away a.val) y) : x = y :=
    Localization.algebraMap_injective_of_span_eq_top s hs (funext h)
  let φ : C.algebra →ₐ[R] B.obj :=
    { toFun := g
      map_zero' := detect (fun a => by simp only [hg, map_zero])
      map_one' := detect (fun a => by simp only [hg, map_one])
      map_add' x y := detect (fun a => by simp only [map_add, hg])
      map_mul' x y := detect (fun a => by simp only [map_mul, hg])
      commutes' r := detect (fun a => by
        rw [hg, (points a).val.commutes]
        exact IsScalarTower.algebraMap_apply R B.obj (Localization.Away a.val) r) }
  choose n hn using fun a : s => (points a).property
  obtain ⟨t, ht, hspan⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  let select (a : (↑t : Set B.obj)) : s := ⟨a.val, ht a.property⟩
  let bound := t.attach.sup fun a => n (select a)
  have hbound (a : (↑t : Set B.obj)) : n (select a) ≤ bound :=
    Finset.le_sup (f := fun b => n (select b)) (t.mem_attach a)
  have hφ : ∃ j : ℕ, C.ideal ^ (j + 1) ≤ RingHom.ker φ.toRingHom := by
    refine ⟨bound, fun x hx => ?_⟩
    change g x = 0
    apply Localization.algebraMap_injective_of_span_eq_top (↑t : Set B.obj)
      ((Ideal.eq_top_iff_one _).mpr hspan)
    funext a
    change algebraMap B.obj (Localization.Away a.val) (g x) =
      algebraMap B.obj (Localization.Away a.val) 0
    rw [map_zero, hg x (select a)]
    exact hn (select a) (Ideal.pow_le_pow_right (Nat.succ_le_succ (hbound a)) hx)
  refine ⟨⟨φ, hφ⟩, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    exact AlgHom.ext fun x => hg x a
  · intro ψ hψ
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    apply detect
    intro a
    exact (congrArg (fun z : C.ContinuousPoint (B.localizationAway a.val) => z.val x)
      (hψ a)).trans (hg x a).symm

/-- The colimit defining the affine formal spectrum is Zariski local. -/
theorem nilpPointsFunctor_isZariskiLocal : Nilp.IsZariskiLocal C.nilpPointsFunctor :=
  Nilp.IsZariskiLocal.of_iso C.nilpPointsContinuousIso C.continuousPointFunctor_isZariskiLocal

end AdicAffineChart

namespace Nilp.OpenOnAffineTests

variable {F : Nilp.{u, u} R π ⥤ Type v}

/-- An isomorphism of functors is an open inclusion with full image on every affine test. -/
def of_iso {G : Nilp.{u, u} R π ⥤ Type v} (e : F ≅ G) : OpenOnAffineTests e.hom where
  injective B := (e.app B).toEquiv.injective
  image _ _ := ⊤
  factors_iff f y := ⟨fun _ => ⟨e.inv.app _ (G.map f y),
    Iso.inv_hom_id_apply (e.app _) (G.map f y)⟩, fun _ => Set.subset_univ _⟩

end Nilp.OpenOnAffineTests

namespace AdicAffineChart

private def sameUniverseChartIso (C : AdicAffineChart π) :
    C.nilpPointsFunctor ⋙ uliftFunctor.{u, u} ≅ C.nilpPointsFunctor :=
  Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫ Functor.rightUnitor _

/-- An affine formal spectrum has a formal-scheme presentation by its single affine chart. -/
def oneChartPresentation (C : AdicAffineChart π) :
    Nilp.FormalSchemePresentation.{u, u} C.nilpPointsFunctor where
  isZariskiLocal := C.nilpPointsFunctor_isZariskiLocal
  Index := PUnit
  chart _ := C
  includeChart _ := C.sameUniverseChartIso.hom
  openChart _ := Nilp.OpenOnAffineTests.of_iso C.sameUniverseChartIso
  covers _ _ _ := ⟨PUnit.unit, trivial⟩

end AdicAffineChart
end Langlands.FormalGroup
