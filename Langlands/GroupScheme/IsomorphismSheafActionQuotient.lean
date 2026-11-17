import Langlands.GroupScheme.IsomorphismSheaf
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The action quotient of the full Isom sheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.LocalGroupIso.ActionQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {S : Scheme.{u}} {G H A : GroupScheme S}
    (a : AutomorphicAction A G)

/-- The canonical action on natural isomorphism families is inverse precomposition. -/
def act {T : Over S} (d : T ⟶ A.X) (e : LocalGroupIso G H T) :
    LocalGroupIso G H T :=
  e.twist a d⁻¹

@[simp] theorem act_one {T : Over S} (e : LocalGroupIso G H T) :
    act a 1 e = e := by
  apply ext_toFun
  intro W t g
  change e.toFun t (a.act (t ≫ (1 : T ⟶ A.X)⁻¹) g) = e.toFun t g
  simp only [inv_one, MonObj.comp_one, a.act_one_left]

theorem act_mul {T : Over S} (d d' : T ⟶ A.X) (e : LocalGroupIso G H T) :
    act a (d * d') e = act a d (act a d' e) := by
  apply ext_toFun
  intro W t g
  change e.toFun t (a.act (t ≫ (d * d')⁻¹) g) =
    e.toFun t (a.act (t ≫ d'⁻¹) (a.act (t ≫ d⁻¹) g))
  rw [mul_inv_rev, MonObj.comp_mul, a.act_mul_left]

@[simp] theorem act_refine {T V : Over S} (d : T ⟶ A.X)
    (e : LocalGroupIso G H T) (r : V ⟶ T) :
    (act a d e).refine r = act a (r ≫ d) (e.refine r) := by
  apply ext_toFun
  intro W t g
  change e.toFun (t ≫ r) (a.act ((t ≫ r) ≫ d⁻¹) g) =
    e.toFun (t ≫ r) (a.act (t ≫ (r ≫ d)⁻¹) g)
  simp only [GrpObj.comp_inv, Category.assoc]

/-- Actual acting points give an equivalence relation on full natural families. -/
def orbitSetoid (T : Over S) : Setoid (LocalGroupIso G H T) where
  r e f := ∃ d : T ⟶ A.X, e = act a d f
  iseqv :=
    { refl := fun e => ⟨1, (act_one a e).symm⟩
      symm := fun {e f} ⟨d, h⟩ => ⟨d⁻¹, by
        rw [h, ← act_mul, inv_mul_cancel, act_one]⟩
      trans := fun {e f k} ⟨d, hd⟩ ⟨d', hd'⟩ => ⟨d * d', by
        rw [hd, hd', act_mul]⟩ }

theorem orbitSetoid_refine {T V : Over S} (r : V ⟶ T)
    {e f : LocalGroupIso G H T} (h : (orbitSetoid a T).r e f) :
    (orbitSetoid a V).r (e.refine r) (f.refine r) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨r ≫ d, act_refine a d f r⟩

/-- The presheaf of actual orbits on every relative scheme. -/
def orbitPresheaf : Presheaf S where
  obj T := Quotient (orbitSetoid (H := H) a T.unop)
  map r := TypeCat.ofHom (Quotient.map (fun e => e.refine r.unop)
    (fun _ _ h => orbitSetoid_refine a r.unop h))
  map_id T := by
    ext q
    induction q using Quotient.ind with
    | _ e => exact congrArg (Quotient.mk _) (refine_id e)
  map_comp r s := by
    ext q
    induction q using Quotient.ind with
    | _ e => exact congrArg (Quotient.mk _) (refine_comp e r.unop s.unop).symm

/-- The map to actual orbit classes commutes with restriction. -/
def toOrbitPresheaf : presheaf G H ⟶ orbitPresheaf (H := H) a where
  app T := TypeCat.ofHom (Quotient.mk (orbitSetoid a T.unop))
  naturality _ _ _ := rfl

/-- The fppf sheafification of actual orbit classes; no Isom scheme is assumed. -/
def sheaf : FppfSheaf S :=
  (presheafToSheaf (fppfTopology S) (Type (u + 1))).obj (orbitPresheaf (H := H) a)

/-- The canonical class map from the full Isom sheaf. -/
def classMap : LocalGroupIso.sheaf G H (fppfTopology S) ⟶ sheaf (H := H) a :=
  ObjectProperty.homMk
    (toOrbitPresheaf a ≫ toSheafify (fppfTopology S) (orbitPresheaf a))

/-- Every section of the quotient has Isom-family representatives fppf locally. -/
theorem classMap_isLocallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (classMap (H := H) a).hom := by
  let : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (toOrbitPresheaf (H := H) a) :=
    CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ _
      (fun _ => Quotient.mk_surjective)
  change CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
    (toOrbitPresheaf a ≫ toSheafify (fppfTopology S) (orbitPresheaf a))
  infer_instance

/-- Acting by an actual point preserves the canonical class. -/
theorem classMap_act {T : Over S} (d : T ⟶ A.X) (e : LocalGroupIso G H T) :
    (classMap a).hom.app (op T) (act a d e) =
      (classMap a).hom.app (op T) e := by
  apply congrArg ((toSheafify (fppfTopology S) (orbitPresheaf a)).app (op T))
  exact Quotient.sound ⟨d, rfl⟩

/-- The sieve on which two natural isomorphism families differ by the action. -/
def orbitSieve {T : Over S} (e f : LocalGroupIso G H T) : Sieve T where
  arrows V r := ∃ d : V ⟶ A.X, e.refine r = act a d (f.refine r)
  downward_closed {V W} r := by
    rintro ⟨d, hd⟩ s
    refine ⟨s ≫ d, ?_⟩
    rw [← refine_comp, hd, act_refine, refine_comp]

/-- Equality of quotient sections is an fppf-local orbit equation. -/
theorem orbitSieve_mem {T : Over S} (e f : LocalGroupIso G H T)
    (hef : (classMap a).hom.app (op T) e = (classMap a).hom.app (op T) f) :
    orbitSieve a e f ∈ fppfTopology S T := by
  let J := fppfTopology S
  let P := orbitPresheaf (H := H) a
  have h := CategoryTheory.Presheaf.equalizerSieve_mem J (toSheafify J P)
    ((toOrbitPresheaf a).app (op T) e) ((toOrbitPresheaf a).app (op T) f) hef
  refine J.superset_covering ?_ h
  intro V r hr
  exact Quotient.exact hr

/-- A faithful action on the source acts freely on each full Isom family. -/
theorem act_injective (ha : a.IsFaithful) {T : Over S} (e : LocalGroupIso G H T) :
    Function.Injective (fun d : T ⟶ A.X => act a d e) := by
  intro d d' h
  apply inv_injective
  apply ha d⁻¹ d'⁻¹
  intro W t g
  apply (e.toFun t).injective
  exact congrArg (fun k : LocalGroupIso G H T => k.toFun t g) h

/-- Freeness glues a locally supplied acting point to a unique point on the test itself. -/
theorem existsUnique_act_of_orbitSieve_mem (ha : a.IsFaithful)
    {T : Over S} (e f : LocalGroupIso G H T)
    (hR : orbitSieve a f e ∈ fppfTopology S T) :
    ∃! d : T ⟶ A.X, act a d e = f := by
  let R := orbitSieve a f e
  let x : Presieve.FamilyOfElements ((schemeYoneda S).obj A.X) R.arrows :=
    fun _ r hr => ⟨hr.choose⟩
  have hx : x.Compatible := by
    intro V W Z r s k l hk hl hrs
    apply ULift.ext
    apply act_injective a ha (e.refine (r ≫ k))
    have h₁ : act a (r ≫ hk.choose) (e.refine (r ≫ k)) =
        f.refine (r ≫ k) := by
      simpa only [act_refine, refine_comp] using
        (congrArg (fun k : LocalGroupIso G H V => k.refine r) hk.choose_spec).symm
    have h₂ : act a (s ≫ hl.choose) (e.refine (s ≫ l)) =
        f.refine (s ≫ l) := by
      simpa only [act_refine, refine_comp] using
        (congrArg (fun k : LocalGroupIso G H W => k.refine s) hl.choose_spec).symm
    change act a (r ≫ hk.choose) (e.refine (r ≫ k)) =
      act a (s ≫ hl.choose) (e.refine (r ≫ k))
    rw [h₁, hrs, h₂]
  have hA := (isSheaf_iff_isSheaf_of_type _ _).mp ((schemeSheaf S).obj A.X).property
  obtain ⟨d, hd, -⟩ := hA R hR x hx
  have hact : act a d.down e = f := by
    have hF := (isSheaf_iff_isSheaf_of_type _ _).mp
      (LocalGroupIso.isSheaf (G := G) (H := H) (fppfTopology S))
    apply (hF R hR).isSeparatedFor.ext
    intro V r hr
    change (act a d.down e).refine r = f.refine r
    rw [act_refine]
    have hdr : r ≫ d.down = hr.choose := congrArg ULift.down (hd r hr)
    rw [hdr]
    exact hr.choose_spec.symm
  exact ⟨d.down, hact, fun c hc => act_injective a ha e (hc.trans hact.symm)⟩

/-- For a faithful source action, equality of classes gives a unique acting point. -/
theorem existsUnique_act_of_classMap_eq (ha : a.IsFaithful)
    {T : Over S} (e f : LocalGroupIso G H T)
    (hef : (classMap a).hom.app (op T) e = (classMap a).hom.app (op T) f) :
    ∃! d : T ⟶ A.X, act a d e = f :=
  existsUnique_act_of_orbitSieve_mem a ha e f (orbitSieve_mem a f e hef.symm)

/-- The canonical class map has exactly the actual action orbits as its kernel. -/
theorem classMap_eq_iff (ha : a.IsFaithful)
    {T : Over S} (e f : LocalGroupIso G H T) :
    (classMap a).hom.app (op T) e = (classMap a).hom.app (op T) f ↔
      ∃ d : T ⟶ A.X, act a d e = f := by
  constructor
  · intro hef
    exact (existsUnique_act_of_classMap_eq a ha e f hef).exists
  · rintro ⟨d, rfl⟩
    exact (classMap_act a d e).symm

end Langlands.GroupScheme.LocalGroupIso.ActionQuotient
