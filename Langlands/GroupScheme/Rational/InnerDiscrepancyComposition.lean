import Langlands.GroupScheme.Rational.InnerDiscrepancySymmetry
import Langlands.GroupScheme.Rational.InnerDiscrepancyRefinement

/-! # Composition and comparison of local families with inner discrepancy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H K A B : GroupScheme S} {U V : Over S}

/-- Compose two natural local group isomorphisms on a common cover. -/
def trans (e : LocalGroupIso G H U) (f : LocalGroupIso H K U) :
    LocalGroupIso G K U where
  toFun c := (e.toFun c).trans (f.toFun c)
  naturality t c g := by
    change f.toFun (t ≫ c) (e.toFun (t ≫ c) (t ≫ g)) =
      t ≫ f.toFun c (e.toFun c g)
    rw [e.naturality, f.naturality]

@[simp] theorem trans_toFun (e : LocalGroupIso G H U) (f : LocalGroupIso H K U)
    {T : Over S} (c : T ⟶ U) (g : T ⟶ G.X) :
    (e.trans f).toFun c g = f.toFun c (e.toFun c g) := rfl

/-- Compare two natural local isomorphisms with the same source. -/
def compare (e : LocalGroupIso G H U) (f : LocalGroupIso G K U) :
    LocalGroupIso H K U :=
  e.symm.trans f

@[simp] theorem compare_toFun (e : LocalGroupIso G H U) (f : LocalGroupIso G K U)
    {T : Over S} (c : T ⟶ U) (h : T ⟶ H.X) :
    (e.compare f).toFun c h = f.toFun c ((e.toFun c).symm h) := rfl

variable (e : LocalGroupIso G H U) (a : AutomorphicAction A G)
    (b : AutomorphicAction B H) (d : LocalGroupIso A B U)
    (hd : ∀ {T : Over S} (c : T ⟶ U) (x : T ⟶ A.X) (g : T ⟶ G.X),
      e.toFun c (a.act x g) = b.act (d.toFun c x) (e.toFun c g))

include d hd

/-- Inverting both equivariant local families preserves equivariance. -/
theorem symm_equivariant {T : Over S} (c : T ⟶ U) (y : T ⟶ B.X)
    (h : T ⟶ H.X) :
    e.symm.toFun c (b.act y h) =
      a.act (d.symm.toFun c y) (e.symm.toFun c h) := by
  apply (e.toFun c).injective
  change e.toFun c ((e.toFun c).symm (b.act y h)) =
    e.toFun c (a.act ((d.toFun c).symm y) ((e.toFun c).symm h))
  rw [MulEquiv.apply_symm_apply, hd, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- The discrepancy of a composite is the transported second discrepancy
multiplied by the first discrepancy, in that order. -/
theorem RepresentsDiscrepancy.trans_of_equivariant
    {f : LocalGroupIso H K U} {T : Over S} {c c' : T ⟶ U}
    {x : T ⟶ A.X} {y : T ⟶ B.X}
    (hx : e.RepresentsDiscrepancy a c c' x)
    (hy : f.RepresentsDiscrepancy b c c' y) :
    (e.trans f).RepresentsDiscrepancy a c c'
      ((d.toFun c).symm y * x) := by
  intro W t g
  change f.toFun (t ≫ c)
      (e.toFun (t ≫ c) (a.act (t ≫ ((d.toFun c).symm y * x)) g)) =
    f.toFun (t ≫ c') (e.toFun (t ≫ c') g)
  rw [MonObj.comp_mul, a.act_mul_left, hd, d.naturality,
    MulEquiv.apply_symm_apply, hx t, hy t]

/-- Inner discrepancies compose through an equivariant acting-group family. -/
theorem HasInnerDiscrepancy.trans_of_equivariant
    {f : LocalGroupIso H K U} (he : e.HasInnerDiscrepancy a)
    (hf : f.HasInnerDiscrepancy b) :
    (e.trans f).HasInnerDiscrepancy a := by
  intro T c c'
  obtain ⟨x, hx⟩ := he c c'
  obtain ⟨y, hy⟩ := hf c c'
  exact ⟨(d.toFun c).symm y * x,
    RepresentsDiscrepancy.trans_of_equivariant e a b d hd hx hy⟩

/-- Comparing two families from the same source transports the quotient
of their discrepancies by the first family's acting-group isomorphism. -/
theorem RepresentsDiscrepancy.compare_of_equivariant
    {f : LocalGroupIso G K U} {T : Over S} {c c' : T ⟶ U}
    {x y : T ⟶ A.X} (hx : e.RepresentsDiscrepancy a c c' x)
    (hy : f.RepresentsDiscrepancy a c c' y) :
    (e.compare f).RepresentsDiscrepancy b c c' (d.toFun c (y * x⁻¹)) := by
  have h : (e.symm.trans f).RepresentsDiscrepancy b c c'
      ((d.symm.toFun c).symm y * d.toFun c x⁻¹) :=
    RepresentsDiscrepancy.trans_of_equivariant
      e.symm b a d.symm (e.symm_equivariant a b d hd)
      (RepresentsDiscrepancy.symm_of_equivariant e a b d hd hx) hy
  intro W t g
  simpa only [compare, symm, MulEquiv.symm_symm, map_mul] using h t g

/-- Two inner families with a common source have an inner comparison family. -/
theorem HasInnerDiscrepancy.compare_of_equivariant
    {f : LocalGroupIso G K U} (he : e.HasInnerDiscrepancy a)
    (hf : f.HasInnerDiscrepancy a) :
    (e.compare f).HasInnerDiscrepancy b := by
  intro T c c'
  obtain ⟨x, hx⟩ := he c c'
  obtain ⟨y, hy⟩ := hf c c'
  exact ⟨d.toFun c (y * x⁻¹),
    RepresentsDiscrepancy.compare_of_equivariant e a b d hd hx hy⟩

/-- Compose local families after refining their covers to the fibre product. -/
def transOnProduct (e : LocalGroupIso G H U) (f : LocalGroupIso H K V) :
    LocalGroupIso G K (U ⊗ V) :=
  (e.refine (fst U V)).trans (f.refine (snd U V))

/-- Innerness of a composite persists when the original covers differ. -/
theorem HasInnerDiscrepancy.transOnProduct_of_equivariant
    {f : LocalGroupIso H K V} (he : e.HasInnerDiscrepancy a)
    (hf : f.HasInnerDiscrepancy b) :
    (e.transOnProduct f).HasInnerDiscrepancy a :=
  HasInnerDiscrepancy.trans_of_equivariant (e.refine (fst U V)) a b
    (d.refine (fst U V)) (fun c x g => hd (c ≫ fst U V) x g)
    (he.refine (fst U V)) (hf.refine (snd U V))

/-- Compare local families on the fibre product of their covers. -/
def compareOnProduct (e : LocalGroupIso G H U) (f : LocalGroupIso G K V) :
    LocalGroupIso H K (U ⊗ V) :=
  (e.refine (fst U V)).compare (f.refine (snd U V))

/-- Inner families on distinct covers have an inner comparison on their
common refinement, given equivariance of the first family. -/
theorem HasInnerDiscrepancy.compareOnProduct_of_equivariant
    {f : LocalGroupIso G K V} (he : e.HasInnerDiscrepancy a)
    (hf : f.HasInnerDiscrepancy a) :
    (e.compareOnProduct f).HasInnerDiscrepancy b :=
  HasInnerDiscrepancy.compare_of_equivariant (e.refine (fst U V)) a b
    (d.refine (fst U V)) (fun c x g => hd (c ≫ fst U V) x g)
    (he.refine (fst U V)) (hf.refine (snd U V))

end Langlands.GroupScheme.LocalGroupIso
