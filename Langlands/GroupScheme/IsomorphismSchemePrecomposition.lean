import Langlands.GroupScheme.OuterIsomorphismScheme
import Langlands.GroupScheme.RelativeInnerForm

/-! # Source precomposition of supplied Isom representatives and outer quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' H A : GroupScheme S} {U : Over S}

namespace LocalGroupIso

/-- Precompose a natural local family by an actual source-group isomorphism. -/
def precompose (e : LocalGroupIso G H U) (i : G' ≅ G) :
    LocalGroupIso G' H U where
  toFun a := ((ofIso i U).toFun a).trans (e.toFun a)
  naturality t a g := by
    change e.toFun (t ≫ a) ((t ≫ g) ≫ i.hom.hom.hom) =
      t ≫ e.toFun a (g ≫ i.hom.hom.hom)
    rw [Category.assoc, e.naturality]

@[simp] theorem precompose_toFun (e : LocalGroupIso G H U) (i : G' ≅ G)
    {T : Over S} (p : T ⟶ U) (g : T ⟶ G'.X) :
    (e.precompose i).toFun p g = e.toFun p (g ≫ i.hom.hom.hom) := rfl

@[simp] theorem precompose_refine (e : LocalGroupIso G H U) (i : G' ≅ G)
    {V : Over S} (r : V ⟶ U) :
    (e.precompose i).refine r = (e.refine r).precompose i := rfl

@[simp] theorem precompose_symm (e : LocalGroupIso G H U) (i : G' ≅ G) :
    (e.precompose i).precompose i.symm = e := by
  apply ext_toFun
  intro T p g
  change e.toFun p ((g ≫ i.inv.hom.hom) ≫ i.hom.hom.hom) = e.toFun p g
  rw [Category.assoc, ← Grp.comp_hom_hom, i.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- Source precomposition is a bijection on all natural local families. -/
def precomposeEquiv (i : G' ≅ G) (U : Over S) :
    LocalGroupIso G H U ≃ LocalGroupIso G' H U where
  toFun e := e.precompose i
  invFun e := e.precompose i.symm
  left_inv e := e.precompose_symm i
  right_inv e := e.precompose_symm i.symm

end LocalGroupIso

namespace GroupIsomorphismScheme

variable (I : GroupIsomorphismScheme G H) (i : G' ≅ G)

/-- Change the source of a supplied representative, retaining its actual parameter. -/
def precompose : GroupIsomorphismScheme G' H where
  parameter := I.parameter
  universalIso := I.universalIso.precompose i
  bijective T :=
    ((I.pointsEquiv T).trans (LocalGroupIso.precomposeEquiv i T)).bijective

@[simp] theorem precompose_parameter : (I.precompose i).parameter = I.parameter := rfl

@[simp] theorem precompose_pointsEquiv (T : Over S) (p : T ⟶ I.parameter) :
    (I.precompose i).pointsEquiv T p = (I.pointsEquiv T p).precompose i := rfl

/-- Source precomposition intertwines inverse-precomposition actions whenever
the two supplied automorphic actions are intertwined by the source isomorphism. -/
theorem precompose_actionHom (a : AutomorphicAction A G)
    (b : AutomorphicAction A G')
    (he : ∀ (T : Over S) (d : T ⟶ A.X) (g : T ⟶ G'.X),
      b.act d g ≫ i.hom.hom.hom = a.act d (g ≫ i.hom.hom.hom))
    {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    lift d p ≫ (I.precompose i).actionHom b = lift d p ≫ I.actionHom a := by
  apply (I.precompose i).hom_ext
  intro W t g
  change (I.precompose i).universalIso.toFun
    (t ≫ (lift d p ≫ (I.precompose i).actionHom b)) g =
      (I.precompose i).universalIso.toFun (t ≫ (lift d p ≫ I.actionHom a)) g
  dsimp only [precompose]
  simp only [← Category.assoc, comp_lift]
  calc
    _ = (I.precompose i).universalIso.toFun (t ≫ p)
        (b.act (t ≫ d)⁻¹ g) :=
      (I.precompose i).actionHom_eval b _ _ _
    _ = I.universalIso.toFun (t ≫ p)
        (a.act (t ≫ d)⁻¹ (g ≫ i.hom.hom.hom)) := by
      change I.universalIso.toFun _ (b.act _ _ ≫ i.hom.hom.hom) = _
      rw [he]
      rfl
    _ = _ := (I.actionHom_eval a _ _ _).symm

end GroupIsomorphismScheme

namespace OuterIsomorphismScheme

variable {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a) (i : G' ≅ G)

/-- Transport an outer quotient through a compatible source-group isomorphism. -/
def precompose (b : AutomorphicAction A G')
    (he : ∀ (T : Over S) (d : T ⟶ A.X) (g : T ⟶ G'.X),
      b.act d g ≫ i.hom.hom.hom = a.act d (g ≫ i.hom.hom.hom)) :
    OuterIsomorphismScheme (I.precompose i) b where
  parameter := O.parameter
  classMap := O.classMap
  flat := O.flat
  surjective := O.surjective
  quasiCompact := O.quasiCompact
  invariant T d p :=
    (congrArg (fun z : T ⟶ I.parameter => z ≫ O.classMap)
      (I.precompose_actionHom i a b he d p)).trans (O.invariant T d p)
  orbit T p q hpq := by
    obtain ⟨d, hd, hu⟩ := O.orbit T p q hpq
    refine ⟨d, ?_, ?_⟩
    · exact (I.precompose_actionHom i a b he d p).trans hd
    · intro c hc
      exact hu c ((I.precompose_actionHom i a b he c p).symm.trans hc)

end OuterIsomorphismScheme

end Langlands.GroupScheme
