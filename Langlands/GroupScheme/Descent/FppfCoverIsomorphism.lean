import Langlands.GroupScheme.Descent.DisjointPullbackCoherence
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent

/-! # Actual group isomorphisms from a compatible covering family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent

variable {S T U : Scheme.{u}} {G H : GroupScheme S}

/-- Direct pullback of an actual base-changed isomorphism is its direct base change. -/
@[simp] theorem pullIso_mapIso (q : U ⟶ T) (f : T ⟶ S) (r : U ⟶ S)
    (hf : q ≫ f = r) (e : G ≅ H) :
    pullIso q hf hf ((baseChange f).mapIso e) = (baseChange r).mapIso e := by
  apply Iso.ext
  exact pullHom_map q f r hf e.hom

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.LocalGroupIso

open Descent

variable {S U : Scheme.{u}} {G H : GroupScheme S} (p : U ⟶ S)
    (e : (baseChange p).obj G ≅ (baseChange p).obj H)

/-- The cover-point action can be evaluated using the actual direct pullback
to the point's test scheme. -/
theorem ofBaseChangeIso_toFun_left_pullIso {Z : Over S}
    (a : Z ⟶ Over.mk p) (x : Z ⟶ G.X) :
    ((ofBaseChangeIso e).toFun a x).left =
      pullback.lift x.left (𝟙 Z.left) (by rw [Category.id_comp]; exact Over.w x) ≫
        (pullIso a.left (Over.w a) (Over.w a) e).hom.hom.hom.left ≫
          pullback.fst H.X.hom Z.hom := by
  have hx : ((coverPointsEquiv G a).symm x).left =
      pullback.lift x.left a.left (by rw [Over.w x, Over.w a]) := by
    apply pullback.hom_ext
    · have h := congrArg (fun z => z.left)
        ((coverPointsEquiv G a).apply_symm_apply x)
      simpa only [coverPointsEquiv_left, pullback.lift_fst] using h
    · exact (Over.w _).trans (pullback.lift_snd _ _ _).symm
  rw [ofBaseChangeIso_toFun_left, hx]
  symm
  exact (pullHom_eval a.left (Over.w a) (Over.w a) e.hom
    x.left (𝟙 Z.left) (by rw [Category.id_comp]; exact Over.w x)).trans
      (by simp only [Category.id_comp])

/-- Agreement of the actual direct pullbacks at every pair of cover points
makes the associated natural local family independent. -/
theorem ofBaseChangeIso_isIndependent_of_pullIso
    (he : ∀ (T : Scheme.{u}) (a b : T ⟶ U) (k : T ⟶ S)
      (ha : a ≫ p = k) (hb : b ≫ p = k),
      pullIso a ha ha e = pullIso b hb hb e) :
    (ofBaseChangeIso (U := Over.mk p) e).IsIndependent := by
  intro Z a b x
  apply Over.OverMorphism.ext
  change ((ofBaseChangeIso e).toFun a x).left =
    ((ofBaseChangeIso e).toFun b x).left
  rw [ofBaseChangeIso_toFun_left_pullIso p e a x,
    ofBaseChangeIso_toFun_left_pullIso p e b x,
    he Z.left a.left b.left Z.hom (Over.w a) (Over.w b)]

end Langlands.GroupScheme.LocalGroupIso

namespace Langlands.GroupScheme.Descent.CoverIsomorphism

open CoproductComponents

variable {S : Scheme.{u}} {G H : GroupScheme S}
    {I : Type u} {X : I → Scheme.{u}} (p : ∀ i, X i ⟶ S)

/-- The single map of a possibly infinite covering family. -/
abbrev projection : (∐ X) ⟶ S := Sigma.desc p

local instance inclusions_isIso : IsIso (Sigma.desc (fun i => Sigma.ι X i)) := by
  simpa only [Sigma.desc_ι] using (inferInstance : IsIso (𝟙 (∐ X)))

variable (e : ∀ i, (baseChange (p i)).obj G ≅ (baseChange (p i)).obj H)

/-- Compatibility is agreement on every common test of two covering members,
with the canonical direct-pullback identifications. -/
def IsCompatible : Prop :=
  ∀ (T : Scheme.{u}) (i j : I) (a : T ⟶ X i) (b : T ⟶ X j)
    (k : T ⟶ S) (ha : a ≫ p i = k) (hb : b ≫ p j = k),
    pullIso a ha ha (e i) = pullIso b hb hb (e j)

/-- Assemble the supplied actual isomorphisms over the disjoint union. -/
def assembled :
    (baseChange (projection p)).obj G ≅ (baseChange (projection p)).obj H :=
  DisjointComponents.pullbackIsoAlong (fun i => Sigma.ι X i)
    (fun i => Sigma.ι_comp_desc p i) (fun i => Sigma.ι_comp_desc p i) e

/-- The disjoint-union isomorphism recovers the supplied value on each member. -/
@[simp] theorem assembled_on_member (i : I) :
    pullIso (Sigma.ι X i) (Sigma.ι_comp_desc p i) (Sigma.ι_comp_desc p i)
      (assembled p e) = e i :=
  DisjointComponents.pullIso_pullbackIsoAlong _ _ _ e i

/-- Evaluate an assembled isomorphism at an arbitrary map with a specified
coordinate in one member of the family. -/
theorem assembled_on_coordinate {T : Scheme.{u}}
    (a : T ⟶ ∐ X) (k : T ⟶ S) (ha : a ≫ projection p = k)
    (i : I) (f : T ⟶ X i) (hf : f ≫ Sigma.ι X i = a) :
    pullIso a ha ha (assembled p e) =
      pullIso f
        (by rw [← Sigma.ι_comp_desc p i, ← Category.assoc, hf]; exact ha)
        (by rw [← Sigma.ι_comp_desc p i, ← Category.assoc, hf]; exact ha) (e i) :=
  DisjointComponents.pullIso_pullbackIsoAlong_factor _ _ _ e i f hf ha ha

/-- Compatible members give equal direct pullbacks at any two points of the
disjoint union lying over the same base map. -/
theorem assembled_pullIso_eq (he : IsCompatible p e)
    {T : Scheme.{u}} (a b : T ⟶ ∐ X) (k : T ⟶ S)
    (ha : a ≫ projection p = k) (hb : b ≫ projection p = k) :
    pullIso a ha ha (assembled p e) = pullIso b hb hb (assembled p e) := by
  apply DisjointComponents.pullIso_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  apply DisjointComponents.pullIso_ext_along
    (toBase (toBase a i ≫ b)) (fun _ => rfl) (fun _ => rfl)
  intro j
  rw [pullIso_pullIso, pullIso_pullIso, pullIso_pullIso, pullIso_pullIso]
  let q := toBase (toBase a i ≫ b) j ≫ toBase a i
  let f := toBase (toBase a i ≫ b) j ≫ toComponent a i
  let g := toComponent (toBase a i ≫ b) j
  have hf : f ≫ Sigma.ι X i = q ≫ a := by
    simp only [f, q, Category.assoc, component_condition]
  have hg : g ≫ Sigma.ι X j = q ≫ b := by
    simpa only [g, q, Category.assoc] using component_condition (toBase a i ≫ b) j
  rw [assembled_on_coordinate p e (q ≫ a) (q ≫ k)
    (by rw [Category.assoc, ha]) i f hf,
    assembled_on_coordinate p e (q ≫ b) (q ≫ k)
      (by rw [Category.assoc, hb]) j g hg]
  exact he _ i j f g (q ≫ k) _ _

/-- Compatibility on the members is enough for the all-test independence
needed by actual fppf descent. -/
theorem assembled_isIndependent (he : IsCompatible p e) :
    (LocalGroupIso.ofBaseChangeIso (U := Over.mk (projection p)) (assembled p e)).IsIndependent :=
  LocalGroupIso.ofBaseChangeIso_isIndependent_of_pullIso (projection p) (assembled p e)
    (fun _ a b k ha hb => assembled_pullIso_eq p e he a b k ha hb)

variable [Flat (projection p)] [Surjective (projection p)]
    [LocallyOfFinitePresentation (projection p)]

local instance projection_flat : Flat (Over.mk (projection p)).hom := by
  change Flat (projection p)
  infer_instance
local instance projection_surjective : Surjective (Over.mk (projection p)).hom := by
  change Surjective (projection p)
  infer_instance
local instance projection_lfp : LocallyOfFinitePresentation (Over.mk (projection p)).hom := by
  change LocallyOfFinitePresentation (projection p)
  infer_instance

/-- Glue compatible isomorphisms from an arbitrary family whose disjoint-union
map is fppf. No affine or quasi-compactness assumptions are required. -/
def descend (he : IsCompatible p e) : G ≅ H :=
  (LocalGroupIso.ofBaseChangeIso (U := Over.mk (projection p)) (assembled p e)).descendFppf
    (assembled_isIndependent p e he)

/-- Pullback to the disjoint union recovers the assembled local isomorphism. -/
theorem mapIso_descend (he : IsCompatible p e) :
    (baseChange (projection p)).mapIso (descend p e he) = assembled p e := by
  exact (LocalGroupIso.mapIso_descendFppf
    (LocalGroupIso.ofBaseChangeIso (U := Over.mk (projection p)) (assembled p e))
    (assembled_isIndependent p e he)).trans
      (LocalGroupIso.toBaseChangeIso_ofBaseChangeIso (U := Over.mk (projection p))
        (assembled p e))

/-- The global isomorphism recovers every original member isomorphism exactly. -/
@[simp] theorem descend_on_member (he : IsCompatible p e) (i : I) :
    (baseChange (p i)).mapIso (descend p e he) = e i := by
  rw [← pullIso_mapIso (Sigma.ι X i) (projection p) (p i) (Sigma.ι_comp_desc p i),
    mapIso_descend, assembled_on_member]

/-- Exact recovery on every covering member uniquely determines the global isomorphism. -/
theorem descend_unique (he : IsCompatible p e) (d : G ≅ H)
    (hd : ∀ i, (baseChange (p i)).mapIso d = e i) : d = descend p e he := by
  apply LocalGroupIso.mapIso_injective_of_fppf (U := Over.mk (projection p))
  change (baseChange (projection p)).mapIso d =
    (baseChange (projection p)).mapIso (descend p e he)
  rw [mapIso_descend]
  apply DisjointComponents.pullIso_ext_along (fun i => Sigma.ι X i)
    (fun i => Sigma.ι_comp_desc p i) (fun i => Sigma.ι_comp_desc p i)
  intro i
  rw [pullIso_mapIso, assembled_on_member, hd]

/-- A compatible fppf covering family has exactly one global group isomorphism
recovering its actual member isomorphisms. -/
theorem existsUnique_descend (he : IsCompatible p e) :
    ∃! d : G ≅ H, ∀ i, (baseChange (p i)).mapIso d = e i :=
  ⟨descend p e he, descend_on_member p e he, descend_unique p e he⟩

end Langlands.GroupScheme.Descent.CoverIsomorphism
