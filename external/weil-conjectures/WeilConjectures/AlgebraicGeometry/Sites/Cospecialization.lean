/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# Points of the strict localization and cospecialization maps

Let `s : Spec Ω ⟶ S` be a geometric point and `S_(s)` the strict localization, the limit of the
pointed étale neighbourhoods `(V, v)` of `s`.

- A point `w` of a pointed étale neighbourhood `(V, v)` which generizes the image of `v` is the
  image of a point of `S_(s)` (`AlgebraicGeometry.Scheme.exists_strictLocalizationConeAll_π_app`).
  On rings: a prime of a stage of a filtered colimit of rings lifts to the colimit as soon as it
  lifts along all transition maps (`CommRingCat.exists_isPrime_comap_eq_of_isColimit`), and the
  transition maps of the neighbourhood system are étale, so their images are open.
- For a geometric point `t` of `S_(s)`, a pointed étale neighbourhood `(V, v)` of `s` is a
  pointed étale neighbourhood of `t ≫ (S_(s) ⟶ S)` through the leg `S_(s) ⟶ V`
  (`AlgebraicGeometry.Scheme.cospecializationNeighborhoodFunctor`). On stalks this gives the
  *cospecialization map* `F_s ⟶ F_t` (`AlgebraicGeometry.Scheme.cospecializationMap`), sending
  the germ of a section at `(V, v)` to its germ at the lifted point.
-/

@[expose] public section

universe w r v u

open CategoryTheory Limits Opposite

namespace CommRingCat

variable {K : Type w} [Category.{r} K] [IsFiltered K] {D : K ⥤ CommRingCat.{v}}
  [PreservesColimit D (forget CommRingCat.{v})] {c : Cocone D} (hc : IsColimit c)

include hc in
/-- **Lifting primes to a filtered colimit of rings.** Let `q` be a prime ideal of a stage
`D k₀` of a filtered colimit of commutative rings. If `q` is the contraction of a prime ideal
along every transition map `D k₀ ⟶ D k`, it is the contraction of a prime ideal of the
colimit. -/
theorem exists_isPrime_comap_eq_of_isColimit {k₀ : K} (q : Ideal (D.obj k₀)) [q.IsPrime]
    (hq : ∀ (k : K) (g : k₀ ⟶ k), ∃ Q : Ideal (D.obj k), Q.IsPrime ∧
      Q.comap (D.map g).hom = q) :
    ∃ P : Ideal c.pt, P.IsPrime ∧ P.comap (c.ι.app k₀).hom = q := by
  have hcw {k k' : K} (f : k ⟶ k') (x : D.obj k) : c.ι.app k' (D.map f x) = c.ι.app k x :=
    ConcreteCategory.congr_hom (c.w f) x
  have hmap {k k' : K} (g : k₀ ⟶ k) (f : k ⟶ k') {y : D.obj k} (hy : y ∈ q.map (D.map g).hom) :
      D.map f y ∈ q.map (D.map (g ≫ f)).hom := by
    rw [D.map_comp, CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hy
  -- the elements of the colimit coming from `q` at some stage form an ideal
  let I : Ideal c.pt :=
    { carrier := {b | ∃ (k : K) (g : k₀ ⟶ k) (y : D.obj k), y ∈ q.map (D.map g).hom ∧
        c.ι.app k y = b}
      add_mem' := by
        rintro _ _ ⟨k₁, g₁, y₁, hy₁, rfl⟩ ⟨k₂, g₂, y₂, hy₂, rfl⟩
        let k := IsFiltered.max k₁ k₂
        let e := IsFiltered.coeqHom (g₁ ≫ IsFiltered.leftToMax k₁ k₂)
          (g₂ ≫ IsFiltered.rightToMax k₁ k₂)
        have he := IsFiltered.coeq_condition (g₁ ≫ IsFiltered.leftToMax k₁ k₂)
          (g₂ ≫ IsFiltered.rightToMax k₁ k₂)
        refine ⟨_, g₁ ≫ IsFiltered.leftToMax k₁ k₂ ≫ e,
          D.map (IsFiltered.leftToMax k₁ k₂ ≫ e) y₁ + D.map (IsFiltered.rightToMax k₁ k₂ ≫ e) y₂,
          add_mem (hmap g₁ _ hy₁) ?_, by rw [map_add, hcw, hcw]⟩
        rw [← Category.assoc, he, Category.assoc]
        exact hmap g₂ _ hy₂
      zero_mem' := ⟨k₀, 𝟙 k₀, 0, zero_mem _, map_zero _⟩
      smul_mem' := by
        rintro b _ ⟨k₁, g₁, y₁, hy₁, rfl⟩
        obtain ⟨k₂, z, rfl⟩ := Concrete.isColimit_exists_rep D hc b
        refine ⟨_, g₁ ≫ IsFiltered.leftToMax k₁ k₂,
          D.map (IsFiltered.rightToMax k₁ k₂) z * D.map (IsFiltered.leftToMax k₁ k₂) y₁,
          Ideal.mul_mem_left _ _ (hmap g₁ _ hy₁), ?_⟩
        rw [map_mul, hcw, hcw, smul_eq_mul] }
  have hqI : q.map (c.ι.app k₀).hom ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine ⟨k₀, 𝟙 k₀, x, ?_, rfl⟩
    rw [D.map_id, CommRingCat.hom_id, Ideal.map_id]
    exact hx
  refine (Ideal.comap_map_eq_self_iff_of_isPrime q).1 (le_antisymm (fun a ha ↦ ?_)
    Ideal.le_comap_map)
  obtain ⟨k, g, y, hy, e⟩ := hqI ha
  obtain ⟨k', f₁, f₂, e'⟩ := Concrete.isColimit_exists_of_rep_eq D hc _ _ (e.trans (hcw g a).symm)
  let h := f₁ ≫ IsFiltered.coeqHom f₁ f₂
  have hh : f₂ ≫ IsFiltered.coeqHom f₁ f₂ = h := (IsFiltered.coeq_condition f₁ f₂).symm
  obtain ⟨Q, hQ, hQq⟩ := hq _ (g ≫ h)
  have hmem : D.map (g ≫ h) a ∈ Q := by
    have h₁ : D.map h y ∈ Q := Ideal.map_le_iff_le_comap.2 hQq.ge (hmap g h hy)
    have h₂ : D.map h y = D.map (g ≫ h) a := by
      calc D.map h y = D.map (IsFiltered.coeqHom f₁ f₂) (D.map f₁ y) := by
            rw [D.map_comp, ConcreteCategory.comp_apply]
        _ = D.map (IsFiltered.coeqHom f₁ f₂) (D.map f₂ (D.map g a)) := by rw [e']
        _ = D.map (g ≫ h) a := by
            rw [← hh, D.map_comp, D.map_comp, ConcreteCategory.comp_apply,
              ConcreteCategory.comp_apply]
    rwa [h₂] at h₁
  rw [← hQq]
  exact hmem

end CommRingCat

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The legs of `strictLocalizationConeAll s` are morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma strictLocalizationConeAll_π_app_hom (x : PointedEtaleNeighborhood s) :
    (strictLocalizationConeAll s).π.app x ≫ x.1.hom = strictLocalizationToBase s :=
  (strictLocalizationConeAll s).w (PointedEtaleNeighborhood.toBase s x)

/-- On affine pointed étale neighbourhoods the legs of `strictLocalizationConeAll s` are those
of `strictLocalizationCone s`. -/
lemma strictLocalizationConeAll_π_app_ι_obj (c : AffinePointedEtaleNeighborhood s) :
    (strictLocalizationConeAll s).π.app ((AffinePointedEtaleNeighborhood.ι s).obj c) =
      (strictLocalizationCone s).π.app c := by
  refine (Functor.Initial.extendCone_obj_π_app' (F := AffinePointedEtaleNeighborhood.ι s) _
    (𝟙 _)).trans (Category.comp_id _)

/-- A morphism of pointed étale neighbourhoods carries the base point to the base point. -/
lemma PointedEtaleNeighborhood.hom_left_base {x y : PointedEtaleNeighborhood s} (f : x ⟶ y) :
    f.1.left.base (x.2.left.base (IsLocalRing.closedPoint Ω)) =
      y.2.left.base (IsLocalRing.closedPoint Ω) := by
  have h : x.2.left ≫ f.1.left = y.2.left := congrArg CategoryTheory.CommaMorphism.left f.2
  rw [← h]
  rfl

/-- **Points of the strict localization over generizations, affine case.** -/
lemma exists_strictLocalizationCone_π_app_base_eq (c : AffinePointedEtaleNeighborhood s)
    {w : c.obj.1.left} (hw : w ⤳ c.obj.2.left.base (IsLocalRing.closedPoint Ω)) :
    ∃ p : strictLocalization s, ((strictLocalizationCone s).π.app c).base p = w := by
  let V := (affineNeighborhoodDiagram s).obj c
  let q : Spec Γ(V, ⊤) := V.toSpecΓ.base w
  obtain ⟨P, hP, hPq⟩ := CommRingCat.exists_isPrime_comap_eq_of_isColimit
    (colimit.isColimit (strictHenselizationDiagram s)) (k₀ := op c) q.asIdeal (fun d g ↦ by
      let φ := (affineNeighborhoodDiagram s).map g.unop
      have : Etale φ := instEtaleLeftDiscretePUnit g.unop.hom.1
      have hφ := PointedEtaleNeighborhood.hom_left_base s g.unop.hom
      rw [← hφ] at hw
      obtain ⟨w', -, hw'⟩ := Flat.generalizingMap φ hw
      refine ⟨((affineNeighborhoodDiagram s).obj d.unop).toSpecΓ.base w' |>.asIdeal,
        inferInstance, ?_⟩
      have h := congrArg (fun f ↦ f.base w') (Scheme.toSpecΓ_naturality φ)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      have h' : q = (Spec.map φ.appTop).base
          (((affineNeighborhoodDiagram s).obj d.unop).toSpecΓ.base w') := by
        exact (congrArg V.toSpecΓ.base hw').symm.trans h
      rw [h']
      rfl)
  refine ⟨⟨P, hP⟩, ?_⟩
  have hq : (Spec.map (colimit.ι (strictHenselizationDiagram s) (op c))).base ⟨P, hP⟩ = q :=
    PrimeSpectrum.ext hPq
  rw [strictLocalizationCone_π_app, Scheme.Hom.comp_base, TopCat.comp_app]
  refine (congrArg (inv V.toSpecΓ).base hq).trans ?_
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
  rfl

/-- **Points of the strict localization over generizations.** Let `(V, v)` be a pointed étale
neighbourhood of the geometric point `s`. Every point `w` of `V` generizing the image of `v` is
the image of a point of the strict localization `S_(s)` under the leg `S_(s) ⟶ V`. -/
theorem exists_strictLocalizationConeAll_π_app_base_eq (x : PointedEtaleNeighborhood s)
    {w : x.1.left} (hw : w ⤳ x.2.left.base (IsLocalRing.closedPoint Ω)) :
    ∃ p : strictLocalization s, ((strictLocalizationConeAll s).π.app x).base p = w := by
  obtain ⟨c, ⟨f⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s x
  have : Etale f.1.left := instEtaleLeftDiscretePUnit f.1
  rw [← PointedEtaleNeighborhood.hom_left_base s f] at hw
  obtain ⟨w', hw', rfl⟩ := Flat.generalizingMap f.1.left hw
  obtain ⟨p, hp⟩ := exists_strictLocalizationCone_π_app_base_eq s c hw'
  refine ⟨p, ?_⟩
  rw [← (strictLocalizationConeAll s).w f, Scheme.Hom.comp_base, TopCat.comp_app,
    strictLocalizationConeAll_π_app_ι_obj]
  exact congrArg f.1.left.base hp

section Cospecialization

variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s)

/-- A pointed étale neighbourhood `(V, v)` of `s` is a pointed étale neighbourhood of the
geometric point `t ≫ (S_(s) ⟶ S)` for a geometric point `t` of the strict localization `S_(s)`,
pointed by `t` followed by the leg `S_(s) ⟶ V`. -/
noncomputable def cospecializationNeighborhoodFunctor :
    PointedEtaleNeighborhood s ⥤ PointedEtaleNeighborhood (t ≫ strictLocalizationToBase s) where
  obj x :=
    { obj := x.1
      val := CategoryTheory.Over.homMk (t ≫ (strictLocalizationConeAll s).π.app x) (by simp) }
  map {x y} f := Functor.Elements.homMk f.1 (by
    apply CategoryTheory.Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans (congrArg (t ≫ ·) ((strictLocalizationConeAll s).w f)))

@[simp]
lemma cospecializationNeighborhoodFunctor_obj_fst (x : PointedEtaleNeighborhood s) :
    ((cospecializationNeighborhoodFunctor s t).obj x).1 = x.1 :=
  rfl

@[simp]
lemma cospecializationNeighborhoodFunctor_obj_snd_left (x : PointedEtaleNeighborhood s) :
    ((cospecializationNeighborhoodFunctor s t).obj x).2.left =
      t ≫ (strictLocalizationConeAll s).π.app x :=
  rfl

variable (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A]

/-- The **cospecialization map** `F_s ⟶ F_t` of a sheaf `F` on the small étale site of `S`,
from the stalk at a geometric point `s` to the stalk at a geometric point
`t ≫ (S_(s) ⟶ S)` coming from a geometric point `t` of the strict localization `S_(s)`: the
germ of a section at a pointed étale neighbourhood `(V, v)` of `s` is sent to its germ at the
point `t` followed by the leg `S_(s) ⟶ V`. For `F` a sheaf, `F_s = Γ(S_(s), F|_{S_(s)})`, and
this is the restriction to the geometric point `t`. -/
noncomputable def cospecializationMap (F : Sheaf S.smallEtaleTopology A) :
    (pointSmallEtale s).sheafFiber.obj F ⟶
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).sheafFiber.obj F :=
  colimit.pre ((Functor.Elements.π
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).fiber).op ⋙ F.obj)
    (cospecializationNeighborhoodFunctor s t).op

/-- The cospecialization map on germs: the germ at `(V, v)` of a section is sent to its germ at
`(V, t ≫ (S_(s) ⟶ V))`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_cospecializationMap (F : Sheaf S.smallEtaleTopology A)
    (x : PointedEtaleNeighborhood s) :
    (pointSmallEtale s).toPresheafFiber x.1 x.2 F.obj ≫ cospecializationMap s t A F =
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).toPresheafFiber x.1
        ((cospecializationNeighborhoodFunctor s t).obj x).2 F.obj :=
  colimit.ι_pre ((Functor.Elements.π
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).fiber).op ⋙ F.obj)
    (cospecializationNeighborhoodFunctor s t).op (op x)

end Cospecialization

end AlgebraicGeometry.Scheme
