import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Normalizer and centralizer subgroup functors, and quotients of their points

The normalizer and centralizer of a subgroup functor are tested after every refinement of the
test scheme. For a torus homomorphism `i : T ⟶ G` this gives the normalizer subgroup functor
`torusNormalizer i`; the centralizer is the published `torusCentralizer i`. At the base scheme
both agree with the published `normalizerPoints i` and `centralizerPoints i`. Over every test
scheme `U` the points give a quotient group `N(U)/Z(U)`, and `relativeWeylGroup i = N(k)/Z(k)`
maps to it by restriction.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Normalizers and centralizers of subgroup functors -/

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The normalizer of a subgroup functor `F`: a point `g` over `U` normalizes `F` when, after
every refinement `a : V ⟶ U`, conjugation by `a ≫ g` and by its inverse maps `F(V)` into
itself. -/
def normalizer (F : SubgroupFunctor G) : SubgroupFunctor G where
  carrier U :=
    { carrier := {g | ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), x ∈ F.carrier V →
        (a ≫ g) * x * (a ≫ g)⁻¹ ∈ F.carrier V ∧ (a ≫ g)⁻¹ * x * (a ≫ g) ∈ F.carrier V}
      one_mem' := by
        intro V a x hx
        rw [MonObj.comp_one, inv_one, one_mul, mul_one]
        exact ⟨hx, hx⟩
      mul_mem' := by
        intro g h hg hh V a x hx
        rw [MonObj.comp_mul, mul_inv_rev]
        constructor
        · have h2 := (hg V a _ (hh V a x hx).1).1
          simpa only [mul_assoc] using h2
        · have h2 := (hh V a _ (hg V a x hx).2).2
          simpa only [mul_assoc] using h2
      inv_mem' := by
        intro g hg V a x hx
        rw [GrpObj.comp_inv, inv_inv]
        exact ⟨(hg V a x hx).2, (hg V a x hx).1⟩ }
  comp_mem a g hg V b x hx := by
    rw [← Category.assoc]
    exact hg V (b ≫ a) x hx

/-- The centralizer of a subgroup functor `F`: a point `g` over `U` centralizes `F` when, after
every refinement `a : V ⟶ U`, the point `a ≫ g` commutes with every point of `F(V)`. -/
def centralizer (F : SubgroupFunctor G) : SubgroupFunctor G where
  carrier U :=
    { carrier := {g | ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), x ∈ F.carrier V →
        Commute (a ≫ g) x}
      one_mem' := by
        intro V a x _
        rw [MonObj.comp_one]
        exact Commute.one_left x
      mul_mem' := by
        intro g h hg hh V a x hx
        rw [MonObj.comp_mul]
        exact (hg V a x hx).mul_left (hh V a x hx)
      inv_mem' := by
        intro g hg V a x hx
        rw [GrpObj.comp_inv]
        exact (hg V a x hx).inv_left }
  comp_mem a g hg V b x hx := by
    rw [← Category.assoc]
    exact hg V (b ≫ a) x hx

variable {F : SubgroupFunctor G}

theorem mem_normalizer {U : Over S} {g : U ⟶ G.X} :
    g ∈ F.normalizer.carrier U ↔ ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), x ∈ F.carrier V →
      (a ≫ g) * x * (a ≫ g)⁻¹ ∈ F.carrier V ∧ (a ≫ g)⁻¹ * x * (a ≫ g) ∈ F.carrier V :=
  Iff.rfl

theorem mem_centralizer {U : Over S} {g : U ⟶ G.X} :
    g ∈ F.centralizer.carrier U ↔
      ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), x ∈ F.carrier V → Commute (a ≫ g) x :=
  Iff.rfl

/-- A normalizing point conjugates the points of `F` over its own test scheme into `F`. -/
theorem conj_mem_of_mem_normalizer {U : Over S} {g x : U ⟶ G.X}
    (hg : g ∈ F.normalizer.carrier U) (hx : x ∈ F.carrier U) : g * x * g⁻¹ ∈ F.carrier U := by
  simpa only [Category.id_comp] using (hg U (𝟙 U) x hx).1

/-- A centralizing point commutes with the points of `F` over its own test scheme. -/
theorem commute_of_mem_centralizer {U : Over S} {g x : U ⟶ G.X}
    (hg : g ∈ F.centralizer.carrier U) (hx : x ∈ F.carrier U) : Commute g x := by
  simpa only [Category.id_comp] using hg U (𝟙 U) x hx

/-- `F` is normalized by its normalizer. -/
theorem isNormalizedBy_normalizer (F : SubgroupFunctor G) : F.IsNormalizedBy F.normalizer :=
  fun _ _ _ hg hx => conj_mem_of_mem_normalizer hg hx

/-- Every point of a subgroup functor normalizes it. -/
theorem le_normalizer (F : SubgroupFunctor G) : F ≤ F.normalizer := by
  intro U g hg V a x hx
  have hag : a ≫ g ∈ F.carrier V := F.comp_mem a hg
  exact ⟨F.carrier V |>.mul_mem (F.carrier V |>.mul_mem hag hx) (F.carrier V |>.inv_mem hag),
    F.carrier V |>.mul_mem (F.carrier V |>.mul_mem (F.carrier V |>.inv_mem hag) hx) hag⟩

/-- The centralizer of `F` lies in its normalizer. -/
theorem centralizer_le_normalizer (F : SubgroupFunctor G) : F.centralizer ≤ F.normalizer := by
  intro U g hg V a x hx
  have h := hg V a x hx
  constructor
  · rw [h.eq, mul_inv_cancel_right]
    exact hx
  · rw [h.inv_left.eq, inv_mul_cancel_right]
    exact hx

/-- The centralizer of `F` is normalized by the normalizer of `F`. -/
theorem centralizer_isNormalizedBy_normalizer (F : SubgroupFunctor G) :
    F.centralizer.IsNormalizedBy F.normalizer := by
  intro U g z hg hz V a x hx
  have hy : (a ≫ g)⁻¹ * x * (a ≫ g) ∈ F.carrier V := (hg V a x hx).2
  have hzy := hz V a _ hy
  have hxe : x = (a ≫ g) * ((a ≫ g)⁻¹ * x * (a ≫ g)) * (a ≫ g)⁻¹ := by group
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hxe]
  exact (Commute.conj_iff (a ≫ g)).mpr hzy

/-- Over every test scheme, the centralizer points are normal in the normalizer points. -/
instance normal_centralizer_subgroupOf (F : SubgroupFunctor G) (U : Over S) :
    ((F.centralizer.carrier U).subgroupOf (F.normalizer.carrier U)).Normal :=
  ⟨fun z hz n => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact F.centralizer_isNormalizedBy_normalizer U n z n.2 hz⟩

/-- A subgroup functor has a closed representative when some closed subgroup `j : H ⟶ G`
represents it. -/
def HasClosedRepresentative (F : SubgroupFunctor G) : Prop :=
  ∃ (H : GroupScheme S) (j : H ⟶ G), IsClosedSubgroup j ∧ F.IsRepresentedBy j

end SubgroupFunctor

/-! ### The normalizer of a torus -/

section Torus

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S} (i : T.toGrp ⟶ G)

/-- The normalizer of a torus homomorphism `i : T ⟶ G`, tested after every refinement: the
normalizer of the subgroup functor of points of `G` that come from `T`. -/
def torusNormalizer : SubgroupFunctor G :=
  (SubgroupFunctor.range i).normalizer

/-- A point normalizes `i` when, after every refinement, conjugation by it and by its inverse
sends every torus point to a torus point. -/
theorem mem_torusNormalizer {U : Over S} {g : U ⟶ G.X} :
    g ∈ (torusNormalizer i).carrier U ↔
      ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
        (∃ t' : V ⟶ T.X, (a ≫ g) * (t ≫ i.hom.hom) * (a ≫ g)⁻¹ = t' ≫ i.hom.hom) ∧
          ∃ t' : V ⟶ T.X, (a ≫ g)⁻¹ * (t ≫ i.hom.hom) * (a ≫ g) = t' ≫ i.hom.hom := by
  constructor
  · intro hg V a t
    obtain ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ := hg V a (t ≫ i.hom.hom) ⟨t, rfl⟩
    exact ⟨⟨t₁, h₁.symm⟩, ⟨t₂, h₂.symm⟩⟩
  · rintro hg V a x ⟨t, rfl⟩
    obtain ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ := hg V a t
    exact ⟨⟨t₁, h₁.symm⟩, ⟨t₂, h₂.symm⟩⟩

/-- The published torus centralizer is the centralizer of the subgroup functor of torus
points. -/
theorem torusCentralizer_eq_centralizer_range :
    torusCentralizer i = (SubgroupFunctor.range i).centralizer := by
  apply SubgroupFunctor.ext
  intro U
  ext g
  constructor
  · rintro hg V a x ⟨t, rfl⟩
    exact hg V a t
  · intro hg V a t
    exact hg V a (t ≫ i.hom.hom) ⟨t, rfl⟩

theorem torusCentralizer_le_torusNormalizer : torusCentralizer i ≤ torusNormalizer i := by
  rw [torusCentralizer_eq_centralizer_range]
  exact SubgroupFunctor.centralizer_le_normalizer _

theorem torusCentralizer_isNormalizedBy_torusNormalizer :
    (torusCentralizer i).IsNormalizedBy (torusNormalizer i) := by
  rw [torusCentralizer_eq_centralizer_range]
  exact SubgroupFunctor.centralizer_isNormalizedBy_normalizer _

/-- Over every test scheme, the torus centralizer points are normal in the torus normalizer
points. -/
instance normal_torusCentralizer_subgroupOf (U : Over S) :
    (((torusCentralizer i).carrier U).subgroupOf ((torusNormalizer i).carrier U)).Normal := by
  rw [torusCentralizer_eq_centralizer_range]
  exact SubgroupFunctor.normal_centralizer_subgroupOf _ U

/-! ### Comparison with the normalizer points at the base -/

variable {i}

/-- Conjugation of a torus point by the constant point of a normalizing base point. -/
theorem IsNormalizingPoint.conj_comp {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (V : Over S) (t : V ⟶ T.X) :
    G.constantPoint n V * (t ≫ i.hom.hom) * (G.constantPoint n V)⁻¹ =
      (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom := by
  rw [← comp_innerIso_hom]
  have h' := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom) h
  simpa only [Grp.comp_hom_hom, Category.assoc] using h'

/-- A restriction of a base point is its constant point. -/
theorem comp_eq_constantPoint {V : Over S} (a : V ⟶ Over.mk (𝟙 S)) (n : Over.mk (𝟙 S) ⟶ G.X) :
    a ≫ n = G.constantPoint n V := by
  simpa only [constantPoint_self] using G.constantPoint_naturality n a

variable (i)

/-- The published normalizer points lie in the normalizer subgroup functor at the base. -/
theorem normalizerPoints_le_torusNormalizer :
    normalizerPoints i ≤ (torusNormalizer i).carrier (Over.mk (𝟙 S)) := by
  rintro n ⟨σ, hσ⟩
  rw [mem_torusNormalizer]
  intro V a t
  rw [comp_eq_constantPoint a n]
  refine ⟨⟨t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom, hσ.conj_comp V t⟩,
    ⟨t ≫ (CommGroupScheme.groupHom σ.symm.hom).hom.hom, ?_⟩⟩
  have h := hσ.inv.conj_comp V t
  rwa [constantPoint_inv, inv_inv] at h

/-- The published centralizer points lie in the torus centralizer at the base. -/
theorem centralizerPoints_le_torusCentralizer :
    centralizerPoints i ≤ (torusCentralizer i).carrier (Over.mk (𝟙 S)) :=
  (torusCentralizer_carrier_base i).ge

/-- Conversely, for a monomorphism `i`, every normalizing point at the base normalizes `i`
through an automorphism of `T`. The automorphism is obtained by comparing the two
representations of the torus points by `i` and by `i` followed by inner conjugation. -/
theorem torusNormalizer_le_normalizerPoints [Mono i.hom.hom.left] :
    (torusNormalizer i).carrier (Over.mk (𝟙 S)) ≤ normalizerPoints i := by
  intro n hn
  rw [mem_torusNormalizer] at hn
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsIso (G.innerIso n).hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over S)).mapIso (G.innerIso n)).hom)
  have hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  have hrange : SubgroupFunctor.range (i ≫ (G.innerIso n).hom) = SubgroupFunctor.range i := by
    apply SubgroupFunctor.ext
    intro V
    ext x
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨t, ht⟩, -⟩ := hn V (Over.homMk V.hom (by simp)) y
      refine ⟨t, ?_⟩
      rw [← ht, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
        comp_eq_constantPoint]
    · rintro ⟨t, rfl⟩
      obtain ⟨-, ⟨y, hy⟩⟩ := hn V (Over.homMk V.hom (by simp)) t
      refine ⟨y, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, ← hy, comp_innerIso_hom, comp_eq_constantPoint]
      group
  have hj : (SubgroupFunctor.range i).IsRepresentedBy (i ≫ (G.innerIso n).hom) := by
    refine ⟨?_, hrange⟩
    rw [Grp.comp_hom_hom]
    infer_instance
  let e := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj hi
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact ⟨σ, (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hj hi).symm⟩

/-- For a monomorphism `i`, the normalizer subgroup functor at the base is exactly the
published group `normalizerPoints i`. -/
theorem torusNormalizer_carrier_base [Mono i.hom.hom.left] :
    (torusNormalizer i).carrier (Over.mk (𝟙 S)) = normalizerPoints i :=
  le_antisymm (torusNormalizer_le_normalizerPoints i) (normalizerPoints_le_torusNormalizer i)

/-! ### Quotients of points and restriction from the base -/

/-- The quotient `N(U)/Z(U)` of the normalizer points over a test scheme `U` by the centralizer
points over `U`. This is a quotient of groups of points, not the points of a quotient
scheme. -/
abbrev pointWeylGroup (U : Over S) : Type u :=
  (torusNormalizer i).carrier U ⧸
    ((torusCentralizer i).carrier U).subgroupOf ((torusNormalizer i).carrier U)

/-- Restriction of normalizer points at the base to a test scheme `U`: `n ↦ n|_U`. -/
def normalizerPointsRestrict (U : Over S) :
    normalizerPoints i →* (torusNormalizer i).carrier U where
  toFun n := ⟨G.constantPoint n U,
    (torusNormalizer i).comp_mem _ (normalizerPoints_le_torusNormalizer i n.2)⟩
  map_one' := Subtype.ext (G.constantPoint_one U)
  map_mul' n m := Subtype.ext (G.constantPoint_mul (n : Over.mk (𝟙 S) ⟶ G.X) m U)

@[simp] theorem coe_normalizerPointsRestrict (U : Over S) (n : normalizerPoints i) :
    (normalizerPointsRestrict i U n : U ⟶ G.X) = G.constantPoint n U :=
  rfl

/-- Restriction maps centralizer points into centralizer points. -/
theorem normalizerPointsRestrict_mem_torusCentralizer (U : Over S) {n : normalizerPoints i}
    (hn : (n : Over.mk (𝟙 S) ⟶ G.X) ∈ centralizerPoints i) :
    (normalizerPointsRestrict i U n : U ⟶ G.X) ∈ (torusCentralizer i).carrier U :=
  (torusCentralizer i).comp_mem _ (centralizerPoints_le_torusCentralizer i hn)

end Torus

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- The restriction homomorphism `relativeWeylGroup i = N(k)/Z(k) → N(U)/Z(U)`. -/
def relativeWeylGroupRestrict (U : Over (Spec (CommRingCat.of k))) :
    relativeWeylGroup i →* pointWeylGroup i U :=
  QuotientGroup.map _ _ (normalizerPointsRestrict i U) fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact normalizerPointsRestrict_mem_torusCentralizer i U hn

theorem relativeWeylGroupRestrict_mk (U : Over (Spec (CommRingCat.of k)))
    (n : normalizerPoints i) :
    relativeWeylGroupRestrict i U (QuotientGroup.mk n) =
      QuotientGroup.mk (normalizerPointsRestrict i U n) :=
  rfl

end Field

end Langlands.GroupScheme
