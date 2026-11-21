import Langlands.Geometry.FormalGroup.PDivisibleGroupSchemeTower
import Langlands.GroupScheme.Torus.InducedProducts

/-! # Products of actual p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}} {G H G' H' G'' H'' : CommGroupScheme S}

/-- A pair of maps induces the actual group scheme map on binary products. -/
def prodMap (f : G ⟶ G') (g : H ⟶ H') : prod G H ⟶ prod G' H' :=
  Additive.ofMul (f.toMul ⊗ₘ g.toMul)

@[simp] theorem prodMap_id (G H : CommGroupScheme S) :
    prodMap (𝟙 G) (𝟙 H) = 𝟙 (prod G H) := by
  change Additive.ofMul ((𝟙 G.toGrp) ⊗ₘ (𝟙 H.toGrp)) = Additive.ofMul (𝟙 (G.toGrp ⊗ H.toGrp))
  rw [id_tensorHom_id]

@[simp] theorem prodMap_comp (f : G ⟶ G') (g : H ⟶ H') (f' : G' ⟶ G'') (g' : H' ⟶ H'') :
    prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g' :=
  congrArg Additive.ofMul (tensorHom_comp_tensorHom f.toMul g.toMul f'.toMul g'.toMul).symm

@[simp] theorem prodMap_fst (f : G ⟶ G') (g : H ⟶ H') :
    prodMap f g ≫ prodFst G' H' = prodFst G H ≫ f :=
  congrArg Additive.ofMul (tensorHom_fst f.toMul g.toMul)

@[simp] theorem prodMap_snd (f : G ⟶ G') (g : H ⟶ H') :
    prodMap f g ≫ prodSnd G' H' = prodSnd G H ≫ g :=
  congrArg Additive.ofMul (tensorHom_snd f.toMul g.toMul)

/-- Multiplication on a product is multiplication on each factor. -/
theorem prodMap_nsmul_id (G H : CommGroupScheme S) (k : ℕ) :
    prodMap (k • 𝟙 G) (k • 𝟙 H) = k • 𝟙 (prod G H) := by
  have hf : prodMap (k • 𝟙 G) (k • 𝟙 H) ≫ prodFst G H =
      (k • 𝟙 (prod G H)) ≫ prodFst G H := by
    simp
  have hg : prodMap (k • 𝟙 G) (k • 𝟙 H) ≫ prodSnd G H =
      (k • 𝟙 (prod G H)) ≫ prodSnd G H := by
    simp
  exact congrArg Additive.ofMul (CartesianMonoidalCategory.hom_ext _ _
    (congrArg Additive.toMul hf) (congrArg Additive.toMul hg))

/-- Points of the actual product, with the group law on each factor. -/
abbrev prodPoints (G H : CommGroupScheme S) (T : Over S) :
    (T ⟶ (prod G H).X) ≃* (T ⟶ G.X) × (T ⟶ H.X) :=
  GroupScheme.productPointsEquiv G.toGrp H.toGrp T

/-- The product map sends each component point along the corresponding arrow. -/
theorem prodPoints_map (f : G ⟶ G') (g : H ⟶ H') (T : Over S) (x : T ⟶ (prod G H).X) :
    prodPoints G' H' T (x ≫ (prodMap f g).toMul.hom.hom) =
      ((prodPoints G H T x).1 ≫ f.toMul.hom.hom, (prodPoints G H T x).2 ≫ g.toMul.hom.hom) := by
  apply Prod.ext
  · change (x ≫ (f.toMul.hom.hom ⊗ₘ g.toMul.hom.hom)) ≫ fst _ _ =
      (x ≫ fst _ _) ≫ f.toMul.hom.hom
    simp only [Category.assoc, tensorHom_fst]
  · change (x ≫ (f.toMul.hom.hom ⊗ₘ g.toMul.hom.hom)) ≫ snd _ _ =
      (x ≫ snd _ _) ≫ g.toMul.hom.hom
    simp only [Category.assoc, tensorHom_snd]

/-- Taking binary products preserves the actual affine fppf short exact sequence. -/
theorem AffineFppfShortExact.prod {R : CommRingCat.{u}}
    {G H J G' H' J' : CommGroupScheme (Spec R)}
    {i : G ⟶ H} {q : H ⟶ J} {i' : G' ⟶ H'} {q' : H' ⟶ J'}
    (h : AffineFppfShortExact i q) (h' : AffineFppfShortExact i' q') :
    AffineFppfShortExact (prodMap i i') (prodMap q q') := by
  refine ⟨?_, ?_, ?_⟩
  · intro A x y he
    apply (prodPoints G G' (affineTest A)).injective
    have hh := congrArg (prodPoints H H' (affineTest A)) he
    rw [prodPoints_map, prodPoints_map] at hh
    exact Prod.ext (h.1 A (congrArg Prod.fst hh)) (h'.1 A (congrArg Prod.snd hh))
  · intro A x
    let T := affineTest A
    let e := prodPoints G G' T
    let w := prodPoints H H' T x
    have hker : x ≫ (prodMap q q').toMul.hom.hom = 1 ↔
        w.1 ≫ q.toMul.hom.hom = 1 ∧ w.2 ≫ q'.toMul.hom.hom = 1 := by
      rw [← (prodPoints J J' T).injective.eq_iff, prodPoints_map, map_one]
      exact ⟨fun hq => ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩,
        fun hq => Prod.ext hq.1 hq.2⟩
    rw [hker, h.2.1 A w.1, h'.2.1 A w.2]
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
      refine ⟨e.symm (y, y'), (prodPoints H H' T).injective ?_⟩
      rw [prodPoints_map]
      change ((e (e.symm (y, y'))).1 ≫ i.toMul.hom.hom,
        (e (e.symm (y, y'))).2 ≫ i'.toMul.hom.hom) = w
      rw [MulEquiv.apply_symm_apply]
      exact Prod.ext hy hy'
    · rintro ⟨y, hy⟩
      have hh := congrArg (prodPoints H H' T) hy
      rw [prodPoints_map] at hh
      exact ⟨⟨(e y).1, congrArg Prod.fst hh⟩, ⟨(e y).2, congrArg Prod.snd hh⟩⟩
  · intro A y
    let w := prodPoints J J' (affineTest A) y
    obtain ⟨B, φ, hflat, hfp, x, hx⟩ := h.2.2 A w.1
    let a := (algSpec R).map φ.op
    obtain ⟨C, ψ, hflat', hfp', x', hx'⟩ := h'.2.2 B (a ≫ w.2)
    let b := (algSpec R).map ψ.op
    let e := prodPoints H H' (affineTest C)
    refine ⟨C, φ ≫ ψ, RingHom.FaithfullyFlat.stableUnderComposition _ _ hflat hflat',
      hfp'.comp hfp, e.symm (b ≫ x, x'), (prodPoints J J' (affineTest C)).injective ?_⟩
    have hba : (algSpec R).map (φ ≫ ψ).op = b ≫ a := (algSpec R).map_comp ψ.op φ.op
    rw [hba, prodPoints_map]
    refine Eq.trans ?_ (GroupScheme.productPointsEquiv_naturality J.toGrp J'.toGrp (b ≫ a) y).symm
    change ((e (e.symm (b ≫ x, x'))).1 ≫ q.toMul.hom.hom,
      (e (e.symm (b ≫ x, x'))).2 ≫ q'.toMul.hom.hom) = ((b ≫ a) ≫ w.1, (b ≫ a) ≫ w.2)
    rw [MulEquiv.apply_symm_apply]
    exact Prod.ext (by rw [Category.assoc, hx, ← Category.assoc])
      (hx'.trans (Category.assoc b a w.2).symm)

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

open CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- The product of two p-divisible groups on the same base, with the actual
product schemes and both arrows defined componentwise. -/
def prod (G H : PDivisibleGroup R p) : PDivisibleGroup R p where
  inclusions := {
    obj n := CommGroupScheme.prod (G.inclusions.obj n) (H.inclusions.obj n)
    map i := prodMap (G.inclusions.map i) (H.inclusions.map i)
    map_id n := by rw [G.inclusions.map_id, H.inclusions.map_id, prodMap_id]
    map_comp i j := by rw [G.inclusions.map_comp, H.inclusions.map_comp, prodMap_comp] }
  transfer i := prodMap (G.transfer i) (H.transfer i)
  transfer_id n := by rw [G.transfer_id, H.transfer_id, prodMap_id]
  transfer_comp i j := by rw [G.transfer_comp, H.transfer_comp, prodMap_comp]
  finiteLocallyFree n := by
    let a := (G.inclusions.obj n).X.hom
    let b := (H.inclusions.obj n).X.hom
    obtain ⟨ha, ha', ha''⟩ := G.finiteLocallyFree n
    obtain ⟨hb, hb', hb''⟩ := H.finiteLocallyFree n
    change IsFinite (pullback.fst a b ≫ a) ∧ Flat (pullback.fst a b ≫ a) ∧
      LocallyOfFinitePresentation (pullback.fst a b ≫ a)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  multiplication {m n} i := by
    change prodMap (G.transfer i) (H.transfer i) ≫ prodMap (G.inclusions.map i) (H.inclusions.map i) = _
    rw [← prodMap_comp, G.multiplication, H.multiplication, prodMap_nsmul_id]
  shortExact m n := (G.shortExact m n).prod (H.shortExact m n)

end Langlands.PDivisibleGroup
