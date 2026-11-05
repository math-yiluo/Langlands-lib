import Langlands.GroupScheme.Adjoint.CenterQuotientCommutator
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.Rational.WeightSemigroup

/-! # Uniform solvability of represented fppf subgroup products

A represented fppf-local product of a normal subgroup and another subgroup is
uniformly solvable on all tests when both factors are. The bound is the sum of the
two factor bounds.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H J P : GroupScheme S}

/-- Two flat surjective locally finitely presented maps to one test scheme have a
common refinement of the same kind, namely their fibre product. -/
theorem exists_fppf_refinement {T V₁ V₂ : Over S} (v₁ : V₁ ⟶ T) (v₂ : V₂ ⟶ T)
    (hf₁ : Flat v₁.left) (hs₁ : Surjective v₁.left)
    (hl₁ : LocallyOfFinitePresentation v₁.left)
    (hf₂ : Flat v₂.left) (hs₂ : Surjective v₂.left)
    (hl₂ : LocallyOfFinitePresentation v₂.left) :
    ∃ (V : Over S) (w₁ : V ⟶ V₁) (w₂ : V ⟶ V₂), w₁ ≫ v₁ = w₂ ≫ v₂ ∧
      Flat (w₁ ≫ v₁).left ∧ Surjective (w₁ ≫ v₁).left ∧
        LocallyOfFinitePresentation (w₁ ≫ v₁).left := by
  let V : Over S := Over.mk (pullback.fst v₁.left v₂.left ≫ V₁.hom)
  let w₁ : V ⟶ V₁ := Over.homMk (pullback.fst v₁.left v₂.left) rfl
  let w₂ : V ⟶ V₂ := Over.homMk (pullback.snd v₁.left v₂.left) (by
    change pullback.snd v₁.left v₂.left ≫ V₂.hom = pullback.fst v₁.left v₂.left ≫ V₁.hom
    rw [← Over.w v₂, ← Over.w v₁, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ v₁ = w₂ ≫ v₂ := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have : Flat v₁.left := hf₁
  have : Flat v₂.left := hf₂
  have : Surjective v₁.left := hs₁
  have : Surjective v₂.left := hs₂
  have : LocallyOfFinitePresentation v₁.left := hl₁
  have : LocallyOfFinitePresentation v₂.left := hl₂
  refine ⟨V, w₁, w₂, hw, ?_, ?_, ?_⟩
  · change Flat (pullback.fst v₁.left v₂.left ≫ v₁.left)
    infer_instance
  · change Surjective (pullback.fst v₁.left v₂.left ≫ v₁.left)
    infer_instance
  · change LocallyOfFinitePresentation (pullback.fst v₁.left v₂.left ≫ v₁.left)
    infer_instance

namespace FppfLocallyInProduct

variable {F N F' N' : SubgroupFunctor G} {T : Over S}

/-- Two local product factorizations can be realized on one common cover. -/
theorem exists_common {x y : T ⟶ G.X} (hx : FppfLocallyInProduct F N x)
    (hy : FppfLocallyInProduct F' N' y) :
    ∃ (V : Over S) (v : V ⟶ T),
      Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
        ∃ a b a' b' : V ⟶ G.X, a ∈ F.carrier V ∧ b ∈ N.carrier V ∧
          a' ∈ F'.carrier V ∧ b' ∈ N'.carrier V ∧ v ≫ x = a * b ∧ v ≫ y = a' * b' := by
  obtain ⟨V₁, v₁, hf₁, hs₁, hl₁, a₁, b₁, ha₁, hb₁, he₁⟩ := hx
  obtain ⟨V₂, v₂, hf₂, hs₂, hl₂, a₂, b₂, ha₂, hb₂, he₂⟩ := hy
  obtain ⟨V, w₁, w₂, hw, hf, hs, hl⟩ :=
    exists_fppf_refinement v₁ v₂ hf₁ hs₁ hl₁ hf₂ hs₂ hl₂
  refine ⟨V, w₁ ≫ v₁, hf, hs, hl, w₁ ≫ a₁, w₁ ≫ b₁, w₂ ≫ a₂, w₂ ≫ b₂,
    F.comp_mem w₁ ha₁, N.comp_mem w₁ hb₁, F'.comp_mem w₂ ha₂, N'.comp_mem w₂ hb₂,
    ?_, ?_⟩
  · rw [Category.assoc, he₁, MonObj.comp_mul]
  · rw [hw, Category.assoc, he₂, MonObj.comp_mul]

/-- With a normal left factor, the commutator of two local products is a local
product whose right factor is a commutator of right factors. -/
theorem commutator (hF : F.IsNormal) {C : SubgroupFunctor G} {x y : T ⟶ G.X}
    (hx : FppfLocallyInProduct F N x) (hy : FppfLocallyInProduct F N' y)
    (hC : ∀ (V : Over S) (b b' : V ⟶ G.X), b ∈ N.carrier V → b' ∈ N'.carrier V →
      ⁅b, b'⁆ ∈ C.carrier V) :
    FppfLocallyInProduct F C ⁅x, y⁆ := by
  obtain ⟨V, v, hf, hs, hl, a, b, a', b', ha, hb, ha', hb', hx', hy'⟩ :=
    hx.exists_common hy
  have : (F.carrier V).Normal := ⟨fun n hn g => hF V g n (Subgroup.mem_top _) hn⟩
  have hπa : QuotientGroup.mk' (F.carrier V) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  have hπa' : QuotientGroup.mk' (F.carrier V) a' = 1 :=
    (QuotientGroup.eq_one_iff a').mpr ha'
  refine ⟨V, v, hf, hs, hl, ⁅a * b, a' * b'⁆ * ⁅b, b'⁆⁻¹, ⁅b, b'⁆, ?_,
    hC V b b' hb hb', ?_⟩
  · have key : QuotientGroup.mk' (F.carrier V) (⁅a * b, a' * b'⁆ * ⁅b, b'⁆⁻¹) = 1 := by
      simp only [map_mul, map_inv, map_commutatorElement, hπa, hπa', one_mul,
        mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp key
  · rw [CenterQuotient.comp_commutatorElement, hx', hy', inv_mul_cancel_right]

end FppfLocallyInProduct

/-- For a normal left factor, fppf-local product membership on one test scheme
is a subgroup of the points. -/
def localProduct (F N : SubgroupFunctor G) (hF : F.IsNormal) (T : Over S) :
    Subgroup (T ⟶ G.X) where
  carrier := {x | FppfLocallyInProduct F N x}
  one_mem' := by
    change FppfLocallyInProduct F N 1
    simpa only [mul_one] using
      FppfLocallyInProduct.of_mul (F.carrier T).one_mem (N.carrier T).one_mem
  mul_mem' := by
    intro x y hx hy
    obtain ⟨V, v, hf, hs, hl, a, b, a', b', ha, hb, ha', hb', hx', hy'⟩ :=
      FppfLocallyInProduct.exists_common hx hy
    refine ⟨V, v, hf, hs, hl, a * (b * a' * b⁻¹), b * b',
      (F.carrier V).mul_mem ha (hF V b a' (Subgroup.mem_top _) ha'),
      (N.carrier V).mul_mem hb hb', ?_⟩
    rw [MonObj.comp_mul, hx', hy']
    group
  inv_mem' := by
    intro x hx
    obtain ⟨V, v, hf, hs, hl, a, b, ha, hb, he⟩ := hx
    refine ⟨V, v, hf, hs, hl, b⁻¹ * a⁻¹ * b⁻¹⁻¹, b⁻¹,
      hF V b⁻¹ a⁻¹ (Subgroup.mem_top _) ((F.carrier V).inv_mem ha),
      (N.carrier V).inv_mem hb, ?_⟩
    rw [GrpObj.comp_inv, he]
    group

/-- Precomposition with a test morphism, as a homomorphism of point groups. -/
def precompHom (X : Over S) [GrpObj X] {T T' : Over S} (a : T' ⟶ T) :
    (T ⟶ X) →* (T' ⟶ X) where
  toFun y := a ≫ y
  map_one' := MonObj.comp_one a
  map_mul' y z := MonObj.comp_mul a y z

/-- Postcomposition with a group-scheme homomorphism, as a homomorphism of point
groups. -/
def postcompHom (f : H ⟶ G) (T : Over S) : (T ⟶ H.X) →* (T ⟶ G.X) where
  toFun y := y ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' y z := MonObj.mul_comp y z _

/-- The images of the derived subgroups of the point groups of a homomorphism. -/
def derivedRange (j : J ⟶ G) (e : ℕ) : SubgroupFunctor G where
  carrier T := (derivedSeries (T ⟶ J.X) e).map (postcompHom j T)
  comp_mem a x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨a ≫ y, map_derivedSeries_le_derivedSeries (precompHom J.X a) e ⟨y, hy, rfl⟩,
      Category.assoc a y j.hom.hom⟩

/-- The zeroth derived image is the whole image. -/
theorem range_le_derivedRange_zero (j : J ⟶ G) : range j ≤ derivedRange j 0 := by
  intro V x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, by rw [derivedSeries_zero]; exact Subgroup.mem_top y, rfl⟩

/-- Commutators of two points of a derived image lie in the next derived image. -/
theorem commutator_mem_derivedRange (j : J ⟶ G) (e : ℕ) {V : Over S} {b b' : V ⟶ G.X}
    (hb : b ∈ (derivedRange j e).carrier V) (hb' : b' ∈ (derivedRange j e).carrier V) :
    ⁅b, b'⁆ ∈ (derivedRange j (e + 1)).carrier V := by
  obtain ⟨c, hc, rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hb'
  refine ⟨⁅c, c'⁆, ?_, map_commutatorElement _ _ _⟩
  rw [derivedSeries_succ]
  exact Subgroup.commutator_mem_commutator hc hc'

/-- A point of the `e`-th derived subgroup of a represented fppf product is
fppf-locally a point of the normal left factor times a point of the `e`-th derived
image of the right factor. -/
theorem fppfLocallyInProduct_derivedSeries {i : H ⟶ G} {j : J ⟶ G} {p : P ⟶ G}
    (hp : IsFppfProduct (range i) (range j) p) (hN : (range i).IsNormal) (e : ℕ)
    (T : Over S) : ∀ z ∈ derivedSeries (T ⟶ P.X) e,
      FppfLocallyInProduct (range i) (derivedRange j e) (z ≫ p.hom.hom) := by
  induction e with
  | zero =>
    intro z _
    exact ((hp.mem_range_iff T _).mp ⟨z, rfl⟩).mono le_rfl (range_le_derivedRange_zero j)
  | succ e ih =>
    intro z hz
    let ψ := postcompHom p T
    have hle : derivedSeries (T ⟶ P.X) (e + 1) ≤
        (localProduct (range i) (derivedRange j (e + 1)) hN T).comap ψ := by
      rw [derivedSeries_succ, Subgroup.commutator_le]
      intro x hx y hy
      change FppfLocallyInProduct _ _ (ψ ⁅x, y⁆)
      rw [map_commutatorElement]
      exact FppfLocallyInProduct.commutator hN (ih x hx) (ih y hy)
        (fun V b b' hb hb' => commutator_mem_derivedRange j e hb hb')
    exact hle hz

/-- A represented fppf-local product of a monic normal subgroup and another
subgroup is uniformly solvable on all tests when both factors are. -/
theorem isSolvableScheme_of_isFppfProduct (i : H ⟶ G) (j : J ⟶ G) (p : P ⟶ G)
    [Mono i.hom.hom] (hp : IsFppfProduct (range i) (range j) p)
    (hN : (range i).IsNormal) (hH : RelativeRoot.IsSolvableScheme H)
    (hJ : RelativeRoot.IsSolvableScheme J) : RelativeRoot.IsSolvableScheme P := by
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  obtain ⟨m, hm⟩ := hH
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n + m, fun T => ?_⟩
  let ψ := postcompHom p T
  let φ := postcompHom i T
  have hψ : Function.Injective ψ := fun x y h => (cancel_mono p.hom.hom).mp h
  have hjn : derivedRange j n ≤ range i := by
    intro V x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hn V] at hy
    rw [Subgroup.mem_bot.mp hy, map_one]
    exact ((range i).carrier V).one_mem
  have hbase : (derivedSeries (T ⟶ P.X) n).map ψ ≤
      (derivedSeries (T ⟶ H.X) 0).map φ := by
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    obtain ⟨y, hy⟩ := ((fppfLocallyInProduct_derivedSeries hp hN n T z hz).mono le_rfl
      hjn).mem_range_of_le i le_rfl le_rfl
    exact ⟨y, by rw [derivedSeries_zero]; exact Subgroup.mem_top y, hy⟩
  have hstep : ∀ d : ℕ, (derivedSeries (T ⟶ P.X) (n + d)).map ψ ≤
      (derivedSeries (T ⟶ H.X) d).map φ := by
    intro d
    induction d with
    | zero => exact hbase
    | succ d ih =>
      rw [← add_assoc, derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator,
        Subgroup.map_commutator]
      exact Subgroup.commutator_mono ih ih
  have h := hstep m
  rw [hm T, Subgroup.map_bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).mp (le_bot_iff.mp h)

end Langlands.GroupScheme.SubgroupFunctor
