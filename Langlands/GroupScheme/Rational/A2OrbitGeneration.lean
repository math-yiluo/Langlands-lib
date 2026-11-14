import Langlands.GroupScheme.Rational.A2OrbitTorusPart
import Langlands.GroupScheme.Rational.SimpleCorootOrbitDecomposition
import Langlands.Geometry.Building.KPApartmentGaloisTransport

/-! # Coroot coordinates of rational torus points in the `A₂`-orbit case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme.GaloisPointComparison Langlands.Geometry.Building
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-- Rational points of a monomorphism of group schemes are injective. -/
theorem rationalPoints_map_injective_of_mono {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G) [Mono f.hom.hom.left] :
    Function.Injective (rationalPoints.map f) := by
  intro x y h
  have : Mono f.hom.hom := Over.mono_of_mono_left f.hom.hom
  exact (cancel_mono f.hom.hom).mp h

namespace SplitPinning

/-- A product of piece triples with a nontrivial merged-root coordinate is nontrivial. -/
theorem tripleProd_ne_one {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (p : SplitPinning G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ p.torus}
    {a : characterLattice S} (hS : IsSplitTorus S.toGrp)
    (hline : RestrictsToMultipliableLine f p.rootDatum a) (F : PieceFamily f p.rootDatum a)
    (ha0 : a ≠ 0) {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lp l)))
    (hg : F.tripleProd x z y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a)
    {l : Fin F.r} (hzl : z l ≠ 1) : F.tripleProd x z y ≠ 1 := by
  intro h1
  have : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono
  have := p.isReduced
  have hT := p.isSplitTorus
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice p.torus) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice p.torus) :=
    Function.Injective.isAddTorsionFree toRat hT.character_toRat_injective
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice S) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice S) :=
    Function.Injective.isAddTorsionFree toRat hS.character_toRat_injective
  have hE := splitPinnedOppositeFactorPairs k G p
  have ha : ∀ n m : ℕ, n • a = m • a → n = m := fun n m h => by
    have h' : ((n : ℤ) • a) = ((m : ℤ) • a) := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact_mod_cast smul_left_injective ℤ ha0 h'
  have hinj := F.enum_injective ha
  have hrange := F.range_enum p.inclusion p.isRootDatum hline ha
  have h1' : F.tripleProd (fun _ => 1) (fun _ => 1) (fun _ => 1) = (1 : rationalPoints G) := by
    simp [PieceFamily.tripleProd]
  have hc := F.triples_eq_of_tripleProd_eq p.inclusion hS hT hE ha0 hinj hrange hx hz hy
    (fun _ => Subgroup.one_mem _) (fun _ => Subgroup.one_mem _) (fun _ => Subgroup.one_mem _)
    hg (h1.trans h1'.symm)
  exact hzl (congrFun hc.2.1 l)

end SplitPinning

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

local instance a2OrbitGenerationAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **Coordinates of rational torus points are equivariant.** If the scalar extension of a
rational point `g` of `G` is the image of a point `x` of the pinned torus, the simple-coroot
coordinates of `x` are Galois equivariant. -/
theorem fundamentalWeightEval_action (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (hjc : IsClosedSubgroup D.inclusion) {g : rationalPoints G}
    {x : rationalPoints D.pinning.torus.toGrp}
    (hx : rationalExtend k K G g = rationalPoints.map D.pinning.inclusion x)
    (σ : K ≃ₐ[k] K) (b : D.pinning.base.support) :
    D.pinning.fundamentalWeightEval hspan (D.action σ b) x =
      Units.map σ.toMonoidHom (D.pinning.fundamentalWeightEval hspan b x) := by
  have hmono : Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion).hom.hom.left :=
    (hjc.baseChange (algebraBaseMap k K)).mono
  have hx' : rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
      (D.torusPointEquiv x) = rationalPoints.map D.pinning.inclusion x := by
    rw [D.inclusion_eq]
    rfl
  have hfix : rationalConjugate k K D.torus.toGrp σ (D.torusPointEquiv x) =
      D.torusPointEquiv x := by
    apply rationalPoints_map_injective_of_mono
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
    rw [← rationalConjugate_map, hx', ← hx, rationalConjugate_rationalExtend, hx]
  have h := D.torusCoordinates_rationalConjugate hspan σ (D.torusPointEquiv x) b
  rw [hfix] at h
  simpa [torusCoordinates, SplitPinning.simpleCorootCoordinates] using h

theorem simpleCorootProduct_mul (c₁ c₂ : D.pinning.base.support → Kˣ) :
    D.pinning.simpleCorootProduct (c₁ * c₂) =
      D.pinning.simpleCorootProduct c₁ * D.pinning.simpleCorootProduct c₂ := by
  simp only [SplitPinning.simpleCorootProduct, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

theorem simpleCorootProduct_one :
    D.pinning.simpleCorootProduct (1 : D.pinning.base.support → Kˣ) = 1 := by
  simp only [SplitPinning.simpleCorootProduct, Pi.one_apply, map_one, Finset.prod_const_one]

theorem simpleCorootProduct_inv (c : D.pinning.base.support → Kˣ) :
    D.pinning.simpleCorootProduct c⁻¹ = (D.pinning.simpleCorootProduct c)⁻¹ := by
  simp only [SplitPinning.simpleCorootProduct, Pi.inv_apply, map_inv, Finset.prod_inv_distrib]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)

/-- Equivariant unit families supported on the Galois orbit of `A`. -/
def IsOrbitFamily (A : D.pinning.base.support) (c : D.pinning.base.support → Kˣ) : Prop :=
  (∀ (σ : K ≃ₐ[k] K) (b : D.pinning.base.support), (c (D.action σ b) : K) = σ (c b)) ∧
    ∀ b, (∀ σ : K ≃ₐ[k] K, D.action σ A ≠ b) → c b = 1

/-- **The good units at `A`.** The values at `A` of equivariant unit families supported on the
orbit of `A` whose coroot products lie in the image of `G(k)^+`. -/
def orbitGoodUnits (A : D.pinning.base.support) : Subgroup Kˣ where
  carrier := {e | ∃ c, D.IsOrbitFamily A c ∧
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) ∧ c A = e}
  one_mem' := ⟨1, ⟨fun σ b => by simp, fun b _ => rfl⟩, by
    rw [D.simpleCorootProduct_one, map_one]; exact Subgroup.one_mem _, rfl⟩
  mul_mem' := by
    rintro e₁ e₂ ⟨c₁, ⟨h₁, s₁⟩, m₁, rfl⟩ ⟨c₂, ⟨h₂, s₂⟩, m₂, rfl⟩
    refine ⟨c₁ * c₂, ⟨fun σ b => ?_, fun b hb => ?_⟩, ?_, rfl⟩
    · simp only [Pi.mul_apply, Units.val_mul, h₁, h₂, map_mul]
    · simp only [Pi.mul_apply, s₁ b hb, s₂ b hb, mul_one]
    · rw [D.simpleCorootProduct_mul, map_mul]
      exact Subgroup.mul_mem _ m₁ m₂
  inv_mem' := by
    rintro e ⟨c, ⟨h, s⟩, m, rfl⟩
    refine ⟨c⁻¹, ⟨fun σ b => ?_, fun b hb => ?_⟩, ?_, rfl⟩
    · simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, h, map_inv₀]
    · simp only [Pi.inv_apply, s b hb, inv_one]
    · rw [D.simpleCorootProduct_inv, map_inv]
      exact Subgroup.inv_mem _ m

/-- Orbit families agreeing at `A` are equal. -/
theorem IsOrbitFamily.eq {A : D.pinning.base.support} {c c' : D.pinning.base.support → Kˣ}
    (hc : D.IsOrbitFamily A c) (hc' : D.IsOrbitFamily A c') (h : c A = c' A) : c = c' := by
  funext b
  by_cases hb : ∃ σ : K ≃ₐ[k] K, D.action σ A = b
  · obtain ⟨σ, rfl⟩ := hb
    apply Units.ext
    rw [hc.1, hc'.1, h]
  · push Not at hb
    rw [hc.2 b hb, hc'.2 b hb]

/-- A family in `orbitGoodUnits` at its value at `A` has coroot product in the image of
`G(k)^+`. -/
theorem mem_of_mem_orbitGoodUnits {A : D.pinning.base.support} {c : D.pinning.base.support → Kˣ}
    (hc : D.IsOrbitFamily A c) (h : c A ∈ D.orbitGoodUnits t A) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  obtain ⟨c', hc', hm, hA⟩ := h
  rw [IsOrbitFamily.eq D hc' hc hA] at hm
  exact hm

attribute [local instance] rootIndexMulAction

/-- The stabilizer of a simple root under the Galois action on simple roots. -/
def rootStabilizer (A : D.pinning.base.support) : Subgroup (K ≃ₐ[k] K) :=
  (MulAction.stabilizer (Equiv.Perm D.pinning.base.support) A).comap D.action

theorem mem_rootStabilizer {A : D.pinning.base.support} {g : K ≃ₐ[k] K} :
    g ∈ D.rootStabilizer A ↔ D.action g A = A := by
  simp [rootStabilizer, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

/-- The stabilizer of the base piece. -/
def pairStabilizer (m₀ : D.pinning.rootIndex) : Subgroup (K ≃ₐ[k] K) :=
  MulAction.stabilizer (K ≃ₐ[k] K) (D.basePair m₀)

theorem mem_pairStabilizer {m₀ : D.pinning.rootIndex} {g : K ≃ₐ[k] K} :
    g ∈ D.pairStabilizer m₀ ↔ g • D.basePair m₀ = D.basePair m₀ :=
  MulAction.mem_stabilizer_iff

section Stabilizers

variable {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))

include hm₀ hS hp₀ hq₀ hpq hline in
/-- An element of the stabilizer of the base piece fixes or exchanges its two roots. -/
theorem pairStabilizer_cases {g : K ≃ₐ[k] K} (hg : g ∈ D.pairStabilizer m₀) :
    (D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairA p₀ (D.basePair m₀) ∧
        D.action g (D.pairB q₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀)) ∨
      (D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀) ∧
        D.action g (D.pairB q₀ (D.basePair m₀)) = D.pairA p₀ (D.basePair m₀)) := by
  have h := D.pair_orient t hm₀ hS hp₀ hq₀ hpq hline g (D.basePair m₀)
  rw [D.mem_pairStabilizer.mp hg] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

include hm₀ hS hp₀ hq₀ hpq hline in
/-- An element carrying the base root `pairA` into the base piece stabilizes the base piece. -/
theorem mem_pairStabilizer_of_action {g : K ≃ₐ[k] K}
    (hg : D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairA p₀ (D.basePair m₀) ∨
      D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀)) :
    g ∈ D.pairStabilizer m₀ := by
  rw [D.mem_pairStabilizer]
  have h := D.pair_orient t hm₀ hS hp₀ hq₀ hpq hline g (D.basePair m₀)
  have hx : ((D.action g (D.pairA p₀ (D.basePair m₀)) : D.pinning.base.support) :
      D.pinning.rootIndex) = D.pairA p₀ (g • D.basePair m₀) ∨
      ((D.action g (D.pairA p₀ (D.basePair m₀)) : D.pinning.base.support) :
        D.pinning.rootIndex) = D.pairB q₀ (g • D.basePair m₀) := by
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl (congrArg Subtype.val h1.symm)
    · exact Or.inr (congrArg Subtype.val h2.symm)
  rcases hg with hg | hg
  · exact (D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inl (congrArg Subtype.val hg))
      hx).symm
  · exact (D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inr (congrArg Subtype.val hg))
      hx).symm

include hm₀ hS hp₀ hq₀ hpq hline in
theorem rootStabilizer_le_pairStabilizer :
    D.rootStabilizer (D.pairA p₀ (D.basePair m₀)) ≤ D.pairStabilizer m₀ := fun _ hg =>
  D.mem_pairStabilizer_of_action t hm₀ hS hp₀ hq₀ hpq hline (Or.inl (D.mem_rootStabilizer.mp hg))

include hpq in
theorem baseA_ne_baseB : D.pairA p₀ (D.basePair m₀) ≠ D.pairB q₀ (D.basePair m₀) := fun h =>
  D.pairA_ne_pairB hpq (D.basePair m₀) (congrArg Subtype.val h)

/-- The swapping element built from `σ₀ p₀ = q₀`. -/
def swapElement (σ₀ : K ≃ₐ[k] K) (m₀ : D.pinning.rootIndex) : K ≃ₐ[k] K :=
  D.pairElement (D.basePair m₀) * σ₀ * (D.pairElement (D.basePair m₀))⁻¹

theorem action_swapElement {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) :
    D.action (D.swapElement σ₀ m₀) (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀) := by
  simp only [swapElement, pairA, pairB, map_mul, Equiv.Perm.mul_apply, map_inv]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply, hσ₀]

include hm₀ hS hp₀ hq₀ hpq hline in
theorem swapElement_mem {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) :
    D.swapElement σ₀ m₀ ∈ D.pairStabilizer m₀ :=
  D.mem_pairStabilizer_of_action t hm₀ hS hp₀ hq₀ hpq hline (Or.inr (D.action_swapElement hσ₀))

include hpq in
theorem swapElement_not_mem {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) :
    D.swapElement σ₀ m₀ ∉ D.rootStabilizer (D.pairA p₀ (D.basePair m₀)) := by
  rw [D.mem_rootStabilizer, D.action_swapElement hσ₀]
  exact (D.baseA_ne_baseB hpq).symm

include hm₀ hS hp₀ hq₀ hpq hline in
/-- The root stabilizer has index two in the pair stabilizer. -/
theorem relIndex_rootStabilizer {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) :
    (D.rootStabilizer (D.pairA p₀ (D.basePair m₀))).relIndex (D.pairStabilizer m₀) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨D.swapElement σ₀ m₀, D.swapElement_mem t hm₀ hS hp₀ hq₀ hpq hline hσ₀⟩, ?_⟩
  rintro ⟨g, hg⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, D.mem_rootStabilizer, map_mul,
    Equiv.Perm.mul_apply, D.action_swapElement hσ₀]
  have hne := D.baseA_ne_baseB (m₀ := m₀) hpq
  rcases D.pairStabilizer_cases t hm₀ hS hp₀ hq₀ hpq hline hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Or.inr ⟨rfl, fun h => hne h.symm⟩
  · rw [h1, h2]
    exact Or.inl ⟨rfl, fun h => hne h.symm⟩

end Stabilizers

theorem simplePoint_zero (b : D.pinning.base.support) : D.simplePoint b 0 = 1 := by
  have h := SplitPinning.RootParametrization.rationalPoint_add
    (D.rootMaps b).toRootParametrization 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

section Commutator

variable {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))
  (M : D.PairOrbit m₀ → D.pinning.SteinbergModifiedData)
  (hM : ∀ c, (M c).a = D.pairA p₀ c ∧ (M c).b = D.pairB q₀ c)
  (hMx : ∀ (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) (s : K),
    rationalConjugate k K G σ ((M c).xAlpha.rationalPoint s) =
      (M (σ • c)).xAlpha.rationalPoint (σ s))

include hm₀ hS hp₀ hq₀ hpq hline hM in
/-- The commutator of the base simple-root points at `1` is a merged-root point. -/
theorem exists_commutatorScalar :
    ∃ r : K, D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 =
      D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint r := by
  obtain ⟨hne, hab, hba⟩ := D.pair_pairings t hm₀ hS hp₀ hq₀ hpq hline (D.basePair m₀)
  have hα : D.pinning.rootDatum.root (M (D.basePair m₀)).alpha =
      D.pinning.rootDatum.root (D.pairA p₀ (D.basePair m₀) : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (D.pairB q₀ (D.basePair m₀) : D.pinning.rootIndex) := by
    rw [(M _).root_eq, (hM _).1, (hM _).2]
  exact D.pinning.adjacent_rationalPoint_reorder _ _ hne hab hba hα _ _ _ 1 1

variable [Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom]

include hm₀ hS hp₀ hq₀ hpq hline hM in
/-- Merged-root points of the base piece commute with the base simple-root points. -/
theorem commute_merged_simple (s c : K) :
    Commute ((M (D.basePair m₀)).xAlpha.rationalPoint s)
        (D.simplePoint (D.pairA p₀ (D.basePair m₀)) c) ∧
      Commute ((M (D.basePair m₀)).xAlpha.rationalPoint s)
        (D.simplePoint (D.pairB q₀ (D.basePair m₀)) c) := by
  have hpc := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq (D.basePair m₀)
  rw [← D.mergedAlpha_eq hm₀ M hM (D.basePair m₀)] at hpc
  obtain ⟨h1, h2, h3, h4⟩ := hpc
  have : Mono D.pinning.inclusion.hom.hom.left := D.pinning.isMaximalTorus.2.1.mono
  refine ⟨?_, ?_⟩
  · have hpc' := IsMultipliablePiece.swap (f := D.restrictMap t) (P := D.pinning.rootDatum)
      (a := characterLattice.baseChange (algebraBaseMap k K) S a) ⟨h1, h2, h3, h4⟩
    exact piece_commute_m_q D.pinning.inclusion D.pinning.isSplitTorus D.pinning.isRootDatum hline
      hpc'.1 hpc'.2.1 hpc'.2.2.1 hpc'.2.2.2 ((M _).xAlpha.rationalPoint_mem s)
      ((D.rootMaps _).toRootParametrization.rationalPoint_mem c)
  · exact piece_commute_m_q D.pinning.inclusion D.pinning.isSplitTorus D.pinning.isRootDatum hline
      h1 h2 h3 h4 ((M _).xAlpha.rationalPoint_mem s)
      ((D.rootMaps _).toRootParametrization.rationalPoint_mem c)

section Fixedness

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom] in
theorem rationalConjugate_simplePoint (g : K ≃ₐ[k] K) (b : D.pinning.base.support) (c : K) :
    rationalConjugate k K G g (D.simplePoint b c) = D.simplePoint (D.action g b) (g c) :=
  SplitPinning.RootMapsGaloisCompatible.rationalPoint k K D.rootMaps_compatible g b c

include hm₀ hS hp₀ hq₀ hpq hline hMx in
omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom] in
/-- The commutator scalar is fixed by the stabilizer of the base root `A`. -/
theorem commutatorScalar_fixed {r : K}
    (hr : D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 =
      D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint r)
    {g : K ≃ₐ[k] K} (hg : g ∈ D.rootStabilizer (D.pairA p₀ (D.basePair m₀))) : g r = r := by
  have hg' := D.rootStabilizer_le_pairStabilizer t hm₀ hS hp₀ hq₀ hpq hline hg
  have hgA := D.mem_rootStabilizer.mp hg
  have hgB : D.action g (D.pairB q₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀) := by
    rcases D.pairStabilizer_cases t hm₀ hS hp₀ hq₀ hpq hline hg' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hgA.symm.trans h1) (D.baseA_ne_baseB hpq)
  have h := congrArg (rationalConjugate k K G g) hr
  have hgc : g • D.basePair m₀ = D.basePair m₀ := D.mem_pairStabilizer.mp hg'
  simp only [map_mul, rationalConjugate_simplePoint, hMx, hgA, hgB, map_one] at h
  rw [hgc, hr] at h
  have h2 := mul_left_cancel h
  exact ((M (D.basePair m₀)).xAlpha.rationalPoint_injective h2).symm

include hm₀ hS hp₀ hq₀ hpq hline hMx in
omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom] in
/-- A swapping element of the base piece negates the commutator scalar. -/
theorem commutatorScalar_swap {r : K}
    (hr : D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 =
      D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint r)
    {g : K ≃ₐ[k] K} (hg : g ∈ D.pairStabilizer m₀)
    (hgA : D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀)) :
    g r = -r := by
  have hgB : D.action g (D.pairB q₀ (D.basePair m₀)) = D.pairA p₀ (D.basePair m₀) := by
    rcases D.pairStabilizer_cases t hm₀ hS hp₀ hq₀ hpq hline hg with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans hgA) (D.baseA_ne_baseB hpq)
    · exact h2
  have h := congrArg (rationalConjugate k K G g) hr
  have hgc : g • D.basePair m₀ = D.basePair m₀ := D.mem_pairStabilizer.mp hg
  simp only [map_mul, rationalConjugate_simplePoint, hMx, hgA, hgB, map_one] at h
  rw [hgc] at h
  have hinv : D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
      D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 =
      D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
          ((M (D.basePair m₀)).xAlpha.rationalPoint r)⁻¹ := by
    rw [hr]; group
  rw [hinv] at h
  have h2 := mul_left_cancel h
  rw [← SplitPinning.RootParametrization.rationalPoint_neg] at h2
  exact ((M (D.basePair m₀)).xAlpha.rationalPoint_injective h2).symm

include hm₀ hS hp₀ hq₀ hpq hline hM hMx in
/-- **The base triple `x_B(1) x_m(w) x_A(1)` is fixed by the stabilizer of the base piece** when
`w` is fixed by the stabilizer of `A` and `w - σ w = r` for a swapping element `σ`. -/
theorem pieceTriple_one_fixed {r w : K}
    (hr : D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 =
      D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
        D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint r)
    (hw : w ∈ IntermediateField.fixedField (D.rootStabilizer (D.pairA p₀ (D.basePair m₀))))
    {σ : K ≃ₐ[k] K}
    (hσA : D.action σ (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ (D.basePair m₀))
    (hwr : w - σ w = r) (g : K ≃ₐ[k] K) (hg : g • D.basePair m₀ = D.basePair m₀) :
    rationalConjugate k K G g (D.pieceTriple p₀ q₀ M (D.basePair m₀) 1 w 1) =
      D.pieceTriple p₀ q₀ M (D.basePair m₀) 1 w 1 := by
  have hg' : g ∈ D.pairStabilizer m₀ := D.mem_pairStabilizer.mpr hg
  have hfix : ∀ h ∈ D.rootStabilizer (D.pairA p₀ (D.basePair m₀)), h w = w := fun h hh =>
    (IntermediateField.mem_fixedField_iff _ _).mp hw h hh
  unfold pieceTriple
  simp only [map_mul, rationalConjugate_simplePoint, hMx, map_one]
  rw [hg]
  have hcm := D.commute_merged_simple t hm₀ hS hp₀ hq₀ hpq hline M hM
  have hcA : ∀ s c : K, Commute ((M (D.basePair m₀)).xAlpha.rationalPoint s)
      (D.simplePoint (D.pairA p₀ (D.basePair m₀)) c) := fun s c => (hcm s c).1
  have hcB : ∀ s c : K, Commute ((M (D.basePair m₀)).xAlpha.rationalPoint s)
      (D.simplePoint (D.pairB q₀ (D.basePair m₀)) c) := fun s c => (hcm s c).2
  rcases D.pairStabilizer_cases t hm₀ hS hp₀ hq₀ hpq hline hg' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hfix g (D.mem_rootStabilizer.mpr h1)]
  · rw [h1, h2]
    have hσg : σ⁻¹ * g ∈ D.rootStabilizer (D.pairA p₀ (D.basePair m₀)) := by
      rw [D.mem_rootStabilizer, map_mul, Equiv.Perm.mul_apply, h1, map_inv,
        Equiv.Perm.inv_eq_iff_eq, hσA]
    have hgw : g w = σ w := by
      calc g w = (σ * (σ⁻¹ * g)) w := by rw [mul_inv_cancel_left]
        _ = σ ((σ⁻¹ * g) w) := rfl
        _ = σ w := by rw [hfix _ hσg]
    rw [hgw]
    have hw' : σ w + r = w := by rw [← hwr]; ring
    calc D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint (σ w) *
          D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1
        = (M (D.basePair m₀)).xAlpha.rationalPoint (σ w) *
          (D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
            D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1) := by
          rw [← (hcA (σ w) 1).eq]; group
      _ = (M (D.basePair m₀)).xAlpha.rationalPoint (σ w) *
          D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
          (D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 *
            (M (D.basePair m₀)).xAlpha.rationalPoint r) := by
          rw [hr]; group
      _ = D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint (σ w) *
          ((M (D.basePair m₀)).xAlpha.rationalPoint r *
            D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1) := by
          rw [(hcB (σ w) 1).eq, (hcA r 1).eq]
      _ = D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1 *
          (M (D.basePair m₀)).xAlpha.rationalPoint w *
          D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1 := by
          conv_rhs => rw [← hw', SplitPinning.RootParametrization.rationalPoint_add]
          group

include hMx in
omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom] in
/-- The base triple `x_m(λ)` is fixed by the stabilizer of the base piece when `λ` is. -/
theorem pieceTriple_zero_fixed {lam : K}
    (hlam : lam ∈ IntermediateField.fixedField (D.pairStabilizer m₀))
    (g : K ≃ₐ[k] K) (hg : g • D.basePair m₀ = D.basePair m₀) :
    rationalConjugate k K G g (D.pieceTriple p₀ q₀ M (D.basePair m₀) 0 lam 0) =
      D.pieceTriple p₀ q₀ M (D.basePair m₀) 0 lam 0 := by
  unfold pieceTriple
  simp only [map_mul, simplePoint_zero, map_one, hMx]
  rw [hg, (IntermediateField.mem_fixedField_iff _ _).mp hlam g (D.mem_pairStabilizer.mpr hg)]

end Fixedness

end Commutator

end GaloisCompatiblePinningData

end Langlands.GroupScheme
