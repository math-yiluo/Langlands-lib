import Langlands.Geometry.Building.ChevalleyRootFamily
import Langlands.GroupScheme.SplitExistence.OppositeFactorPairs
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.Geometry.Building.ReflectionRealizationUniqueness

/-! # Axioms V 2 and V 5 for the Chevalley root function family -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.SplitExistence
open Langlands.GroupScheme.SplitExistence.ChevalleyData
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ChevalleyRootFamily

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]
  (G : D.ChevGroup k) [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
  (omega : AddValuation k (WithTop ℝ))

/-- The family on a root point is the valuation of its coordinate. -/
theorem family_rootPt (j : J) (s : k) :
    family G omega (charOf k (P.root j)) (G.rootPt j s) = omega s := by
  rw [family_root]
  exact additiveRootValue_coordinate omega (rootCoord G j) s

/-- The valuation of an integral sign is zero. -/
theorem omega_sign (ε : ℤˣ) : omega ((ε : ℤ) : k) = 0 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · simp [AddValuation.map_neg]

/-- **Axiom V 5.** For a nonidentity root point `u` and opposite points `u', u''` whose
product with `u` normalizes the torus, the values of `u'` and `u` add to zero. -/
theorem opposite [IsAffineHom G.H.X.hom] [Mono G.t.hom.hom.left] :
    ∀ a ∈ relativeRoots G.t, ∀ u ∈ rootGroupPoints G.t a, u ≠ 1 →
      ∀ u' ∈ rootGroupPoints G.t (-a), ∀ u'' ∈ rootGroupPoints G.t (-a),
        u' * u * u'' ∈ normalizerPoints G.t → family G omega (-a) u' + family G omega a u = 0 := by
  intro a ha u hu hu1 u' hu' u'' hu'' hm
  have ha0 : a ≠ 0 := ha.1
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  obtain ⟨s, hs⟩ := (G.rootCoordEquiv j).surjective ⟨u, hu⟩
  have hus : u = G.rootPt j (Multiplicative.toAdd s) := (congrArg Subtype.val hs).symm
  have hs0 : Multiplicative.toAdd s ≠ 0 := by
    intro h0
    apply hu1
    rw [hus, h0, ChevGroup.rootPt_zero]
  obtain ⟨ε, hp⟩ := G.exists_isOppositeFactorPair_rootPt j (Units.mk0 _ hs0)
  have hq : RelativeRoot.IsOppositeFactorPair G.t (charOf k (P.root j))
      (G.rootPt j ((Units.mk0 _ hs0 : kˣ) : k)) (u', u'') := by
    refine ⟨hu', hu'', ?_⟩
    rw [Units.val_mk0, ← hus]
    exact hm
  have hx : G.rootPt j ((Units.mk0 _ hs0 : kˣ) : k) ∈
      (RelativeRoot.subgroup G.t (charOf k (P.root j))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := G.rootPt_mem j _
  have hx1 : G.rootPt j ((Units.mk0 _ hs0 : kˣ) : k) ≠ 1 := by
    rw [Units.val_mk0, ← hus]
    exact hu1
  have heq := RelativeRoot.IsOppositeFactorPair.eq G.t (isSplitTorus_Tk k P) ha0 hx hx1 hp hq
  have hu'eq : u' = G.rootPt (P.reflectionPerm j j)
      (((ε : ℤ) : k) * (((Units.mk0 _ hs0)⁻¹ : kˣ) : k)) := (congrArg Prod.fst heq).symm
  rw [hu'eq, ← ChevGroup.charOf_root_reflectionPerm_self, family_rootPt, hus, family_rootPt,
    ← omega.map_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, omega_sign]

section Reflection

variable [IsAffineHom G.H.X.hom] [Mono G.t.hom.hom.left]

/-- A normalizer point acts on characters through the reflection of a root. -/
def ActsByReflection (α : J) (m : normalizerPoints G.t) : Prop :=
  ∀ x : X, weylAction G.t m (charOf k x) = charOf k (P.reflection α x)

/-- Conjugation by a normalizer point moves the root points of a root to those of its
negative, up to a sign. -/
def ConjToNeg (α : J) (m : normalizerPoints G.t) : Prop :=
  ∃ ε : ℤˣ, ∀ s : k, (m : rationalPoints G.H) * G.rootPt α s * (m : rationalPoints G.H)⁻¹ =
    G.rootPt (P.reflectionPerm α α) (((ε : ℤ) : k) * s)

/-- A root has an explicit reflection element. -/
def HasReflectionElement (α : J) : Prop :=
  ∃ m : normalizerPoints G.t, ActsByReflection G α m ∧ ConjToNeg G α m

/-- The simple Weyl point as a normalizer point. -/
def weylNormalizer (i : b.support) : normalizerPoints G.t :=
  ⟨G.weylPoint i, G.weylPoint_mem_normalizerPoints i⟩

theorem weylNormalizer_actsByReflection (i : b.support) :
    ActsByReflection G i (weylNormalizer G i) := by
  intro x
  have hσ : normalizingAut G.t (weylNormalizer G i) = torusAut k (P.reflection i).toAddEquiv :=
    (isNormalizingPoint_normalizingAut G.t _).unique G.t (G.isNormalizingPoint_weylPoint i)
  change characterAut (normalizingAut G.t (weylNormalizer G i)) (charOf k x) = _
  rw [hσ, characterAut_apply, torusAut_inv_comp_charOf]
  congr 1

theorem ActsByReflection.inv {α : J} {m : normalizerPoints G.t} (h : ActsByReflection G α m) :
    ActsByReflection G α m⁻¹ := by
  intro x
  rw [map_inv]
  apply (LinearEquiv.symm_apply_eq _).2
  rw [h, RootPairing.reflection_same]

theorem ActsByReflection.conj {α : J} {m : normalizerPoints G.t} (h : ActsByReflection G α m)
    (j : b.support) :
    ActsByReflection G (P.reflectionPerm j α)
      (weylNormalizer G j * m * (weylNormalizer G j)⁻¹) := by
  intro x
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ActsByReflection.inv G (weylNormalizer_actsByReflection G j) x, h, weylNormalizer_actsByReflection,
    RootPairing.reflection_reflectionPerm]
  rfl

theorem hasReflectionElement_simple (i : b.support) : HasReflectionElement G i := by
  obtain ⟨ε, hε⟩ := G.exists_weylPoint_conj_rootPt i i
  exact ⟨weylNormalizer G i, weylNormalizer_actsByReflection G i, ε, hε⟩

theorem HasReflectionElement.neg {α : J} (h : HasReflectionElement G α) :
    HasReflectionElement G (P.reflectionPerm α α) := by
  obtain ⟨m, hm, ε, hε⟩ := h
  refine ⟨m⁻¹, ?_, ε, fun s => ?_⟩
  · intro x
    rw [ActsByReflection.inv G hm x]
    congr 1
    rw [RootPairing.reflection_reflectionPerm, ← sq, RootPairing.reflection_sq, one_mul]
  · have h1 := hε (((ε : ℤ) : k) * s)
    have hεε : ((ε : ℤ) : k) * (((ε : ℤ) : k) * s) = s := by
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
    rw [hεε] at h1
    rw [reflectionPerm_neg_self, Subgroup.coe_inv, inv_inv, ← h1]
    group

theorem HasReflectionElement.reflect {α : J} (h : HasReflectionElement G α) (j : b.support) :
    HasReflectionElement G (P.reflectionPerm j α) := by
  obtain ⟨m, hm, ε, hε⟩ := h
  obtain ⟨ε₁, h₁⟩ := G.exists_weylPoint_conj_rootPt j α
  obtain ⟨ε₂, h₂⟩ := G.exists_weylPoint_conj_rootPt j (P.reflectionPerm α α)
  refine ⟨weylNormalizer G j * m * (weylNormalizer G j)⁻¹, hm.conj G j, ε₂ * ε * ε₁, fun s => ?_⟩
  have hs : G.rootPt (P.reflectionPerm j α) s =
      G.weylPoint j * G.rootPt α (((ε₁ : ℤ) : k) * s) * (G.weylPoint j)⁻¹ := by
    rw [h₁]
    congr 1
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> simp
  have hconj : ∀ y : rationalPoints G.H,
      ((weylNormalizer G j * m * (weylNormalizer G j)⁻¹ : normalizerPoints G.t) :
          rationalPoints G.H) * (G.weylPoint j * y * (G.weylPoint j)⁻¹) *
        ((weylNormalizer G j * m * (weylNormalizer G j)⁻¹ : normalizerPoints G.t) :
          rationalPoints G.H)⁻¹ =
      G.weylPoint j * ((m : rationalPoints G.H) * y * (m : rationalPoints G.H)⁻¹) *
        (G.weylPoint j)⁻¹ := by
    intro y
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, weylNormalizer]
    group
  rw [hs, hconj, hε, h₂, reflectionPerm_reflectionPerm_neg]
  congr 1
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₂ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- Every root has an explicit reflection element. -/
theorem hasReflectionElement_all (α : J) :
    HasReflectionElement G α ∧ HasReflectionElement G (P.reflectionPerm α α) :=
  b.induction_reflect
    (p := fun β => HasReflectionElement G β ∧ HasReflectionElement G (P.reflectionPerm β β)) α
    (fun β h => ⟨h.2, by rw [reflectionPerm_neg_self]; exact h.1⟩)
    (fun i hi => ⟨hasReflectionElement_simple G ⟨i, hi⟩,
      (hasReflectionElement_simple G ⟨i, hi⟩).neg G⟩)
    (fun β j h hj => ⟨h.1.reflect G ⟨j, hj⟩, by
      rw [← reflectionPerm_reflectionPerm_neg]
      exact h.2.reflect G ⟨j, hj⟩⟩)

/-- A point acting by a root reflection realizes that reflection. -/
theorem realizesReflection_of_actsByReflection {α : J} {m : normalizerPoints G.t}
    (h : ActsByReflection G α m) : RealizesReflection G.t (charOf k (P.root α)) m := by
  refine ⟨?_, fun v hv => ?_⟩
  · rw [h, RootPairing.reflection_apply_self, ← charOfHom_apply, map_neg, charOfHom_apply]
  · have hsep := eq_zero_of_forall_eval_eq_zero (isSplitTorus_Tk k P) (u := m • v - v)
    apply sub_eq_zero.1
    apply hsep
    intro χ
    obtain ⟨x, rfl⟩ := (charEquiv k (X := X)).surjective χ
    rw [charEquiv_apply, map_sub, eval_normalizer_smul, ActsByReflection.inv G h x, RootPairing.reflection_apply,
      ← charOfHom_apply, map_sub, map_zsmul, eval_sub_apply, eval_zsmul_apply, charOfHom_apply,
      charOfHom_apply, hv, mul_zero, sub_zero, sub_self]

/-- Centralizer points of a Chevalley group are torus points. -/
theorem exists_eq_of_mem_centralizerPoints {z : rationalPoints G.H}
    (hz : z ∈ centralizerPoints G.t) : ∃ τ : rationalPoints (Tk (X := X) k).toGrp,
      τ ≫ G.t.hom.hom = z := by
  have h1 := centralizerPoints_le_torusCentralizer G.t hz
  rw [G.torusCentralizer_eq] at h1
  exact SubgroupFunctor.mem_range.1 h1

/-- Conjugation by a torus point scales root coordinates. -/
theorem conj_torus_rootPt (j : J) (τ : rationalPoints (Tk (X := X) k).toGrp) (s : k) :
    (τ ≫ G.t.hom.hom) * G.rootPt j s * (τ ≫ G.t.hom.hom)⁻¹ =
      G.rootPt j (((rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm
        (charOf k (P.root j))) τ : kˣ) : k) * s) := by
  have h := conj_rootCoordEquiv G j τ⁻¹ s
  rw [← map_inv, inv_inv, map_inv, inv_inv, rationalPoints.map_apply] at h
  exact h

/-- **Axiom V 2.** For a normalizer point realizing the reflection along a root, the values
on the root group and on the conjugated opposite root group differ by a constant. -/
theorem reflection :
    ∀ a ∈ relativeRoots G.t, ∀ n : normalizerPoints G.t, RealizesReflection G.t a n →
      ∃ c : ℝ, ∀ u ∈ rootGroupPoints G.t a, u ≠ 1 →
        family G omega a u =
          family G omega (-a) ((n : rationalPoints G.H) * u * (n : rationalPoints G.H)⁻¹) +
            (c : WithTop ℝ) := by
  intro a ha n hn
  have ha0 : a ≠ 0 := ha.1
  obtain ⟨α, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  obtain ⟨m, hmW, ε, hmC⟩ := (hasReflectionElement_all G α).1
  have hmR := realizesReflection_of_actsByReflection G hmW
  have hmax : IsMaximalSplitTorus G.t := G.isMaximalTorus.isMaximalSplitTorus (isSplitTorus_Tk k P)
  have : Finite (relativeWeylGroup G.t) := G.isConnectedReductive.finite_relativeWeylGroup G.t hmax
  have hinj := G.isConnectedReductive.relativeWeylAction_injective G.t hmax
  have hz := RealizesReflection.inv_mul_mem_centralizerPoints G.t (isSplitTorus_Tk k P) hinj
    ha0 hn hmR
  obtain ⟨τ, hτ⟩ := exists_eq_of_mem_centralizerPoints G hz
  set lam := ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm
    (charOf k (P.root α))) τ : kˣ) : k)
  have hlam : lam ≠ 0 := Units.ne_zero _
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff omega).2 hlam)
  refine ⟨-r, fun u hu _ => ?_⟩
  obtain ⟨s, hs⟩ := (G.rootCoordEquiv α).surjective ⟨u, hu⟩
  have hus : u = G.rootPt α (Multiplicative.toAdd s) := (congrArg Subtype.val hs).symm
  have hn' : (n : rationalPoints G.H) = (m : rationalPoints G.H) * (τ ≫ G.t.hom.hom) := by
    rw [hτ, mul_inv_cancel_left]
  have hconj : (n : rationalPoints G.H) * u * (n : rationalPoints G.H)⁻¹ =
      G.rootPt (P.reflectionPerm α α) (((ε : ℤ) : k) * (lam * Multiplicative.toAdd s)) := by
    rw [hn', hus, ← hmC]
    rw [← conj_torus_rootPt G α τ]
    group
  rw [hconj, ← ChevGroup.charOf_root_reflectionPerm_self, family_rootPt, hus, family_rootPt,
    omega.map_mul, omega_sign, zero_add, omega.map_mul, ← hr]
  induction omega (Multiplicative.toAdd s) using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    ring

end Reflection

end ChevalleyRootFamily

end Langlands.Geometry.Building
