import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots

/-! # Actual coefficient action on rational normalizer points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BasePoint

variable {S S' : Scheme.{u}} {C : CommGroupScheme S} {H : GroupScheme S}
  {j : C.toGrp ⟶ H}

/-- Normalizing-point membership respects equality of the actual point. -/
theorem IsNormalizingPoint.of_point_eq
    {n m : Over.mk (𝟙 S) ⟶ H.X} {τ : C ≅ C}
    (hn : IsNormalizingPoint j n τ) (h : m = n) : IsNormalizingPoint j m τ := by
  cases h
  exact hn

/-- Pullback preserves the actual supplied normalizing point. -/
theorem IsNormalizingPoint.baseChangeBasePoint (c : S' ⟶ S)
    {n : Over.mk (𝟙 S) ⟶ H.X} {τ : C ≅ C} (hn : IsNormalizingPoint j n τ) :
    IsNormalizingPoint ((GroupScheme.baseChange c).map j)
      (Langlands.GroupScheme.baseChangeBasePoint c H n)
      ((CommGroupScheme.baseChange c).mapIso τ) := by
  have h := congrArg (fun f => (GroupScheme.baseChange c).map f) hn
  change (GroupScheme.baseChange c).map j ≫
      (((GroupScheme.baseChange c).obj H).innerIso
        (Langlands.GroupScheme.baseChangeBasePoint c H n)).hom =
    (GroupScheme.baseChange c).map (CommGroupScheme.groupHom τ.hom) ≫
      (GroupScheme.baseChange c).map j
  simpa only [IsNormalizingPoint, Functor.map_comp, baseChange_innerIso_hom] using h

end BasePoint

section CanonicalDescent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  {C : CommGroupScheme B} {H : GroupScheme B} (j : C.toGrp ⟶ H)

/-- Canonical descent preserves the given normalizing representative itself. -/
theorem IsNormalizingPoint.baseChange_descent
    {n : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj H).X}
    {τ : (CommGroupScheme.baseChange b).obj C ≅ (CommGroupScheme.baseChange b).obj C}
    (hn : IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj C)
      ((GroupScheme.baseChange b).map j) n τ) :
    IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj C)
      ((GroupScheme.baseChange b).map j)
      (Langlands.GroupScheme.baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) n ≫
        (descentBaseChangeIso b a ha H).hom.hom.hom)
      ((CommGroupScheme.descentBaseChangeIso b a ha C).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso τ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha C) :=
  (hn.baseChangeBasePoint a).transport
    (CommGroupScheme.descentBaseChangeIso b a ha C)
    (descentBaseChangeIso b a ha H) (descentBaseChangeIso_naturality b a ha j)

/-- The generic transport theorem expressed using an identified target point. -/
theorem IsNormalizingPoint.baseChange_descent_of_eq
    {n m : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj H).X}
    {τ : (CommGroupScheme.baseChange b).obj C ≅ (CommGroupScheme.baseChange b).obj C}
    (hn : IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj C)
      ((GroupScheme.baseChange b).map j) n τ)
    (hm : m = Langlands.GroupScheme.baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) n ≫
      (descentBaseChangeIso b a ha H).hom.hom.hom) :
    IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj C)
      ((GroupScheme.baseChange b).map j) m
      ((CommGroupScheme.descentBaseChangeIso b a ha C).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso τ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha C) :=
  (hn.baseChange_descent b a ha j).of_point_eq hm

end CanonicalDescent

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

/-- Actual coefficient conjugation is pullback of the section followed by the
canonical descent comparison, with the original coefficient convention. -/
theorem rationalConjugate_eq_baseChange_descent (σ : K ≃ₐ[k] K)
    (n : rationalPoints G_K) :
    rationalConjugate k K G σ n =
      baseChangeBasePoint (galoisBaseMap k K σ) G_K n ≫
        (descentBaseChangeIso b (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G).hom.hom.hom := by
  apply (baseChangeCoeffEquiv k K G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, baseChangeCoeffEquiv_left, Over.comp_left,
    Category.assoc, descentBaseChangeIso_hom_fst]
  change (rationalConjugate k K G σ n).left ≫ pullback.fst G.X.hom b =
    (baseChangeBasePoint (galoisBaseMap k K σ) G_K n).left ≫
      (pullback.fst (G_K).X.hom (galoisBaseMap k K σ) ≫ pullback.fst G.X.hom b)
  rw [← Category.assoc, baseChangeBasePoint_fst, Category.assoc]
  have h := congrArg (fun p => p.left) (baseChangeCoeffEquiv_rationalConjugate k K G σ n)
  rw [baseChangeCoeffEquiv_left] at h
  change (rationalConjugate k K G σ n).left ≫ pullback.fst G.X.hom b =
    galoisBaseMap k K σ ≫ (baseChangeCoeffEquiv k K G n).left at h
  rw [baseChangeCoeffEquiv_left] at h
  exact h

/-- Canonical coefficient transport of an actual automorphism of the upstairs
commutative group scheme. -/
def torusAutGaloisTransport (σ : K ≃ₐ[k] K) (τ : T_K ≅ T_K) : T_K ≅ T_K :=
  (CommGroupScheme.descentBaseChangeIso b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) T).symm ≪≫
  (CommGroupScheme.baseChange (galoisBaseMap k K σ)).mapIso τ ≪≫
  CommGroupScheme.descentBaseChangeIso b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) T

variable (i : T.toGrp ⟶ G)

/-- The actual coefficient conjugate normalizes through the explicitly
transported original torus automorphism. -/
theorem IsNormalizingPoint.rationalConjugate (σ : K ≃ₐ[k] K)
    {n : rationalPoints G_K} {τ : T_K ≅ T_K}
    (hn : IsNormalizingPoint (T := T_K) (i_K i) n τ) :
    IsNormalizingPoint (T := T_K) (i_K i) (rationalConjugate k K G σ n)
      (torusAutGaloisTransport k K σ τ) := by
  exact hn.baseChange_descent_of_eq b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) i
    (rationalConjugate_eq_baseChange_descent (G := G) k K σ n)

/-- Coefficient conjugation preserves the existing rational normalizer subgroup. -/
theorem rationalConjugate_mem_normalizerPoints (σ : K ≃ₐ[k] K)
    {n : rationalPoints G_K} (hn : n ∈ normalizerPoints (T := T_K) (i_K i)) :
    rationalConjugate k K G σ n ∈ normalizerPoints (T := T_K) (i_K i) := by
  obtain ⟨τ, hτ⟩ := hn
  exact ⟨_, hτ.rationalConjugate k K i σ⟩

/-- The existing coefficient action restricts to actual normalizer points,
including its inverse and multiplication laws. -/
def normalizerGaloisAction :
    (K ≃ₐ[k] K) →* MulAut (normalizerPoints (T := T_K) (i_K i)) where
  toFun σ :=
    { toFun n := ⟨rationalConjugate k K G σ n.val,
        rationalConjugate_mem_normalizerPoints k K i σ n.property⟩
      invFun n := ⟨rationalConjugate k K G σ⁻¹ n.val,
        rationalConjugate_mem_normalizerPoints k K i σ⁻¹ n.property⟩
      left_inv n := by
        apply Subtype.ext
        change rationalConjugate k K G σ⁻¹ (rationalConjugate k K G σ n.val) = n.val
        rw [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one]
      right_inv n := by
        apply Subtype.ext
        change rationalConjugate k K G σ (rationalConjugate k K G σ⁻¹ n.val) = n.val
        rw [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]
      map_mul' n m := by
        apply Subtype.ext
        exact (rationalConjugate k K G σ).map_mul n.val m.val }
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    exact rationalConjugate_one k K G n.val
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    exact rationalConjugate_mul k K G σ τ n.val

@[simp] theorem normalizerGaloisAction_coe (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) (i_K i)) :
    (normalizerGaloisAction k K i σ n).val = rationalConjugate k K G σ n.val := rfl

variable [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

/-- The full actual Weyl character action is covariant under the restricted
coefficient action. -/
theorem weylAction_normalizerGaloisAction (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) (i_K i)) (χ : characterLattice T_K) :
    weylAction (T := T_K) (i_K i) (normalizerGaloisAction k K i σ n)
        (characterLattice.galoisRepresentation k K T σ χ) =
      characterLattice.galoisRepresentation k K T σ
        (weylAction (T := T_K) (i_K i) n χ) := by
  have h := (isNormalizingPoint_normalizingAut (T := T_K) (i_K i) n).rationalConjugate k K i σ
  have hAut := (isNormalizingPoint_normalizingAut (T := T_K) (i_K i)
    (normalizerGaloisAction k K i σ n)).unique (T := T_K) (i_K i) h
  change characterAut (normalizingAut (T := T_K) (i_K i)
    (normalizerGaloisAction k K i σ n)) (characterLattice.galoisRepresentation k K T σ χ) = _
  rw [hAut]
  exact characterAut_descentTransport b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) (normalizingAut (T := T_K) (i_K i) n) χ

end Langlands.GroupScheme
