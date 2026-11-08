import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Geometry.Building.KPApartmentGaloisImage
import Langlands.GroupScheme.Rational.CharacterGaloisAction

/-! # Coefficient transport of full centralizer compatibility -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.IntegerValuation

section Valuation

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {Z : GroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ Z)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "s_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) s

/-- Restriction of actual rational characters to the torus is coefficient-equivariant. -/
theorem characterRestriction_galoisRepresentation (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj Z)) :
    Cartan.characterRestriction (S := T_K) s_K
        (rationalCharacters.galoisRepresentation k K Z σ χ) =
      characterLattice.galoisRepresentation k K T σ
        (Cartan.characterRestriction (S := T_K) s_K χ) := by
  change rationalCharacters.equivCharacterLattice T_K
      (characterRestrict s_K (rationalCharacters.galoisRepresentation k K Z σ χ)) = _
  rw [rationalCharacters.characterRestrict_galoisRepresentation]
  rfl

variable (w : Valuation K (WithZero (Multiplicative ℤ)))

/-- The positive centralizer valuation of a coefficient-transported point is the
transported real cocharacter, when the order is coefficient invariant. -/
theorem centralizerValuation_galois (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (z : rationalPoints (baseChanged k K Z)) :
    (centralizerValuation w (S := T_K) s_K hK (rationalConjugate k K Z σ z)).toAdd =
      galoisCocharacterAction k K T σ
        (centralizerValuation w (S := T_K) s_K hK z).toAdd := by
  apply hK.1
  ext χ
  change eval T_K (Cartan.characterRestriction (S := T_K) s_K χ)
      (centralizerValuation w (S := T_K) s_K hK (rationalConjugate k K Z σ z)).toAdd =
    eval T_K (Cartan.characterRestriction (S := T_K) s_K χ)
      (galoisCocharacterAction k K T σ (centralizerValuation w (S := T_K) s_K hK z).toAdd)
  rw [centralizerValuation_spec, eval_galoisCocharacterAction_right,
    ← characterRestriction_galoisRepresentation, centralizerValuation_spec,
    rationalCharacterEval_rationalConjugate, hw]

/-- The KP centralizer translation is transported in the same way. -/
theorem centralizerTranslation_galois (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (z : rationalPoints (baseChanged k K Z)) :
    (centralizerTranslation w (S := T_K) s_K hK (rationalConjugate k K Z σ z)).toAdd =
      galoisCocharacterAction k K T σ
        (centralizerTranslation w (S := T_K) s_K hK z).toAdd := by
  rw [centralizerTranslation_toAdd, centralizerTranslation_toAdd,
    centralizerValuation_galois k K s w σ hw hK z]
  exact (map_neg (galoisCocharacterAction k K T σ) _).symm

end Valuation

section Transport

variable {L : Type u} [Field L]
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  {H Z : GroupScheme (Spec (CommRingCat.of L))} [IsAffineHom H.X.hom]

/-- Full centralizer compatibility can be pulled back along covariant character,
ambient-point and centralizer-point maps. -/
theorem IsCentralizerCompatible.pullbackTransport
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (i : S.toGrp ⟶ H) (j : Z ⟶ H) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {φ ψ : RootFunctionFamily S H}
    (hφ : IsCentralizerCompatible v i j s h φ)
    (α : characterLattice S → characterLattice S)
    (β : rationalPoints H →* rationalPoints H)
    (centralizerMap : rationalPoints Z → rationalPoints Z)
    (hψ : ∀ a g, ψ a g = φ (α a) (β g))
    (hroots : ∀ a ∈ relativeRoots i, α a ∈ relativeRoots i)
    (hgroups : ∀ a g, g ∈ rootGroupPoints i a → β g ∈ rootGroupPoints i (α a))
    (hmap : ∀ z, β (rationalPoints.map j z) = rationalPoints.map j (centralizerMap z))
    (heval : ∀ a z,
      eval S (α a) (centralizerTranslation v s h (centralizerMap z)).toAdd =
        eval S a (centralizerTranslation v s h z).toAdd) :
    IsCentralizerCompatible v i j s h ψ := by
  intro a ha z u hu
  have hc := hφ (α a) (hroots a ha) (centralizerMap z) (β u) (hgroups a u hu)
  rw [heval] at hc
  simpa only [hψ, map_mul, map_inv, hmap] using hc

end Transport

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (j : Z ⟶ G) (s : T.toGrp ⟶ Z)
  (w : Valuation K (WithZero (Multiplicative ℤ)))

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "s_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) s

variable [IsAffineHom G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The inverse coefficient action preserves full centralizer compatibility when the
order is coefficient invariant. -/
theorem IsCentralizerCompatible.galoisTransport_inv (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    {φ : RootFunctionFamily T_K G_K}
    (hφ : IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK φ) :
    IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK
      (RootFunctionFamily.galoisAction k K T G σ⁻¹ φ) := by
  refine IsCentralizerCompatible.pullbackTransport (S := T_K) (H := G_K)
    (φ := φ) (ψ := RootFunctionFamily.galoisAction k K T G σ⁻¹ φ)
    w i_K j_K s_K hK hφ (characterLattice.galoisRepresentation k K T σ)
    (rationalConjugate k K G σ).toMonoidHom
    (rationalConjugate k K Z σ)
    (RootFunctionFamily.galoisAction_inv_apply k K σ φ)
    (fun a ha => (mem_roots_galois_iff k K i σ a).2 ha)
    (fun a u hu =>
      (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a u).2 hu)
    (rationalConjugate_map k K j σ) ?_
  intro a z
  rw [centralizerTranslation_galois k K s w σ hw hK z, eval_galoisCocharacterAction]

/-- The original coefficient action preserves full centralizer compatibility. -/
theorem IsCentralizerCompatible.galoisTransport (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    {φ : RootFunctionFamily T_K G_K}
    (hφ : IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK φ) :
    IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK
      (RootFunctionFamily.galoisAction k K T G σ φ) := by
  have hwinv (t : Kˣ) : order w (Units.map σ⁻¹.toMonoidHom t) = order w t :=
    invariant_apply_of_inverse
      (Units.map σ.toMonoidHom) (Units.map σ⁻¹.toMonoidHom) (order w)
      (units_map_algEquiv_inv σ) hw rfl
  simpa only [inv_inv] using
    IsCentralizerCompatible.galoisTransport_inv k K i j s w σ⁻¹ hwinv hK hφ

/-- The coefficient permutation restricts to exactly all fully centralizer-compatible
families for a coefficient-invariant order. -/
def IsCentralizerCompatible.galoisEquiv (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K)) :
    Equiv.Perm {φ : RootFunctionFamily T_K G_K //
      IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK φ} where
  toFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ φ.val,
    IsCentralizerCompatible.galoisTransport k K i j s w σ hw hK φ.property⟩
  invFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ⁻¹ φ.val,
    IsCentralizerCompatible.galoisTransport_inv k K i j s w σ hw hK φ.property⟩
  left_inv φ := by
    apply Subtype.ext
    change (RootFunctionFamily.galoisAction k K T G σ⁻¹ *
      RootFunctionFamily.galoisAction k K T G σ) φ.val = φ.val
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv φ := by
    apply Subtype.ext
    change (RootFunctionFamily.galoisAction k K T G σ *
      RootFunctionFamily.galoisAction k K T G σ⁻¹) φ.val = φ.val
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

@[simp] theorem IsCentralizerCompatible.galoisEquiv_val (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (φ : {φ : RootFunctionFamily T_K G_K //
      IsCentralizerCompatible w (S := T_K) i_K j_K s_K hK φ}) :
    (IsCentralizerCompatible.galoisEquiv k K i j s w σ hw hK φ).val =
      RootFunctionFamily.galoisAction k K T G σ φ.val := rfl

/-- The actual coefficient image of a supplied class that is fully compatible with the
base-changed centralizer datum is fully compatible with the same datum. -/
theorem IsOmegaCompatible.galoisImage
    [Mono (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
    (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (D : KPApartmentData (S := T_K) i_K (order w))
    (hcl : IsClosedSubgroup j_K)
    (hrep : (torusCentralizer (T := T_K) i_K).IsRepresentedBy j_K)
    (hcomp : s_K ≫ j_K = i_K)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (hD : IsOmegaCompatible w D ⟨(GroupScheme.baseChange b).obj Z, j_K, s_K, hcl, hrep,
      hcomp, hK⟩) :
    IsOmegaCompatible w (KPApartmentData.galoisImage k K i D σ hw)
      ⟨(GroupScheme.baseChange b).obj Z, j_K, s_K, hcl, hrep, hcomp, hK⟩ := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact IsCentralizerCompatible.galoisTransport k K i j s w σ hw hK (hD φ hφ)

end Galois

end Langlands.Geometry.Building.IntegerValuation
