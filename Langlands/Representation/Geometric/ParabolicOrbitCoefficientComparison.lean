import Langlands.Representation.Geometric.ParabolicOrbitComparisonData
import Langlands.Representation.Geometric.IntersectionTransport
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Jacquet.CharacterTwistEquiv
import Langlands.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Group.GL.OppositeBlocks

/-! Actual coefficient quotients for a parabolic orbit. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The radical intersection viewed inside the inducing stabilizer. -/
abbrev parabolicOrbitCoefficientRadical :
    Subgroup (parabolicOrbitStabilizer F B C w) :=
  (C.unipotentRadical F).comap (parabolicOrbitStabilizer F B C w).subtype

/-- Switching the order of the two subgroup inclusions preserves the actual
radical intersection element. -/
def parabolicOrbitCoefficientRadicalEquiv :
    parabolicOrbitCoefficientRadical F B C w ≃*
      parabolicOrbitRadicalIntersection F B C w where
  toFun j := ⟨⟨j.val.val, j.property⟩, j.val.property⟩
  invFun j := ⟨⟨j.val.val, j.property⟩, j.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The image of the actual stabilizer radical is exactly the source radical
intersection, rather than merely a subgroup of it. -/
theorem parabolicOrbitCoefficientRadical_map :
    (parabolicOrbitCoefficientRadical F B C w).map
      (parabolicOrbitToSourceLevi F B C w) = sourceUnipotent F B C w := by
  ext m
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact parabolicOrbitRadicalToSource_mem F B C w
      (parabolicOrbitCoefficientRadicalEquiv F B C w ⟨h, hh⟩)
  · intro hm
    obtain ⟨j, hj⟩ := parabolicOrbitRadicalToSource_surjective F B C w ⟨m, hm⟩
    let d := (parabolicOrbitCoefficientRadicalEquiv F B C w).symm j
    exact ⟨d.val, d.property, congrArg Subtype.val hj⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual conjugated inducing coefficient, including its source twist. -/
abbrev parabolicOrbitCoefficient (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (parabolicOrbitStabilizer F B C w) V :=
  (twist χ ρ).comp (parabolicOrbitToSourceLevi F B C w)

private def coefficientSubgroupCongr (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') :
    Jacquet.Coinvariants ρ U ≃ₗ[ℂ] Jacquet.Coinvariants ρ U' := by
  subst U'
  exact LinearEquiv.refl ℂ _

@[simp]
private theorem coefficientSubgroupCongr_mk (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') (v : V) :
    coefficientSubgroupCongr F B ρ h (Jacquet.mk ρ U v) =
      Jacquet.mk ρ U' v := by
  subst U'
  rfl

/-- The identity on coefficient representatives identifies the actual orbit
coefficient quotient with source-intersection coinvariants. -/
def parabolicOrbitCoefficientEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) :
    Jacquet.Coinvariants (parabolicOrbitCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficientRadical F B C w) ≃ₗ[ℂ]
      Jacquet.Coinvariants ρ (sourceUnipotent F B C w) :=
  (Jacquet.coinvariantsMapEquiv (twist χ ρ)
    (parabolicOrbitToSourceLevi F B C w)
    (parabolicOrbitCoefficientRadical F B C w)).trans
    ((coefficientSubgroupCongr F B (twist χ ρ)
      (parabolicOrbitCoefficientRadical_map F B C w)).trans
      (Jacquet.twistCoinvariantsLinearEquiv χ ρ (sourceUnipotent F B C w) hχ))

@[simp]
theorem parabolicOrbitCoefficientEquiv_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    parabolicOrbitCoefficientEquiv F B C w χ ρ hχ
        (Jacquet.mk (parabolicOrbitCoefficient F B C w χ ρ)
          (parabolicOrbitCoefficientRadical F B C w) v) =
      Jacquet.mk ρ (sourceUnipotent F B C w) v := by
  simp only [parabolicOrbitCoefficientEquiv, LinearEquiv.trans_apply,
    Jacquet.coinvariantsMapEquiv_mk, coefficientSubgroupCongr_mk,
    Jacquet.twistCoinvariantsLinearEquiv_mk]

@[simp]
theorem parabolicOrbitCoefficientEquiv_symm_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ).symm
        (Jacquet.mk ρ (sourceUnipotent F B C w) v) =
      Jacquet.mk (parabolicOrbitCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficientRadical F B C w) v := by
  apply (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitCoefficientEquiv_mk]

/-- Coefficient intertwiners retain their original linear maps. -/
def parabolicOrbitCoefficientMap (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) :
    (parabolicOrbitCoefficient F B C w χ ρ).IntertwiningMap
      (parabolicOrbitCoefficient F B C w χ τ) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := (twistIntertwining χ f).isIntertwining'
    (parabolicOrbitToSourceLevi F B C w h)

/-- The quotient identification is natural for every coefficient intertwiner. -/
theorem parabolicOrbitCoefficientEquiv_natural (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (f : ρ.IntertwiningMap τ)
    (z : Jacquet.Coinvariants (parabolicOrbitCoefficient F B C w χ ρ)
      (parabolicOrbitCoefficientRadical F B C w)) :
    parabolicOrbitCoefficientEquiv F B C w χ τ hχ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (parabolicOrbitCoefficientMap F B C w χ f)
            (parabolicOrbitCoefficientRadical F B C w)) z) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap f (sourceUnipotent F B C w))
        (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change parabolicOrbitCoefficientEquiv F B C w χ τ hχ
      (Jacquet.mk _ _ (f v)) = _
    rw [parabolicOrbitCoefficientEquiv_mk, parabolicOrbitCoefficientEquiv_mk]
    rfl

/-- The source intersection Levi normalizes the actual source intersection radical. -/
theorem sourceLevi_le_normalizer_sourceUnipotent :
    sourceLevi F B C w ≤ Subgroup.normalizer (sourceUnipotent F B C w) := by
  intro m hm
  exact Subgroup.le_normalizer_comap (conjugatedLeviMap F B w)
    (C.leviSubgroup_le_normalizer_unipotentSubgroup F hm)

/-- The target intersection Levi section, valued in the actual orbit stabilizer. -/
def parabolicOrbitIntersectionSection :
    sourceLevi F C B w⁻¹ →* parabolicOrbitStabilizer F B C w :=
  (C.leviInParabolic F).comp (sourceLevi F C B w⁻¹).subtype |>.codRestrict _
    (fun m => by
      change (permutation n F w)⁻¹ * C.leviEmbedding F m.val *
        ((permutation n F w)⁻¹)⁻¹ ∈ B.parabolic F
      have hm : conjugatedLeviMap F C w⁻¹ m.val ∈ B.leviSubgroup F := m.property
      have hp := (B.leviAsParabolic F ⟨_, hm⟩).property
      change conjugatedLeviMap F C w⁻¹ m.val ∈ B.parabolic F at hp
      simpa only [conjugatedLeviMap, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply,
        map_inv, inv_inv] using hp)

/-- The source coordinate of the target section is exactly inverse conjugation. -/
theorem parabolicOrbitToSourceLevi_intersectionSection
    (m : sourceLevi F C B w⁻¹) :
    parabolicOrbitToSourceLevi F B C w
        (parabolicOrbitIntersectionSection F B C w m) =
      ((intersectionLeviConjugation F B C w).symm m).val := by
  have h : stabilizerToInducing (B.parabolic F) (C.parabolic F)
      (permutation n F w) (parabolicOrbitIntersectionSection F B C w m) =
      B.leviInParabolic F ((intersectionLeviConjugation F B C w).symm m).val := by
    apply Subtype.ext
    exact (intersectionLeviConjugation_symm_embedding F B C w m).symm
  change B.leviProjection F _ = _
  rw [h, B.leviProjection_section]

/-- The quotient action retained from the stabilizer on the target intersection Levi. -/
abbrev parabolicOrbitCoefficientAction (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (sourceLevi F C B w⁻¹)
      (Jacquet.Coinvariants (parabolicOrbitCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficientRadical F B C w)) :=
  ((parabolicOrbitCoefficient F B C w χ ρ).toCoinvariants
    (parabolicOrbitCoefficientRadical F B C w)).comp
      (parabolicOrbitIntersectionSection F B C w)

/-- The coefficient quotient intertwines the actual section action with the
inverse-conjugated source Jacquet action and the source character. -/
def parabolicOrbitCoefficientActionEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) :
    (parabolicOrbitCoefficientAction F B C w χ ρ).Equiv
      (intersectionTransport F B C w
        (twist (χ.comp (sourceLevi F B C w).subtype)
          (Jacquet.action ρ (sourceUnipotent F B C w)
            (sourceLevi F B C w) (sourceLevi_le_normalizer_sourceUnipotent F B C w)))) where
  toLinearEquiv := parabolicOrbitCoefficientEquiv F B C w χ ρ hχ
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change parabolicOrbitCoefficientEquiv F B C w χ ρ hχ
        (Jacquet.mk _ _ ((twist χ ρ)
          (parabolicOrbitToSourceLevi F B C w
            (parabolicOrbitIntersectionSection F B C w m)) v)) =
      intersectionTransport F B C w
        (twist (χ.comp (sourceLevi F B C w).subtype)
          (Jacquet.action ρ (sourceUnipotent F B C w)
            (sourceLevi F B C w) (sourceLevi_le_normalizer_sourceUnipotent F B C w)))
        m (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ (Jacquet.mk _ _ v))
    rw [parabolicOrbitCoefficientEquiv_mk,
      parabolicOrbitCoefficientEquiv_mk, parabolicOrbitToSourceLevi_intersectionSection]
    change Jacquet.mk ρ (sourceUnipotent F B C w)
        ((χ ((intersectionLeviConjugation F B C w).symm m).val : ℂ) •
          ρ ((intersectionLeviConjugation F B C w).symm m).val v) =
      (χ ((intersectionLeviConjugation F B C w).symm m).val : ℂ) •
        Jacquet.mk ρ (sourceUnipotent F B C w)
          (ρ ((intersectionLeviConjugation F B C w).symm m).val v)
    exact map_smul (Jacquet.mk ρ (sourceUnipotent F B C w)) _ _

@[simp]
theorem parabolicOrbitCoefficientActionEquiv_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    parabolicOrbitCoefficientActionEquiv F B C w χ ρ hχ
        (Jacquet.mk _ (parabolicOrbitCoefficientRadical F B C w) v) =
      Jacquet.mk ρ (sourceUnipotent F B C w) v :=
  parabolicOrbitCoefficientEquiv_mk F B C w χ ρ hχ v

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)

include S hS in
/-- The genuine source induction character is trivial on the actual source
radical intersection, using the supplied unipotent refinement equality. -/
theorem sourceUnipotent_le_ker_leviHalfModulus :
    sourceUnipotent F.Carrier B C w ≤ (T.leviHalfModulus B).ker := by
  intro u hu
  have hr : u ∈ refinedUnipotent F.Carrier B S := hS.2.2 ▸ hu
  exact T.leviHalfModulus_refinedUnipotent B S ⟨u, hr⟩

/-- The actual positive-half inducing coefficient has exactly the refined
source Jacquet carrier as its radical quotient. -/
def parabolicOrbitRefinedCoefficientEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Jacquet.Coinvariants
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
        (parabolicOrbitCoefficientRadical F.Carrier B C w) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ := by
  exact (parabolicOrbitCoefficientEquiv F.Carrier B C w (T.leviHalfModulus B) ρ
    (T.sourceUnipotent_le_ker_leviHalfModulus B C w S hS)).trans
      (coefficientSubgroupCongr F.Carrier B ρ hS.2.2)

@[simp]
theorem parabolicOrbitRefinedCoefficientEquiv_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
          (parabolicOrbitCoefficientRadical F.Carrier B C w) v) =
      refinedJacquetMk B S ρ v := by
  simp only [parabolicOrbitRefinedCoefficientEquiv, LinearEquiv.trans_apply,
    parabolicOrbitCoefficientEquiv_mk, coefficientSubgroupCongr_mk]

@[simp]
theorem parabolicOrbitRefinedCoefficientEquiv_symm_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ).symm
        (refinedJacquetMk B S ρ v) =
      Jacquet.mk
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
        (parabolicOrbitCoefficientRadical F.Carrier B C w) v := by
  apply (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitRefinedCoefficientEquiv_mk]

/-- The refined identification commutes with all coefficient intertwiners. -/
theorem parabolicOrbitRefinedCoefficientEquiv_natural
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ)
    (z : Jacquet.Coinvariants
      (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
      (parabolicOrbitCoefficientRadical F.Carrier B C w)) :
    T.parabolicOrbitRefinedCoefficientEquiv B C w S hS τ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap
            (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f)
            (parabolicOrbitCoefficientRadical F.Carrier B C w)) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change T.parabolicOrbitRefinedCoefficientEquiv B C w S hS τ
      (Jacquet.mk _ _ (f v)) = _
    rw [parabolicOrbitRefinedCoefficientEquiv_mk,
      parabolicOrbitRefinedCoefficientEquiv_mk]
    rfl

/-- On every coefficient class the section action has the original source
half modulus and inverse-conjugated source action. -/
theorem parabolicOrbitRefinedCoefficientEquiv_section_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (m : sourceLevi F.Carrier C B w⁻¹) (v : V) :
    T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (parabolicOrbitCoefficientAction F.Carrier B C w (T.leviHalfModulus B) ρ m
          (Jacquet.mk _ (parabolicOrbitCoefficientRadical F.Carrier B C w) v)) =
      (T.leviHalfModulus B
        ((intersectionLeviConjugation F.Carrier B C w).symm m).val : ℂ) •
        refinedJacquetMk B S ρ
          (ρ ((intersectionLeviConjugation F.Carrier B C w).symm m).val v) := by
  change T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
    (Jacquet.mk _ _ ((twist (T.leviHalfModulus B) ρ)
      (parabolicOrbitToSourceLevi F.Carrier B C w
        (parabolicOrbitIntersectionSection F.Carrier B C w m)) v)) = _
  rw [parabolicOrbitRefinedCoefficientEquiv_mk,
    parabolicOrbitToSourceLevi_intersectionSection]
  exact map_smul (refinedJacquetMk B S ρ) _ _

end Langlands.PadicField.TopologicalData
