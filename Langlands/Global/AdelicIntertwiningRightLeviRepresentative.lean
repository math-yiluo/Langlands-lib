import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Reductive.DominantMultipleCoefficients

/-! # Changing the intertwining representative by a right Levi point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P U M Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {q : Q ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {l' : M' ⟶ Q}

private theorem map_mem_normalizer_unipotentImage
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (y : AdelicGroupPoints F P) :
    map F P G p y ∈ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G)) := by
  let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  let H := (map F U P iU).toMonoidHom.range
  let : H.Normal := by
    refine ⟨fun u hu z => ?_⟩
    exact hU.1.isNormal T z u (Subgroup.mem_top _) hu
  have himage : H.map (map F P G p).toMonoidHom = parabolicUnipotentImage F p iU := by
    unfold H parabolicUnipotentImage
    rw [MonoidHom.map_range]
    congr 1
  rw [← himage]
  apply Subgroup.le_normalizer_map (map F P G p).toMonoidHom
  refine ⟨y, ?_, rfl⟩
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top y

private theorem intertwiningRationalSubgroup_mul_of_normalizer (j : V ⟶ G)
    (w t : AdelicGroupPoints F G)
    (ht : t ∈ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G))) :
    intertwiningRationalSubgroup F p iU j (w * t) = intertwiningRationalSubgroup F p iU j w := by
  ext v
  rw [mem_intertwiningRationalSubgroup_iff, mem_intertwiningRationalSubgroup_iff]
  apply and_congr_right
  intro _
  have h : (w * t)⁻¹ * (v : AdelicGroupPoints F G) * (w * t) =
      t⁻¹ * (w⁻¹ * (v : AdelicGroupPoints F G) * w) * t := by group
  rw [h]
  simpa only [inv_inv] using
    ((Subgroup.mem_normalizer_iff.mp (inv_mem ht)) (w⁻¹ * (v : AdelicGroupPoints F G) * w)).symm

section Integral

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsAffine V.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- Right multiplication of the representative by a rational point of the
source parabolic preserves the rational quotient and the intertwining integral. -/
theorem IsIwasawaCompact.intertwiningIntegral_mul_rational_parabolic
    (hK : IsIwasawaCompact p K) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ P.X)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU j (w * (z ≫ p.hom.hom)) φ lam g =
      hK.intertwiningIntegral iU j w φ lam g := by
  let zF : RationalGroupPoints F P :=
    P.constantPoint z ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))
  let t := map F P G p (rational F P zF)
  let wA := innerAdelicPoint F G w
  let w' := w * (z ≫ p.hom.hom)
  have htp : innerAdelicPoint F G (z ≫ p.hom.hom) = t := by
    rw [innerAdelicPoint_eq_rational, ← constantPoint_comp p z]
    exact DFunLike.congr_fun (rational_naturality F P p) zF
  have hw' : innerAdelicPoint F G w' = wA * t := by
    change G.constantPoint (w * (z ≫ p.hom.hom)) _ = _
    rw [constantPoint_mul]
    exact congrArg (wA * ·) htp
  have hsub : intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w') =
      intertwiningRationalSubgroup F p iU j wA := by
    rw [hw']
    exact intertwiningRationalSubgroup_mul_of_normalizer j wA t
      (map_mem_normalizer_unipotentImage hU (rational F P zF))
  let H := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  let : IsClosed (H : Set (AdelicGroupPoints F G)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let d (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H)) (f : H → ℂ) :=
    ∫ x, f (Quotient.out x) ∂LeftCosetSpace.discreteQuotientMeasure Γ hΓ
      (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j))
  let f (s : AdelicGroupPoints F G) (v : H) :=
    hK.parameterTwist φ lam (s⁻¹ * (v : AdelicGroupPoints F G) * g)
  have hf : f (innerAdelicPoint F G w') = f wA := by
    funext v
    change hK.parameterTwist φ lam ((innerAdelicPoint F G w')⁻¹ * (v : AdelicGroupPoints F G) * g) =
      hK.parameterTwist φ lam (wA⁻¹ * (v : AdelicGroupPoints F G) * g)
    rw [hw']
    simpa only [mul_inv_rev, mul_assoc, map_inv] using hK.parameterTwist_map_rational_mul
      hφ hl hU lam zF⁻¹ (wA⁻¹ * (v : AdelicGroupPoints F G) * g)
  have hΓ (Γ₁ Γ₂ : Subgroup H) (h₁ : IsDiscrete (Γ₁ : Set H)) (h₂ : IsDiscrete (Γ₂ : Set H))
      (heq : Γ₁ = Γ₂) : d Γ₁ h₁ (f wA) = d Γ₂ h₂ (f wA) := by
    subst Γ₂
    rfl
  change d _ _ (f (innerAdelicPoint F G w')) = d _ _ (f wA)
  rw [hf]
  exact hΓ _ _ _ _ hsub

end Integral

omit [NumberField F] in
/-- A rational source Levi point changes the inverse conjugation by its
inner automorphism. -/
theorem IsWeylConjugation.mul_right_levi
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : IsWeylConjugation p l q l' w c)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X) :
    IsWeylConjugation p l q l' (w * (z ≫ (l ≫ p).hom.hom)) (c ≫ (M.innerIso z).inv) := by
  have hz : IsWeylConjugation p l p l (z ≫ (l ≫ p).hom.hom) (M.innerIso z).inv :=
    ⟨inferInstance, by
      simpa only [innerIso_inv_hom, GrpObj.inv_comp, Category.assoc] using
        innerIso_hom_comp (l ≫ p) z⁻¹⟩
  exact hz.comp hw

omit [NumberField F] in
/-- The change of inverse conjugation by an inner automorphism of the source
Levi acts trivially on the transported character parameter. -/
theorem weylParameter_comp_innerIso_inv (c : M' ⟶ M) (π' : Q ⟶ M')
    (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X) :
    weylParameter (F := F) l (c ≫ (M.innerIso z).inv) π' = weylParameter l c π' := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ
  have hχ : characterRestrict (M.innerIso z).inv (characterRestrict l χ) = characterRestrict l χ := by
    apply Additive.toMul.injective
    rw [characterRestrict_apply, ← innerIso_inv_hom]
    exact DominantMultiple.innerIso_hom_comp_character z⁻¹ (characterRestrict l χ)
  simp only [weylParameter_tmul, characterRestrict_comp, AddMonoidHom.comp_apply, hχ]

end AdelicGroupPoints

open AdelicGroupPoints

/-- A change of Weyl representative by a right rational Levi point preserves
the Weyl condition, the parameter map, and the actual normalized operator. -/
def IntertwiningRightLeviRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left] (l' : M' ⟶ Q)
    (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X),
    IsWeylConjugation p l q l' w c → IsRationalLeviSubgroup l → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hQ : IsIwasawaCompact q K) (φ : AdelicGroupPoints F G → ℂ),
      IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ →
      IsWeylConjugation p l q l' (w * (z ≫ (l ≫ p).hom.hom)) (c ≫ (M.innerIso z).inv) ∧
      weylParameter (F := F) l (c ≫ (M.innerIso z).inv) π' = weylParameter l c π' ∧
      ∀ lam g,
        hK.intertwiningOperator hQ iU l iV (c ≫ (M.innerIso z).inv) π' (w * (z ≫ (l ≫ p).hom.hom))
          φ lam g = hK.intertwiningOperator hQ iU l iV c π' w φ lam g

theorem intertwiningRightLeviRepresentative : IntertwiningRightLeviRepresentativeStatement.{u} := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ p _ iU l q _ iV _ l' π' w c z hw hl hU K hK hQ φ hφ
  have heq := weylParameter_comp_innerIso_inv (F := F) (l := l) c π' z
  refine ⟨hw.mul_right_levi z, heq, fun lam g => ?_⟩
  unfold IsIwasawaCompact.intertwiningOperator
  rw [heq]
  congr 1
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    hK.intertwiningIntegral_mul_rational_parabolic (iV ≫ q) w (z ≫ l.hom.hom) hl hU hφ lam g

end Langlands.Global
