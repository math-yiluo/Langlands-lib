import Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient

/-! The full intermediate section factors through the target refined Levi. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (R : BlockRefinement C)
  (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)

/-- The actual intermediate quotient is the supplied target refined parabolic. -/
def parabolicOrbitStagesRefinedEquiv :
    parabolicOrbitStagesQuotient F B C w ≃* refinedParabolic F C R :=
  MulEquiv.subgroupCongr ((parabolicOrbitStages_comap_section F B C w).trans hR.1)

@[simp] theorem parabolicOrbitStagesRefinedEquiv_val
    (l : parabolicOrbitStagesQuotient F B C w) :
    (parabolicOrbitStagesRefinedEquiv F B C w R hR l).val = l.val := rfl

@[simp] theorem parabolicOrbitStagesRefinedEquiv_symm_val
    (q : refinedParabolic F C R) :
    ((parabolicOrbitStagesRefinedEquiv F B C w R hR).symm q).val = q.val := rfl

/-- The intermediate target section with its supplied refined-parabolic domain. -/
def parabolicOrbitRefinedSection :
    refinedParabolic F C R →* parabolicOrbitStabilizer F B C w :=
  (parabolicOrbitStagesSection F B C w).comp
    (parabolicOrbitStagesRefinedEquiv F B C w R hR).symm.toMonoidHom

/-- The source coordinate of the full target refined section. -/
def parabolicOrbitRefinedSourceCoordinate :
    refinedParabolic F C R →* B.Levi F :=
  (parabolicOrbitToSourceLevi F B C w).comp
    (parabolicOrbitRefinedSection F B C w R hR)

/-- The refined radical conjugates into the source radical, so its coordinate is one. -/
theorem parabolicOrbitRefinedSourceCoordinate_unipotent
    (u : refinedUnipotentRadical F C R) :
    parabolicOrbitRefinedSourceCoordinate F B C w R hR u.val = 1 := by
  have hu : u.val.val ∈ sourceUnipotent F C B w⁻¹ :=
    hR.2.2.symm ▸ (mem_refinedUnipotentRadical F C R u.val).mp u.property
  have hc : conjugatedLeviMap F C w⁻¹ u.val.val ∈ B.unipotentSubgroup F := hu
  obtain ⟨b, hb, he⟩ := hc
  have hs : stabilizerToInducing (B.parabolic F) (C.parabolic F)
      (permutation n F w) (parabolicOrbitRefinedSection F B C w R hR u.val) = b := by
    apply Subtype.ext
    change (permutation n F w)⁻¹ * C.leviEmbedding F u.val.val *
      ((permutation n F w)⁻¹)⁻¹ = b.val
    calc
      _ = conjugatedLeviMap F C w⁻¹ u.val.val := by
        simp only [conjugatedLeviMap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply,
          map_inv, inv_inv]
      _ = b.val := he.symm
  change B.leviProjection F _ = 1
  rw [hs]
  exact hb

/-- On the refined Levi the section is the actual intersection-Levi section. -/
theorem parabolicOrbitRefinedSection_levi (m : refinedLevi F C R) :
    parabolicOrbitRefinedSection F B C w R hR (refinedLeviSection F C R m) =
      parabolicOrbitIntersectionSection F B C w
        (MulEquiv.subgroupCongr hR.2.1.symm m) := rfl

/-- On the refined Levi the source coordinate is inverse intersection conjugation. -/
theorem parabolicOrbitRefinedSourceCoordinate_levi (m : refinedLevi F C R) :
    parabolicOrbitRefinedSourceCoordinate F B C w R hR
        (refinedLeviSection F C R m) =
      ((intersectionLeviConjugation F B C w).symm
        (MulEquiv.subgroupCongr hR.2.1.symm m)).val := by
  change parabolicOrbitToSourceLevi F B C w
    (parabolicOrbitRefinedSection F B C w R hR (refinedLeviSection F C R m)) = _
  rw [parabolicOrbitRefinedSection_levi]
  exact parabolicOrbitToSourceLevi_intersectionSection F B C w _

/-- The full source coordinate factors through the actual target refined projection. -/
theorem parabolicOrbitRefinedSourceCoordinate_factor (q : refinedParabolic F C R) :
    parabolicOrbitRefinedSourceCoordinate F B C w R hR q =
      ((intersectionLeviConjugation F B C w).symm
        (MulEquiv.subgroupCongr hR.2.1.symm
          (refinedLeviProjection F C R q))).val := by
  have he := (refinedDecomposition F C R).symm_apply_apply q
  change (refinedUnipotentPart F C R q).val *
    refinedLeviSection F C R (refinedLeviProjection F C R q) = q at he
  rw [← he, map_mul, parabolicOrbitRefinedSourceCoordinate_unipotent,
    one_mul, parabolicOrbitRefinedSourceCoordinate_levi]
  rw [he]

/-- The actual target refined projection, valued in the target intersection Levi. -/
def parabolicOrbitTargetLeviProjection :
    parabolicOrbitStagesQuotient F B C w →* sourceLevi F C B w⁻¹ :=
  (MulEquiv.subgroupCongr hR.2.1.symm).toMonoidHom.comp
    ((refinedLeviProjection F C R).comp
      (parabolicOrbitStagesRefinedEquiv F B C w R hR).toMonoidHom)

/-- The full source coordinate with its proved source intersection-Levi codomain. -/
def parabolicOrbitSourceLeviCoordinate :
    parabolicOrbitStagesQuotient F B C w →* sourceLevi F B C w :=
  (intersectionLeviConjugation F B C w).symm.toMonoidHom.comp
    (parabolicOrbitTargetLeviProjection F B C w R hR)

/-- On the original full intermediate subgroup, this is the original section coordinate. -/
theorem parabolicOrbitToSourceLevi_stagesSection
    (l : parabolicOrbitStagesQuotient F B C w) :
    parabolicOrbitToSourceLevi F B C w (parabolicOrbitStagesSection F B C w l) =
      (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val :=
  parabolicOrbitRefinedSourceCoordinate_factor F B C w R hR
    (parabolicOrbitStagesRefinedEquiv F B C w R hR l)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual stabilizer-coinvariant action restricted along the full stages section. -/
abbrev parabolicOrbitFullCoefficientAction (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (parabolicOrbitStagesQuotient F B C w)
      (Jacquet.Coinvariants (parabolicOrbitCoefficient F B C w χ ρ)
        (parabolicOrbitCoefficientRadical F B C w)) :=
  ((parabolicOrbitCoefficient F B C w χ ρ).toCoinvariants
    (parabolicOrbitCoefficientRadical F B C w)).comp
      (parabolicOrbitStagesSection F B C w)

/-- The full quotient action is the projected, inverse-conjugated source action. -/
def parabolicOrbitFullCoefficientActionEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) :
    (parabolicOrbitFullCoefficientAction F B C w χ ρ).Equiv
      ((intersectionTransport F B C w
        (twist (χ.comp (sourceLevi F B C w).subtype)
          (Jacquet.action ρ (sourceUnipotent F B C w)
            (sourceLevi F B C w) (sourceLevi_le_normalizer_sourceUnipotent F B C w)))).comp
        (parabolicOrbitTargetLeviProjection F B C w R hR)) where
  toLinearEquiv := parabolicOrbitCoefficientEquiv F B C w χ ρ hχ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change parabolicOrbitCoefficientEquiv F B C w χ ρ hχ
        (Jacquet.mk _ _ ((twist χ ρ)
          (parabolicOrbitToSourceLevi F B C w
            (parabolicOrbitStagesSection F B C w l)) v)) =
      (χ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val : ℂ) •
        Jacquet.action ρ (sourceUnipotent F B C w) (sourceLevi F B C w)
          (sourceLevi_le_normalizer_sourceUnipotent F B C w)
          (parabolicOrbitSourceLeviCoordinate F B C w R hR l)
          (parabolicOrbitCoefficientEquiv F B C w χ ρ hχ (Jacquet.mk _ _ v))
    rw [parabolicOrbitCoefficientEquiv_mk, parabolicOrbitCoefficientEquiv_mk,
      parabolicOrbitToSourceLevi_stagesSection F B C w R hR]
    change Jacquet.mk ρ (sourceUnipotent F B C w)
        ((χ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val : ℂ) •
          ρ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val v) =
      (χ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val : ℂ) •
        Jacquet.mk ρ (sourceUnipotent F B C w)
          (ρ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val v)
    exact map_smul (Jacquet.mk ρ (sourceUnipotent F B C w)) _ _

/-- The full action equivalence retains every coefficient representative. -/
@[simp] theorem parabolicOrbitFullCoefficientActionEquiv_mk (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (v : V) :
    parabolicOrbitFullCoefficientActionEquiv F B C w R hR χ ρ hχ
        (Jacquet.mk _ (parabolicOrbitCoefficientRadical F B C w) v) =
      Jacquet.mk ρ (sourceUnipotent F B C w) v :=
  parabolicOrbitCoefficientEquiv_mk F B C w χ ρ hχ v

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The full action equivalence is natural for every original coefficient map. -/
theorem parabolicOrbitFullCoefficientActionEquiv_natural (χ : B.Levi F →* ℂˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (hχ : sourceUnipotent F B C w ≤ χ.ker) (f : ρ.IntertwiningMap τ)
    (z : Jacquet.Coinvariants (parabolicOrbitCoefficient F B C w χ ρ)
      (parabolicOrbitCoefficientRadical F B C w)) :
    parabolicOrbitFullCoefficientActionEquiv F B C w R hR χ τ hχ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (parabolicOrbitCoefficientMap F B C w χ f)
            (parabolicOrbitCoefficientRadical F B C w)) z) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap f (sourceUnipotent F B C w))
        (parabolicOrbitFullCoefficientActionEquiv F B C w R hR χ ρ hχ z) :=
  parabolicOrbitCoefficientEquiv_natural F B C w χ hχ f z

/-- The actual nested quotient has the same full projected section formula. -/
theorem parabolicOrbitNestedCoefficientEquiv_projected_section_mk
    (χ : B.Levi F →* ℂˣ) (ρ : Representation ℂ (B.Levi F) V)
    (hχ : sourceUnipotent F B C w ≤ χ.ker)
    (l : parabolicOrbitStagesQuotient F B C w) (v : V) :
    parabolicOrbitNestedCoefficientEquiv F B C w χ ρ hχ
        (Representation.Coinvariants.mk (parabolicOrbitNestedCoefficient F B C w χ ρ)
          (parabolicOrbitCoefficient F B C w χ ρ (parabolicOrbitStagesSection F B C w l) v)) =
      (χ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val : ℂ) •
        Jacquet.mk ρ (sourceUnipotent F B C w)
          (ρ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val v) := by
  rw [parabolicOrbitNestedCoefficientEquiv_section_mk,
    parabolicOrbitToSourceLevi_stagesSection F B C w R hR]

/-- The source coordinate valued in the supplied actual source refined Levi. -/
def parabolicOrbitSourceRefinedCoordinate (S : BlockRefinement B)
    (hS : IsIntersectionRefinement (F := F) B C w S) :
    parabolicOrbitStagesQuotient F B C w →* refinedLevi F B S :=
  (MulEquiv.subgroupCongr hS.2.1).toMonoidHom.comp
    (parabolicOrbitSourceLeviCoordinate F B C w R hR)

@[simp] theorem parabolicOrbitSourceRefinedCoordinate_val (S : BlockRefinement B)
    (hS : IsIntersectionRefinement (F := F) B C w S)
    (l : parabolicOrbitStagesQuotient F B C w) :
    (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS l).val =
      (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val := rfl

section Topology

variable [TopologicalSpace F]

/-- Relabeling the stages subgroup preserves its actual induced topology. -/
def parabolicOrbitStagesRefinedEquivContinuous :
    parabolicOrbitStagesQuotient F B C w ≃ₜ* refinedParabolic F C R where
  toMulEquiv := parabolicOrbitStagesRefinedEquiv F B C w R hR
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

variable [IsTopologicalRing F]

theorem continuous_parabolicOrbitTargetLeviProjection :
    Continuous (parabolicOrbitTargetLeviProjection F B C w R hR) :=
  ((continuous_subtype_val).subtype_mk _).comp
    ((refinedLeviProjectionContinuous F C R).continuous.comp
      (parabolicOrbitStagesRefinedEquivContinuous F B C w R hR).continuous)

theorem continuous_parabolicOrbitSourceLeviCoordinate :
    Continuous (parabolicOrbitSourceLeviCoordinate F B C w R hR) :=
  (intersectionLeviConjugationContinuous F B C w).symm.continuous.comp
    (continuous_parabolicOrbitTargetLeviProjection F B C w R hR)

theorem continuous_parabolicOrbitSourceRefinedCoordinate (S : BlockRefinement B)
    (hS : IsIntersectionRefinement (F := F) B C w S) :
    Continuous (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS) :=
  ((continuous_subtype_val).subtype_mk _).comp
    (continuous_parabolicOrbitSourceLeviCoordinate F B C w R hR)

end Topology

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The two source positive halves retained before the Haar and target corrections. -/
def parabolicOrbitSectionCharacter :
    parabolicOrbitStagesQuotient F.Carrier B C w →* ℂˣ :=
  (T.leviHalfModulus B).comp
      ((sourceLevi F.Carrier B C w).subtype.comp
        (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR)) *
    (T.refinedLeviHalfModulus B S).comp
      (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS)

private theorem sectionCharacter_normalized_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) (v : V) :
    (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS l)
          (refinedJacquetMk B S ρ v) =
      (T.leviHalfModulus B
        (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR l).val : ℂ) •
        refinedJacquetMk B S ρ
          (ρ (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR l).val v) := by
  rw [T.normalizedRefinedJacquet_mk]
  simp only [parabolicOrbitSectionCharacter, MonoidHom.mul_apply,
    MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_mul,
    refinedLeviInverseHalfModulus_eq_inv, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, smul_smul, mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  rfl

/-- The genuine nested refined quotient has the full normalized section formula. -/
theorem parabolicOrbitNestedRefinedCoefficientEquiv_projected_section_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) (v : V) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ
            (parabolicOrbitStagesSection F.Carrier B C w l) v)) =
      (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS l)
          (refinedJacquetMk B S ρ v) := by
  rw [T.parabolicOrbitNestedRefinedCoefficientEquiv_section_mk,
    parabolicOrbitToSourceLevi_stagesSection F.Carrier B C w R hR]
  exact (sectionCharacter_normalized_mk T B C w S R hS hR ρ l v).symm

/-- The full actual coefficient action identifies with normalized refined Jacquet
action and the two explicit source positive halves. -/
def parabolicOrbitFullRefinedCoefficientActionEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    (parabolicOrbitFullCoefficientAction F.Carrier B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS))) where
  toLinearEquiv := T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk _ _ ((twist (T.leviHalfModulus B) ρ)
          (parabolicOrbitToSourceLevi F.Carrier B C w
            (parabolicOrbitStagesSection F.Carrier B C w l)) v)) =
      (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS l)
          (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ (Jacquet.mk _ _ v))
    rw [T.parabolicOrbitRefinedCoefficientEquiv_mk,
      T.parabolicOrbitRefinedCoefficientEquiv_mk,
      parabolicOrbitToSourceLevi_stagesSection F.Carrier B C w R hR,
      sectionCharacter_normalized_mk]
    exact map_smul (refinedJacquetMk B S ρ) _ _

@[simp] theorem parabolicOrbitFullRefinedCoefficientActionEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ
        (Jacquet.mk _ (parabolicOrbitCoefficientRadical F.Carrier B C w) v) =
      refinedJacquetMk B S ρ v :=
  T.parabolicOrbitRefinedCoefficientEquiv_mk B C w S hS ρ v

/-- The full refined action equivalence commutes with all normalized Jacquet maps. -/
theorem parabolicOrbitFullRefinedCoefficientActionEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ)
    (z : Jacquet.Coinvariants
      (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
      (parabolicOrbitCoefficientRadical F.Carrier B C w)) :
    T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR τ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap
            (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f)
            (parabolicOrbitCoefficientRadical F.Carrier B C w)) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ z) :=
  T.parabolicOrbitRefinedCoefficientEquiv_natural B C w S hS f z

end Langlands.PadicField.TopologicalData
