import Langlands.Representation.Geometric.ProductLeviClosedQuotient
import Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof
import Langlands.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Jacquet.ExactProof

noncomputable section
open CategoryTheory

set_option maxHeartbeats 1200000

namespace Langlands.Geometric
open GeneralLinear Parabolic
universe uF uV
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The forward flattening comparison evaluates at the inner identity. -/
theorem flattenedInductionInStagesIso_inv_eval (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
      (φ : ((SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
        T.normalizedRefinedInductionFunctor B Q ⋙
        T.normalizedParabolicInductionFunctor B).obj A))
      (g : GeneralLinear n F.Carrier),
      Induction.eval _ _
        (SmoothRep.hom ((flattenedInductionInStagesIso T B Q).inv.app A) φ) g =
        Induction.eval _ _ (Induction.eval _ _ φ g) 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A φ g
  let A' := (SmoothRep.pullbackFunctor
    (flattenedLeviEquivContinuous F.Carrier B Q).symm).obj A
  change Induction.eval _ _
    ((composedFlattenedInduction p F T n B Q A' A'.representation).choose
      (SmoothRep.hom
        ((normalizedRefinementInductionTransitivity F T B Q).choose.hom.app A') φ)) g = _
  exact ((composedFlattenedInduction p F T n B Q A' A'.representation).choose_spec.1
    (SmoothRep.hom
      ((normalizedRefinementInductionTransitivity F T B Q).choose.hom.app A') φ) g).trans
    ((normalizedRefinementInductionTransitivity F T B Q).choose_spec.1 A' φ g)

/-- The stages comparison evaluates a flattened induced function at block Levi
matrices, with the prescribed positive-half normalization removed. -/
theorem flattenedInductionInStagesIso_hom_eval (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
      (f : (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A)
      (g : GeneralLinear n F.Carrier) (m : B.Levi F.Carrier),
      Induction.eval _ _
        (Induction.eval _ _
          (SmoothRep.hom ((flattenedInductionInStagesIso T B Q).hom.app A) f) g) m =
        (T.leviHalfModulus B m : ℂ)⁻¹ •
          Induction.eval _ _ f (B.leviEmbedding F.Carrier m * g) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A f g m
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  let E := SmoothRep.equivOfIso ((flattenedInductionInStagesIso T B Q).app A)
  have hv := flattenedInductionInStagesIso_inv_eval T B Q A (E f)
    (B.leviEmbedding F.Carrier m * g)
  change Induction.eval _ _ (E.symm (E f)) _ = _ at hv
  rw [E.symm_apply_apply] at hv
  have hc := congrArg
    (fun v => Induction.eval _ _ v (1 : B.Levi F.Carrier))
    (B.normalizedInducedOf_covariant (T.leviHalfCharacter B)
      (I.obj A).representation (E f) (B.leviInParabolic F.Carrier m) g)
  rw [B.leviProjection_section] at hc
  change Induction.eval _ _ (Induction.eval _ _ (E f)
      (B.leviEmbedding F.Carrier m * g)) 1 =
    (T.leviHalfModulus B m : ℂ) •
      Induction.eval _ _ (Induction.eval _ _ (E f) g) (1 * m) at hc
  rw [one_mul] at hc
  rw [hv, hc]
  exact (inv_smul_smul₀ (Units.ne_zero _) _).symm

/-- The raw restriction underlying the product-Levi quotient, expressed by
identity evaluation after induction in stages. -/
def productLeviRestrictionMap (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier),
      ((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A) →ₗ[ℂ]
        ((SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
          T.normalizedRefinedInductionFunctor B Q).obj A) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro A
  exact {
    toFun := fun f => Induction.eval _ _
      (SmoothRep.hom ((flattenedInductionInStagesIso T B Q).hom.app A) f) 1
    map_add' := by
      intro f g
      rw [map_add]
      rfl
    map_smul' := by
      intro c f
      rw [map_smul]
      rfl }

/-- Raw restriction is onto for every smooth coefficient representation. -/
theorem productLeviRestrictionMap_surjective (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier),
      Function.Surjective (productLeviRestrictionMap T B Q A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A v
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  obtain ⟨φ, hφ⟩ := CuspidalSupport.normalizedParabolicInduced_eval_surjective
    T B (I.obj A).representation (I.obj A).isSmooth v
  let E := SmoothRep.equivOfIso ((flattenedInductionInStagesIso T B Q).app A)
  refine ⟨E.symm φ, ?_⟩
  change Induction.eval _ _ (E (E.symm φ)) 1 = v
  rw [E.apply_symm_apply φ]
  exact hφ

/-- Projection of the flattened upper radical onto the inner upper radical. -/
def flattenedUnipotentProjection (S : BlockRefinement B) :
    (B.flatten S).unipotentSubgroup F.Carrier →* refinedUnipotent F.Carrier B S :=
  (preimageProjection F.Carrier B (refinedUnipotent F.Carrier B S)).comp
    { toFun := fun u => ⟨u.val, (by
        change u.val ∈ composedUnipotent F.Carrier B S
        rw [flattenedUnipotentComparison F.Carrier n B S]
        exact u.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- Every inner radical element lifts to the flattened radical. -/
theorem flattenedUnipotentProjection_surjective (S : BlockRefinement B) :
    Function.Surjective (flattenedUnipotentProjection (F := F) B S) := by
  intro u
  let v := preimageSection F.Carrier B (refinedUnipotent F.Carrier B S) u
  refine ⟨⟨v.val, (by rw [← flattenedUnipotentComparison F.Carrier n B S]; exact v.property)⟩, ?_⟩
  exact preimageProjection_section F.Carrier B (refinedUnipotent F.Carrier B S) u

/-- Restriction intertwines flattened-radical translation with inner-radical
translation; the outer half-modulus is trivial on that radical. -/
theorem productLeviRestrictionMap_unipotent (Q S : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
      (u : (B.flatten S).unipotentSubgroup F.Carrier)
      (f : (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A),
      productLeviRestrictionMap T B Q A
        (((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A).representation u f) =
      ((SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
          T.normalizedRefinedInductionFunctor B Q).obj A).representation
        (flattenedUnipotentProjection (F := F) B S u) (productLeviRestrictionMap T B Q A f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A u f
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  let E := SmoothRep.hom ((flattenedInductionInStagesIso T B Q).hom.app A)
  let u' : composedUnipotent F.Carrier B S :=
    ⟨u.val, (by rw [flattenedUnipotentComparison F.Carrier n B S]; exact u.property)⟩
  let b := preimageInParabolic F.Carrier B (refinedUnipotent F.Carrier B S) u'
  have he := E.isIntertwining
    (((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A).representation)
    (T.normalizedParabolicInduced B (I.obj A).representation) u.val f
  change Induction.eval _ _ (E (_)) 1 = _
  erw [he]
  change Induction.eval _ _ (E f) (1 * u.val) = _
  rw [one_mul]
  have hc := B.normalizedInducedOf_covariant (T.leviHalfCharacter B)
    (I.obj A).representation (E f) b 1
  rw [mul_one] at hc
  change Induction.eval _ _ (E f) u.val = _ at hc
  refine hc.trans ?_
  have hhalf := T.leviHalfModulus_refinedUnipotent B S
    (flattenedUnipotentProjection (F := F) B S u)
  change T.leviHalfModulus B (B.leviProjection F.Carrier b) = 1 at hhalf
  change (T.leviHalfModulus B (B.leviProjection F.Carrier b) : ℂ) • _ = _
  rw [hhalf, Units.val_one, one_smul]
  rfl

/-- The actual quotient sends each flattened Jacquet representative to the
inner Jacquet class of its restriction. -/
theorem productLeviQuotientMap_mk (Q S : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
      (f : (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A),
      ((productLeviQuotientMap T B Q S).app A).hom
        ((B.flatten S).jacquetMk
          ((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A).representation f) =
      refinedJacquetMk B S
        ((SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
          T.normalizedRefinedInductionFunctor B Q).obj A).representation
        (productLeviRestrictionMap T B Q A f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A f
  rfl

/-- Raw restriction vanishes precisely when the flattened induced function
vanishes on the coarse parabolic. -/
theorem productLeviRestrictionMap_eq_zero_iff (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
      (f : (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A),
      productLeviRestrictionMap T B Q A f = 0 ↔
        ∀ b : B.parabolic F.Carrier, Induction.eval _ _ f b = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A f
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  let E := SmoothRep.equivOfIso ((flattenedInductionInStagesIso T B Q).app A)
  constructor
  · intro hr b
    change Induction.eval _ _ (E f) 1 = 0 at hr
    have hc := B.normalizedInducedOf_covariant (T.leviHalfCharacter B)
      (I.obj A).representation (E f) b 1
    erw [mul_one, hr, map_zero, smul_zero] at hc
    have hv := flattenedInductionInStagesIso_inv_eval T B Q A (E f) b.val
    change Induction.eval _ _ (E.symm (E f)) _ = _ at hv
    rw [E.symm_apply_apply] at hv
    exact hv.trans (congrArg (fun v => Induction.eval _ _ v (1 : B.Levi F.Carrier)) hc)
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    funext m
    change Induction.eval _ _ (Induction.eval _ _ (E f) 1) m = 0
    have hv := flattenedInductionInStagesIso_hom_eval T B Q A f 1 m
    erw [mul_one, h (B.leviInParabolic F.Carrier m), smul_zero] at hv
    exact hv

private theorem relations_map_of_surjective
    {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ H W)
    (N : Subgroup G) (M : Subgroup H) (π : N →* M)
    (hπ : Function.Surjective π) (r : V →ₗ[ℂ] W) (hr : Function.Surjective r)
    (hc : ∀ (u : N) (v : V), r (ρ u v) = τ (π u) (r v)) :
    (Jacquet.relations ρ N).map r = Jacquet.relations τ M := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change r (ρ u v - v) ∈ Jacquet.relations τ M
    rw [map_sub, hc]
    exact Jacquet.sub_mem_relations τ M (π u) (r v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hr w
    obtain ⟨z, rfl⟩ := hπ u
    refine ⟨ρ z v - v, Jacquet.sub_mem_relations ρ N z v, ?_⟩
    exact (map_sub r _ _).trans (congrArg (fun x => x - r v) (hc z v))

/-- Restriction maps the full flattened radical relation space onto the inner
radical relation space. -/
theorem productLeviRestrictionMap_relations (Q S : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier),
      (Jacquet.relations
        ((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A).representation
        ((B.flatten S).unipotentSubgroup F.Carrier)).map
          (productLeviRestrictionMap T B Q A) =
      Jacquet.relations
        ((SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
          T.normalizedRefinedInductionFunctor B Q).obj A).representation
        (refinedUnipotent F.Carrier B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  exact relations_map_of_surjective _ _ _ _
    (flattenedUnipotentProjection (F := F) B S)
    (flattenedUnipotentProjection_surjective (F := F) B S)
    (productLeviRestrictionMap T B Q A) (productLeviRestrictionMap_surjective T B Q A)
    (productLeviRestrictionMap_unipotent T B Q S A)

/-- The kernel after Jacquet is exactly the image of the raw restriction
kernel, by lifting target relations to source relations. -/
theorem productLeviQuotientMap_ker (Q S : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier),
      LinearMap.ker ((productLeviQuotientMap T B Q S).app A).hom.toLinearMap =
        (LinearMap.ker (productLeviRestrictionMap T B Q A)).map
          ((B.flatten S).jacquetMk
            ((T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A).representation) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  let X := (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A
  let I := (SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q).obj A
  let r := productLeviRestrictionMap T B Q A
  let q := ((productLeviQuotientMap T B Q S).app A).hom
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := (B.flatten S).jacquetMk_surjective X.representation x
    have hr : r f ∈ Jacquet.relations I.representation (refinedUnipotent F.Carrier B S) := by
      apply (Jacquet.mk_eq_zero _ _ _).mp
      exact (productLeviQuotientMap_mk T B Q S A f).symm.trans hx
    rw [← productLeviRestrictionMap_relations T B Q S A] at hr
    obtain ⟨z, hz, hrz⟩ := hr
    change r z = r f at hrz
    refine ⟨f - z, ?_, ?_⟩
    · change r (f - z) = 0
      rw [map_sub, hrz, sub_self]
    · have hz' : (B.flatten S).jacquetMk X.representation z = 0 := by
        apply (B.flatten S).jacquetModuleEquiv X.representation |>.injective
        change Jacquet.mk X.representation ((B.flatten S).unipotentSubgroup F.Carrier) z = 0
        exact (Jacquet.mk_eq_zero _ _ _).mpr hz
      rw [map_sub, hz', sub_zero]
  · rintro _ ⟨f, hf, rfl⟩
    change q ((B.flatten S).jacquetMk X.representation f) = 0
    exact (productLeviQuotientMap_mk T B Q S A f).trans
      ((congrArg (refinedJacquetMk B S I.representation) hf).trans (map_zero _))

end Langlands.Geometric
