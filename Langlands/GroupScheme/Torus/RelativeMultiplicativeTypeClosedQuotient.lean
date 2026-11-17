import Langlands.GroupScheme.Torus.DiagonalizableClosedQuotient

/-! # Quotients of relative multiplicative-type groups by closed multiplicative-type subgroups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeMultiplicativeType

private theorem range_isNormal_of_comm
    {S : Scheme.{u}} {H N : GroupScheme S} [IsCommMonObj H.X] (i : N ⟶ H) :
    (SubgroupFunctor.range i).IsNormal := by
  intro T g x _ hx
  simpa only [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- Quotients of two supplied diagonalizable models over an affine base. -/
theorem exists_quotient_of_diagonalizable_affine
    (R : CommRingCat.{u}) {H N : GroupScheme (Spec R)}
    (hH : IsDiagonalizable H) (hN : IsDiagonalizable N)
    (i : N ⟶ H) (hi : IsClosedSubgroup i) :
    ∃ (Q : GroupScheme (Spec R)) (q : H ⟶ Q), IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      IsAffineHom q.hom.hom.left := by
  obtain ⟨Λ, _, _, ⟨eH⟩⟩ := hH
  obtain ⟨Γ, _, _, ⟨eN⟩⟩ := hN
  let aH := eH ≪≫ (Diagonalizable.relativeModelIso R Λ).symm
  let aN := eN ≪≫ (Diagonalizable.relativeModelIso R Γ).symm
  let f := aN.inv ≫ i ≫ aH.hom
  have hf : IsClosedSubgroup f :=
    IsClosedSubgroup.iso_comp aN.symm (hi.comp_iso aH)
  obtain ⟨Q, q, hQ, hq, hqa⟩ :=
    Diagonalizable.exists_quotient_of_closed_inclusion f hf
  have hc : i ≫ aH.hom = aN.hom ≫ f := by
    simp only [f, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) (aH.hom ≫ q) :=
    RelativeRoot.IsFppfQuotient.of_iso_square f i q aH aN hc hq
  have : IsAffineHom q.hom.hom.left := hqa
  have : IsIso aH.hom.hom.hom.left := (Over.forget _).map_isIso aH.hom.hom.hom
  refine ⟨Q, aH.hom ≫ q, hQ, hq', ?_⟩
  change IsAffineHom (aH.hom.hom.hom.left ≫ q.hom.hom.left)
  infer_instance

/-- Closed inclusions between diagonalizable groups over an arbitrary scheme
have affine full quotients of multiplicative type. -/
theorem exists_quotient_of_diagonalizable
    {S : Scheme.{u}} {H N : GroupScheme S}
    (hH : IsDiagonalizable H) (hN : IsDiagonalizable N)
    (i : N ⟶ H) (hi : IsClosedSubgroup i) :
    ∃ (Q : GroupScheme S) (q : H ⟶ Q), IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      IsAffineHom q.hom.hom.left := by
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsCommMonObj H.X := hH.isCommMonObj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let 𝒰 := S.affineOpenCover
  have hlocal (j : 𝒰.I₀) :
      ∃ (Q : GroupScheme (Spec (𝒰.X j)))
        (q : (baseChange (𝒰.f j)).obj H ⟶ Q), IsMultiplicativeType Q ∧
        RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) q ∧
        IsAffineHom q.hom.hom.left :=
    exists_quotient_of_diagonalizable_affine (𝒰.X j)
      (hH.baseChange (𝒰.f j)) (hN.baseChange (𝒰.f j))
      _ (hi.baseChange (𝒰.f j))
  choose Q q hQ hq hqa using hlocal
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S :=
    𝒰.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  exact exists_quotient_of_local_quotients i (range_isNormal_of_comm i) 𝒱 Q q hQ hq

/-- A diagonalizable source and a closed multiplicative-type subgroup
have an affine full quotient of multiplicative type. -/
theorem exists_quotient_of_diagonalizable_source
    {S : Scheme.{u}} {H N : GroupScheme S}
    (hH : IsDiagonalizable H) (hN : IsMultiplicativeType N)
    (i : N ⟶ H) (hi : IsClosedSubgroup i) :
    ∃ (Q : GroupScheme S) (q : H ⟶ Q), IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      IsAffineHom q.hom.hom.left := by
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsCommMonObj H.X := hH.isCommMonObj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨𝒰, h𝒰⟩ := hN
  have hlocal (j : 𝒰.I₀) :
      ∃ (Q : GroupScheme (𝒰.X j))
        (q : (baseChange (𝒰.f j)).obj H ⟶ Q), IsMultiplicativeType Q ∧
        RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) q ∧
        IsAffineHom q.hom.hom.left :=
    exists_quotient_of_diagonalizable (hH.baseChange (𝒰.f j)) (h𝒰 j)
      _ (hi.baseChange (𝒰.f j))
  choose Q q hQ hq hqa using hlocal
  exact exists_quotient_of_local_quotients i (range_isNormal_of_comm i) 𝒰 Q q hQ hq

/-- A closed multiplicative-type subgroup of a multiplicative-type group
admits an actual affine full quotient of multiplicative type over every base. -/
theorem exists_quotient_of_multiplicativeType
    {S : Scheme.{u}} {H N : GroupScheme S}
    (hH : IsMultiplicativeType H) (hN : IsMultiplicativeType N)
    (i : N ⟶ H) (hi : IsClosedSubgroup i) :
    ∃ (Q : GroupScheme S) (q : H ⟶ Q), IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      IsAffineHom q.hom.hom.left := by
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsCommMonObj H.X := hH.isCommMonObj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨𝒰, h𝒰⟩ := hH
  have hlocal (j : 𝒰.I₀) :
      ∃ (Q : GroupScheme (𝒰.X j))
        (q : (baseChange (𝒰.f j)).obj H ⟶ Q), IsMultiplicativeType Q ∧
        RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) q ∧
        IsAffineHom q.hom.hom.left :=
    exists_quotient_of_diagonalizable_source (h𝒰 j) (hN.baseChange (𝒰.f j))
      _ (hi.baseChange (𝒰.f j))
  choose Q q hQ hq hqa using hlocal
  exact exists_quotient_of_local_quotients i (range_isNormal_of_comm i) 𝒰 Q q hQ hq

/-- A chosen affine quotient by a closed relative multiplicative-type subgroup. -/
def closedSubgroupQuotient
    {S : Scheme.{u}} {H N : GroupScheme S}
    (hH : IsMultiplicativeType H) (hN : IsMultiplicativeType N)
    (i : N ⟶ H) (hi : IsClosedSubgroup i) :
    Σ (Q : GroupScheme S), {q : H ⟶ Q // IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      IsAffineHom q.hom.hom.left} := by
  let h := exists_quotient_of_multiplicativeType hH hN i hi
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme.RelativeMultiplicativeType
