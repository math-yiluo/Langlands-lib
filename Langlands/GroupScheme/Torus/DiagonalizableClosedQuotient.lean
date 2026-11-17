import Langlands.GroupScheme.Torus.DiagonalizableClosedCharacterSurjection
import Langlands.GroupScheme.Torus.RelativeDiagonalizableExactQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.NormalQuotientFppfCoverGluing

/-! # Affine multiplicative-type quotients of closed diagonalizable inclusions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeMultiplicativeType

/-- Gluing supplied local multiplicative-type quotients preserves
multiplicative type of the actual quotient target. -/
theorem exists_quotient_of_local_quotients
    {S : Scheme.{u}} {H N : GroupScheme S} [IsAffineHom H.X.hom]
    (i : N ⟶ H) [Mono i.hom.hom] (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj H ⟶ Q j)
    (hQ : ∀ j, IsMultiplicativeType (Q j))
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : H ⟶ M), IsMultiplicativeType M ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r ∧
      IsAffineHom r.hom.hom.left := by
  obtain ⟨M, r, hMa, hr⟩ :=
    NormalQuotient.exists_affine_fppfQuotient_of_fppfCover i hn 𝒰 Q q
      (fun j => (hQ j).isAffineHom) hq
  have : IsAffineHom M.X.hom := hMa
  have : IsAffineHom (r.hom.hom.left ≫ M.X.hom) := by
    rw [Over.w]
    infer_instance
  have hra : IsAffineHom r.hom.hom.left := IsAffineHom.of_comp _ M.X.hom
  have htype : IsMultiplicativeType M := by
    apply IsMultiplicativeType.of_fppfCover 𝒰
    intro j
    have hrj : RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i))
        ((baseChange (𝒰.f j)).map r) := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hr.baseChange (𝒰.f j)
    have : IsAffineHom ((baseChange (𝒰.f j)).map r).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @IsAffineHom) (𝒰.f j) r.hom.hom hra
    have : IsAffineHom ((baseChange (𝒰.f j)).obj H).X.hom :=
      MorphismProperty.pullback_snd H.X.hom (𝒰.f j) inferInstance
    have : IsAffineHom (Q j).X.hom := (hQ j).isAffineHom
    have : QuasiCompact ((q j).hom.hom.left ≫ (Q j).X.hom) := by
      rw [Over.w]
      infer_instance
    have : QuasiCompact (q j).hom.hom.left :=
      QuasiCompact.of_comp _ (Q j).X.hom
    exact IsMultiplicativeType.of_iso (FppfQuotientComparison.iso hrj (hq j)) (hQ j)
  exact ⟨M, r, htype, hr, hra⟩

end RelativeMultiplicativeType

namespace Diagonalizable

variable {R : CommRingCat.{u}} {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]

/-- The explicit full exact quotient is fppf over every coefficient ring. -/
theorem isFppfQuotient_exactQuotientMap_arbitraryRing [AddGroup.FG Λ]
    (p : Λ →+ Γ) (hp : Function.Surjective p) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (restrictMap R p))
      (exactQuotientMap R p) := by
  let b := Gm.toSpecZ (Spec R)
  let q := (baseChange b).map
    (exactQuotientMap (CommRingCat.of (ULift.{u} ℤ)) p)
  have hq := RelativeMultiplicativeType.isFppfQuotient_diagonalizableExactQuotientMap
    (Spec R) p hp
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let aΛ := baseChangeIso b Λ
  let aK := baseChangeIso b p.ker
  have hn : q ≫ aK.hom = aΛ.hom ≫ exactQuotientMap R p :=
    baseChangeIso_restrictMap b p.ker.subtype
  have heq : exactQuotientMap R p = aΛ.inv ≫ q ≫ aK.hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  have : IsIso aΛ.inv.hom.hom.left := (Over.forget _).map_isIso aΛ.inv.hom.hom
  have : IsIso aK.hom.hom.hom.left := (Over.forget _).map_isIso aK.hom.hom.hom
  refine ⟨?_, ?_, ?_, kernel_exactQuotientMap R p hp⟩
  · rw [heq]
    change Flat (aΛ.inv.hom.hom.left ≫ q.hom.hom.left ≫ aK.hom.hom.hom.left)
    infer_instance
  · rw [heq]
    change Surjective (aΛ.inv.hom.hom.left ≫ q.hom.hom.left ≫ aK.hom.hom.hom.left)
    infer_instance
  · rw [heq]
    change LocallyOfFinitePresentation
      (aΛ.inv.hom.hom.left ≫ q.hom.hom.left ≫ aK.hom.hom.hom.left)
    infer_instance

/-- A closed inclusion between diagonalizable groups has an actual affine
quotient of multiplicative type over the original arbitrary ring. -/
theorem exists_quotient_of_closed_inclusion [AddGroup.FG Λ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)
    (hf : IsClosedSubgroup f) :
    ∃ (Q : GroupScheme (Spec R)) (q : (groupScheme R Λ).toGrp ⟶ Q),
      RelativeMultiplicativeType.IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range f) q ∧
      IsAffineHom q.hom.hom.left := by
  have : IsAffineHom (groupScheme R Λ).X.hom := Diagonalizable.isAffineHom R Λ
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have hn : (SubgroupFunctor.range f).IsNormal := by
    intro T g x _ hx
    simpa only [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one] using hx
  let 𝒰 := restrictionCover f
  let p := restrictionCharacterMap f
  have hp (j : 𝒰.I₀) : Function.Surjective (p j) :=
    restrictionCharacterMap_surjective f hf j
  let Q := fun j : 𝒰.I₀ => (baseChange (𝒰.f j)).obj (groupScheme R (p j).ker).toGrp
  let q := fun j : 𝒰.I₀ => (baseChange (𝒰.f j)).map (exactQuotientMap R (p j))
  have hQ (j : 𝒰.I₀) : RelativeMultiplicativeType.IsMultiplicativeType (Q j) := by
    have := RelativeMultiplicativeType.exactQuotientCharacters_fg (p j)
    exact RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      ((isDiagonalizable_groupScheme R (p j).ker).baseChange (𝒰.f j))
  have hq (j : 𝒰.I₀) : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map f)) (q j) := by
    rw [restrictionCover_map_eq, SubgroupFunctor.range_baseChangeHom]
    exact (isFppfQuotient_exactQuotientMap_arbitraryRing (p j) (hp j)).baseChange (𝒰.f j)
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage (Spec R) :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  exact RelativeMultiplicativeType.exists_quotient_of_local_quotients
    f hn 𝒱 Q q hQ hq

/-- A chosen actual affine multiplicative-type quotient of a closed
diagonalizable subgroup inclusion. -/
def closedQuotient [AddGroup.FG Λ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)
    (hf : IsClosedSubgroup f) :
    Σ (Q : GroupScheme (Spec R)), {q : (groupScheme R Λ).toGrp ⟶ Q //
      RelativeMultiplicativeType.IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range f) q ∧
      IsAffineHom q.hom.hom.left} := by
  let h := exists_quotient_of_closed_inclusion f hf
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Diagonalizable
end Langlands.GroupScheme
