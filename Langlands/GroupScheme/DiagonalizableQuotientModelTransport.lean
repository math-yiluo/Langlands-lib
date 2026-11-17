import Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientReduction
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # Transport from direct diagonalizable quotient models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The affine normal quotient problem with a specified direct diagonalizable
kernel over the spectrum of a ring. -/
def AffineDiagonalizableModelQuotientStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
    ∃ (Q : GroupScheme (Spec R)) (q : G ⟶ Q), IsAffineHom Q.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

/-- Quotient existence for direct ring models suffices for all diagonalizable
normal kernels over arbitrary affine schemes. -/
theorem affineDiagonalizableNormalQuotient_of_model
    (hmodel : AffineDiagonalizableModelQuotientStatement.{u}) :
    AffineDiagonalizableNormalQuotientStatement.{u} := by
  intro S _ G N _ i hi hn hN
  let R := Γ(S, ⊤)
  let p : Spec R ⟶ S := S.isoSpec.inv
  let Gp := (baseChange p).obj G
  let Np := (baseChange p).obj N
  let ip : Np ⟶ Gp := (baseChange p).map i
  have : IsAffineHom Gp.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom p))
  have : IsAffine Gp.X.left := isAffine_of_isAffineHom Gp.X.hom
  have hip : IsClosedSubgroup ip := hi.baseChange p
  let : IsClosedImmersion ip.hom.hom.left := hip
  have hnp : (SubgroupFunctor.range ip).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange p
  obtain ⟨M, _, _, ⟨e⟩⟩ := hN.baseChange p
  let d : Np ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  let j : (Diagonalizable.groupScheme R M).toGrp ⟶ Gp := d.inv ≫ ip
  have hjrange : SubgroupFunctor.range j = SubgroupFunctor.range ip :=
    SubgroupFunctor.range_iso_comp d.symm ip
  have : IsIso d.inv.hom.hom := (Grp.forget (Over (Spec R))).map_isIso d.inv
  have : IsIso d.inv.hom.hom.left := (Over.forget (Spec R)).map_isIso d.inv.hom.hom
  have hj : IsClosedSubgroup j := by
    change IsClosedImmersion (d.inv.hom.hom.left ≫ ip.hom.hom.left)
    infer_instance
  have hjn : (SubgroupFunctor.range j).IsNormal := by
    rw [hjrange]
    exact hnp
  obtain ⟨Q, q, hQ, hq⟩ := hmodel R M Gp j hj hjn
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ip) q := by
    rwa [hjrange] at hq
  let : IsAffineHom Q.X.hom := hQ
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Q₀, q₀, hQ₀, hq₀, _⟩ := Descent.exists_affine_fppfQuotient p i Q q hq'
  let : IsAffine Q₀.X.left := hQ₀
  exact ⟨Q₀, q₀, inferInstance, hq₀⟩

/-- The direct ring-model quotient construction implies the unchanged
central multiplicative-type quotient statement over arbitrary bases. -/
theorem relativeCentralMultiplicativeTypeQuotient_of_affineDiagonalizableModel
    (hmodel : AffineDiagonalizableModelQuotientStatement.{u}) :
    RelativeCentralMultiplicativeTypeQuotientStatement.{u} :=
  relativeCentralMultiplicativeTypeQuotient_of_affineDiagonalizable
    (affineDiagonalizableNormalQuotient_of_model hmodel)

end Langlands.GroupScheme
