import Langlands.GroupScheme.Quaternionic.LocalSpinRankOneStatement
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.IdentityComponent.AlmostSimpleDescent

/-! # Reduction of spin-cover existence and uniqueness to semisimple geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
  [Smooth (σ.isometryGroup q).X.hom]

/-- Smoothness of the isometry group and semisimplicity of its identity component
give a spin cover over an arbitrary field. -/
theorem exists_isSpinCover_of_isSemisimple
    (hG : IsSemisimple (σ.connectedIsometryGroup q)) :
    ∃ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
      σ.IsSpinCover q π := by
  obtain ⟨S, p, hp⟩ :=
    simplyConnectedCoverExistence K (σ.connectedIsometryGroup q) hG
  refine ⟨S, p ≫ identityComponentι (σ.isometryGroup q), ?_⟩
  exact ⟨hp.isSimplyConnected, inferInstance, p, hp.isCentralIsogeny, rfl⟩

variable {σ q}

/-- Two spin covers of a form with semisimple connected isometry group are
isomorphic over the full isometry group. -/
theorem IsSpinCover.exists_iso
    {S S' : GroupScheme (Spec (CommRingCat.of K))}
    {π : S ⟶ σ.isometryGroup q} {π' : S' ⟶ σ.isometryGroup q}
    (hπ : σ.IsSpinCover q π) (hπ' : σ.IsSpinCover q π')
    (hG : IsSemisimple (σ.connectedIsometryGroup q)) :
    ∃ e : S ≅ S', e.hom ≫ π' = π := by
  obtain ⟨p, hp, hpπ⟩ := hπ.exists_centralIsogeny
  obtain ⟨p', hp', hp'π'⟩ := hπ'.exists_centralIsogeny
  have hcover : IsSimplyConnectedCover p :=
    ⟨hG, hπ.isSimplyConnected, hp,
      simplyConnectedCentralCoverUniversalProperty K S _ p
        hπ.isSimplyConnected hG hp⟩
  have hcover' : IsSimplyConnectedCover p' :=
    ⟨hG, hπ'.isSimplyConnected, hp',
      simplyConnectedCentralCoverUniversalProperty K S' _ p'
        hπ'.isSimplyConnected hG hp'⟩
  refine ⟨hcover.iso hcover', ?_⟩
  rw [← hp'π', ← Category.assoc, hcover.iso_hom_comp hcover', hpπ]

/-- Almost simplicity and split rank one need be checked on only one spin cover. -/
theorem IsSpinCover.properties_of_one
    {C : GroupScheme (Spec (CommRingCat.of K))}
    {π₀ : C ⟶ σ.isometryGroup q} (hπ₀ : σ.IsSpinCover q π₀)
    (hG : IsSemisimple (σ.connectedIsometryGroup q))
    (hC : IsAlmostSimple C) (hrank : splitRank C = 1)
    {S : GroupScheme (Spec (CommRingCat.of K))}
    {π : S ⟶ σ.isometryGroup q} (hπ : σ.IsSpinCover q π) :
    IsSimplyConnected S ∧ IsAlmostSimple S ∧ splitRank S = 1 := by
  obtain ⟨e, -⟩ := hπ.exists_iso hπ₀ hG
  exact ⟨hπ.isSimplyConnected, hC.of_iso e, (splitRank_eq_of_iso e).trans hrank⟩

omit [Smooth (σ.isometryGroup q).X.hom] in
/-- A smooth geometric model with absolutely almost-simple identity component
gives a spin cover before smoothness of the original isometry group is known. -/
theorem exists_isSpinCover_of_fieldExtension_iso
    {L : Type u} [Field L] [Algebra K L]
    {H : GroupScheme (Spec (CommRingCat.of L))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (e : (GroupScheme.baseChange (algebraBaseMap K L)).obj (σ.isometryGroup q) ≅ H)
    (hH : IsAbsolutelyAlmostSimple (identityComponent H)) :
    ∃ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
      σ.IsSpinCover q π := by
  obtain ⟨hsm, hG⟩ :=
    IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso e hH
  let := hsm
  exact σ.exists_isSpinCover_of_isSemisimple q hG.1.isSemisimple

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.Quaternionic

/-- Smoothness and semisimplicity of the connected isometry group give spin-cover
existence and uniqueness up to an isomorphism over the full isometry group. -/
def SpinCoverSemisimpleReductionStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (σ : FirstKindInvolution K D)
    (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    (hsm : Smooth (σ.isometryGroup q).X.hom),
    letI := hsm
    IsSemisimple (σ.connectedIsometryGroup q) →
      (∃ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π) ∧
      ∀ (S S' : GroupScheme (Spec (CommRingCat.of K)))
        (π : S ⟶ σ.isometryGroup q) (π' : S' ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π → σ.IsSpinCover q π' →
          ∃ e : S ≅ S', e.hom ≫ π' = π

theorem spinCoverSemisimpleReduction : SpinCoverSemisimpleReductionStatement.{u} := by
  intro K D _ _ _ _ σ n _ _ q hsm
  let := hsm
  intro hG
  refine ⟨σ.exists_isSpinCover_of_isSemisimple q hG, ?_⟩
  intro S S' π π' hπ hπ'
  exact hπ.exists_iso hπ' hG

end Langlands.GroupScheme.Quaternionic
