import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning

/-! # Compatible pinnings retaining a specified centralizer torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusCentralizerTorusData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (C : TorusCentralizerTorusData a) [LocallyOfFiniteType G.X.hom]
    [FiniteDimensional k K]
    (hA : IsSplitTorus A.toGrp) (hG : IsConnectedReductive G)
    (hRDE : RootDatumExistenceStatement.{u})
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj C.torus).toGrp)

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Construct compatible pinning data whose descended torus and inclusion are
definitionally the specified centralizer torus and inclusion. -/
def galoisCompatiblePinningData : GaloisCompatiblePinningData k K G := by
  let hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  let E : Nonempty
      (Σ (J : Type u),
        {P : RootDatum J
          (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj C.torus))
          (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj C.torus)) //
          Finite J ∧
            IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k K)).map C.inclusion) P ∧
              P.IsReduced}) := by
    obtain ⟨J, hJ, P, hP, hred⟩ :=
      hRDE K ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) hGK _ hT _
        (C.isMaximalTorus_baseChange K)
    exact ⟨⟨J, P, hJ, hP, hred⟩⟩
  let Q := Classical.choice E
  letI : Finite Q.1 := Q.2.property.1
  letI : Q.2.val.IsReduced := Q.2.property.2.2
  exact GaloisCompatiblePinningData.ofRegularCocharacter C.inclusion Q.2.property.2.1
    (C.regularCocharacter hA)
    (Q.2.property.2.1.root'_ne_zero_of_isRegularCocharacter
      (C.regularCocharacter_baseChange_isRegular K hA hT))
    hGK hT (C.isMaximalTorus_baseChange K)

@[simp]
theorem galoisCompatiblePinningData_torus :
    (C.galoisCompatiblePinningData hA hG hRDE hT).torus = C.torus := rfl

@[simp]
theorem galoisCompatiblePinningData_inclusion :
    (C.galoisCompatiblePinningData hA hG hRDE hT).inclusion = C.inclusion := rfl

end Langlands.GroupScheme.TorusCentralizerTorusData
