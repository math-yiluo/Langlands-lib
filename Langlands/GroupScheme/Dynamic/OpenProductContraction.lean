import Langlands.GroupScheme.Dynamic.OrbitOpenLift
import Langlands.GroupScheme.Dynamic.OppositeCellContraction

/-! # Orbit contractions through normalized open products -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- The multiplication presentation of two group homomorphisms contains the identity. -/
theorem identity_mem_product_opensRange (iH : H ⟶ G) (iK : K ⟶ G)
    [IsOpenImmersion
      ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom)).left] :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left
        (⊥ : PrimeSpectrum k) ∈
      ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom)).left.opensRange := by
  let z := lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X)
  have hz : z ≫ ((fst H.X K.X ≫ iH.hom.hom) *
      (snd H.X K.X ≫ iK.hom.hom)) = 1 := by
    simp only [z, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, one_mul]
  refine ⟨z.left (⊥ : PrimeSpectrum k), ?_⟩
  exact congrArg (fun f => f.left (⊥ : PrimeSpectrum k)) hz

variable [IsSeparated G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (iH : H ⟶ G) (iK : K ⟶ G)
  [IsOpenImmersion
    ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom)).left]
  (hH : (SubgroupFunctor.range iH).IsNormalizedBy (SubgroupFunctor.range χ))
  (hK : (SubgroupFunctor.range iK).IsNormalizedBy (SubgroupFunctor.range χ))
  {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
  {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
    AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
  (he : IsOrbitExtension χ g e) (he0 : evalZero e = 1)

/-- Lift an identity-limit orbit extension through a normalized open product. -/
def openProductOrbitLift :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ H.X ⊗ K.X :=
  orbitOpenLift χ
    ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom))
    (isCocharacterStable_product χ iH iK hH hK) he
    (by rw [he0]; exact identity_mem_product_opensRange iH iK)

@[reassoc]
theorem openProductOrbitLift_fac :
    openProductOrbitLift χ iH iK hH hK he he0 ≫
      ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom)) = e :=
  orbitOpenLift_fac χ _ _ _ _

include hH hK he he0 in
/-- A normalized open product of represented subgroups contains every orbit contraction. -/
theorem hasProductContraction_of_openProduct
    {A B : SubgroupFunctor G} (hA : A.IsRepresentedBy iH) (hB : B.IsRepresentedBy iK) :
    HasProductContraction χ A B g :=
  hasProductContraction_of_represented_lift χ A B hA hB he he0
    (openProductOrbitLift χ iH iK hH hK he he0)
    (openProductOrbitLift_fac χ iH iK hH hK he he0)

end Langlands.GroupScheme.Dynamic
