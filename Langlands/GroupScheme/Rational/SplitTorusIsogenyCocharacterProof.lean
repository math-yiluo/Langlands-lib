import Langlands.GroupScheme.Rational.SplitTorusIsogenyQuasiInverse
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every isogeny between actual split tori has a two-sided nonzero integer quasiinverse. -/
theorem IsSplitTorus.exists_isogeny_quasiInverse (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    (hf : IsIsogeny (CommGroupScheme.groupHom f)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ g : T ⟶ A,
      f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 T := by
  classical
  obtain ⟨I, hI, ⟨eA⟩⟩ := hA
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT
  let := hI
  let := hJ
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let eA' : A ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso eA
  let eT' : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J :=
    CommGroupScheme.isoOfGroupIso eT
  let q : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J :=
    eA.inv ≫ CommGroupScheme.groupHom f ≫ eT.hom
  have hq : IsIsogeny q :=
    (isCentralIsogeny_of_isIso eA.inv).isIsogeny.comp
      (hf.comp (isCentralIsogeny_of_isIso eT.hom).isIsogeny)
  have : IsFinite q.hom.hom.left := hq.1
  have : Flat q.hom.hom.left := hq.2.1
  have : Surjective q.hom.hom.left := hq.2.2
  have : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
  obtain ⟨n, hn, g, hfg, hgf⟩ := splitTorus.exists_integer_quasiInverse I J q
  let a : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J := Additive.ofMul q
  have ha : a = eA'.inv ≫ f ≫ eT'.hom := rfl
  change a ≫ g = n • 𝟙 _ at hfg
  change g ≫ a = n • 𝟙 _ at hgf
  refine ⟨n, hn, eT'.hom ≫ g ≫ eA'.inv, ?_, ?_⟩
  · calc
      f ≫ (eT'.hom ≫ g ≫ eA'.inv) = eA'.hom ≫ (a ≫ g) ≫ eA'.inv := by
        rw [ha]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = n • 𝟙 A := by
        rw [hfg]
        simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
          Category.id_comp, Iso.hom_inv_id]
  · calc
      (eT'.hom ≫ g ≫ eA'.inv) ≫ f = eT'.hom ≫ (g ≫ a) ≫ eT'.inv := by
        rw [ha]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = n • 𝟙 T := by
        rw [hgf]
        simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
          Category.id_comp, Iso.hom_inv_id]

/-- The exact comparison on the published actual integral, rational and real cocharacter maps. -/
theorem splitTorusIsogenyCocharacter : SplitTorusIsogenyCocharacterStatement.{u} := by
  intro k _ A T f hA hT hf
  obtain ⟨n, hn, g, hfg, hgf⟩ := hA.exists_isogeny_quasiInverse hT f hf
  exact SplitTorusIsogeny.cocharacter_isogeny_conclusions_of_quasiInverse
    f g n hn hA hT hfg hgf

end Langlands.GroupScheme
