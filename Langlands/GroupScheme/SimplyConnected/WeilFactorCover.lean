import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionProof
import Langlands.GroupScheme.Rational.AffineWeilSplitRankProof
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank

/-! # Actual Weil factors in simply connected central covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
  {C A G : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual Weil presentation of a prescribed almost-simple direct factor,
with an actual simply connected complementary group and the original insertion
retained in the product isomorphism. -/
structure SimplyConnectedWeilFactor (j : A ⟶ C) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra k extension]
  [finiteDimensional : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  factor : GroupScheme (Spec (CommRingCat.of extension))
  [affine : IsAffine factor.X.left]
  [affineHom : IsAffineHom factor.X.hom]
  [finiteType : LocallyOfFiniteType factor.X.hom]
  simplyConnected : IsSimplyConnected factor
  absolutelyAlmostSimple : IsAbsolutelyAlmostSimple factor
  weilIso : A ≅ AffineWeil.groupScheme k extension factor
  complement : GroupScheme (Spec (CommRingCat.of k))
  complement_simplyConnected : IsSimplyConnected complement
  productIso : AffineWeil.groupScheme k extension factor ⊗ complement ≅ C
  product_simplyConnected :
    IsSimplyConnected (AffineWeil.groupScheme k extension factor ⊗ complement)
  left_eq :
    lift (𝟙 (AffineWeil.groupScheme k extension factor))
        (Grp.homMk (toUnit _ ≫ η[complement.X])) ≫ productIso.hom = weilIso.inv ≫ j

attribute [instance] SimplyConnectedWeilFactor.field SimplyConnectedWeilFactor.algebra
  SimplyConnectedWeilFactor.finiteDimensional SimplyConnectedWeilFactor.separable
  SimplyConnectedWeilFactor.affine SimplyConnectedWeilFactor.affineHom
  SimplyConnectedWeilFactor.finiteType

namespace SimplyConnectedWeilFactor

variable {j : A ⟶ C} (F : SimplyConnectedWeilFactor j)

/-- The resulting actual homomorphism from the Weil factor and its complement. -/
def cover (π : C ⟶ G) :
    (AffineWeil.groupScheme k F.extension F.factor ⊗ F.complement) ⟶ G :=
  F.productIso.hom ≫ π

/-- Composing the actual product isomorphism with a central cover retains
its full scheme-theoretic central kernel. -/
theorem cover_centralIsogeny {π : C ⟶ G} (hπ : IsCentralIsogeny π) :
    IsCentralIsogeny (F.cover π) :=
  hπ.iso_comp F.productIso

/-- The factor inclusion in the new cover is the original factor inclusion,
precomposed with the inverse of its Weil presentation. -/
theorem left_cover (π : C ⟶ G) :
    lift (𝟙 (AffineWeil.groupScheme k F.extension F.factor))
        (Grp.homMk (toUnit _ ≫ η[F.complement.X])) ≫ F.cover π =
      F.weilIso.inv ≫ j ≫ π := by
  rw [cover, ← Category.assoc, F.left_eq, Category.assoc]

/-- Anisotropy descends to the extension-field factor of a finite map into
an affine anisotropic group, provided the prescribed insertion is closed. -/
theorem anisotropic_of_isFinite [IsAffineHom G.X.hom]
    (hj : IsClosedSubgroup j) (π : C ⟶ G) [IsFinite π.hom.hom.left]
    (hG : IsAnisotropic G) : IsAnisotropic F.factor := by
  have hC : IsAnisotropic C := by
    apply le_antisymm _ bot_le
    exact (splitRank_le_of_isFinite π).trans_eq hG
  have hA : IsAnisotropic A := by
    apply le_antisymm _ bot_le
    exact (splitRank_le_of_isClosedSubgroup j hj).trans_eq hC
  change splitRank F.factor = 0
  rw [← affineWeilSplitRank k F.extension F.factor
    F.simplyConnected.isSemisimple.isConnectedReductive]
  rw [← splitRank_eq_of_iso F.weilIso]
  exact hA

end SimplyConnectedWeilFactor

namespace SimplyConnectedAlmostSimpleProduct

variable {C : GroupScheme (Spec (CommRingCat.of k))}
  (D : SimplyConnectedAlmostSimpleProduct C)

/-- Every prescribed almost-simple factor in a simply connected product
has an actual absolutely almost-simple Weil presentation and an actual
simply connected complement, with its original insertion preserved. -/
theorem nonempty_weilFactor (hC : IsSimplyConnected C) (i : D.Index) :
    Nonempty (SimplyConnectedWeilFactor (D.inclusion i)) := by
  let hCr := hC.isSemisimple.isConnectedReductive
  let := hCr.isAffineHom
  let hA := (D.isSimplyConnected i).isSemisimple.isConnectedReductive
  let := hA.isAffineHom
  obtain ⟨hAs, N, n, hN, _hn, _hnormal, hprod, hc, hm⟩ :=
    semisimpleNormalIsogenyComplement k C (D.factor i) hC.isSemisimple
      (D.inclusion i) (D.isClosedSubgroup_inclusion i) hA.smooth hA.connectedSpace
      (D.isNormal_range_inclusion i)
  let m := commutingSubgroupMultiplicationHom (D.inclusion i) n hc
  let : IsIso m := hC.central_isogeny_isIso _ m hprod hm
  have hscProd : IsSimplyConnected (D.factor i ⊗ N) := hC.of_iso (asIso m)
  have hscN : IsSimplyConnected N := hscProd.of_tensor_right hAs hN
  obtain ⟨E, hE, hAlg, hFin, hSep, H, hAff, hFt, hscH, haH, ⟨e⟩⟩ :=
    simplyConnectedAlmostSimpleWeilRestriction k (D.factor i)
      (D.isSimplyConnected i) (D.isAlmostSimple i)
  let := hE
  let := hAlg
  let := hFin
  let := hSep
  let := hAff
  let := hFt
  let := hscH.isSemisimple.isConnectedReductive.isAffineHom
  let eprod : AffineWeil.groupScheme k E H ⊗ N ≅ C :=
    (e.symm ⊗ᵢ Iso.refl N) ≪≫ asIso m
  refine ⟨{
    extension := E
    factor := H
    simplyConnected := hscH
    absolutelyAlmostSimple := haH
    weilIso := e
    complement := N
    complement_simplyConnected := hscN
    productIso := eprod
    product_simplyConnected := hC.of_iso eprod
    left_eq := ?_ }⟩
  apply Grp.hom_ext
  change (lift (𝟙 _) (toUnit _ ≫ η[N.X])) ≫
    (e.inv.hom.hom ⊗ₘ 𝟙 N.X) ≫ subgroupMultiplication (D.inclusion i) n =
      e.inv.hom.hom ≫ (D.inclusion i).hom.hom
  simp only [subgroupMultiplication, MonObj.comp_mul, tensorHom_fst_assoc,
    tensorHom_snd_assoc, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
  change (e.inv.hom.hom ≫ (D.inclusion i).hom.hom) *
    ((1 : (AffineWeil.groupScheme k E H).X ⟶ N.X) ≫ n.hom.hom) = _
  rw [MonObj.one_comp, mul_one]

/-- A chosen actual extension-field factor of the prescribed product factor. -/
def weilFactor (hC : IsSimplyConnected C) (i : D.Index) :
    SimplyConnectedWeilFactor (D.inclusion i) :=
  Classical.choice (D.nonempty_weilFactor hC i)

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
