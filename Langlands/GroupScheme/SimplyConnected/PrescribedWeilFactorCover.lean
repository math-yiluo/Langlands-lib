import Langlands.GroupScheme.SimplyConnected.WeilFactorCover
import Langlands.GroupScheme.Reductive.TitsComponentFactorStatement

/-! # Prescribed extension-field models in actual component covers -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme
namespace SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {C : GroupScheme (Spec (CommRingCat.of k))} (D : SimplyConnectedAlmostSimpleProduct C)

/-- An actual simply connected complement to the prescribed original product
factor, retaining its insertion in the product isomorphism. -/
structure FactorComplement (i : D.Index) where
  group : GroupScheme (Spec (CommRingCat.of k))
  simplyConnected : IsSimplyConnected group
  iso : D.factor i ⊗ group ≅ C
  left_eq : lift (𝟙 (D.factor i)) (Grp.homMk (toUnit _ ≫ η[group.X])) ≫ iso.hom =
    D.inclusion i

/-- The normal complement theorem and simple connectedness give an actual
product complement to any prescribed almost-simple product factor. -/
theorem nonempty_factorComplement (hC : IsSimplyConnected C) (i : D.Index) :
    Nonempty (D.FactorComplement i) := by
  let hCr := hC.isSemisimple.isConnectedReductive
  let := hCr.isAffineHom
  let hA := (D.isSimplyConnected i).isSemisimple.isConnectedReductive
  obtain ⟨hAs, N, n, hN, _hn, _hnormal, hprod, hc, hm⟩ :=
    semisimpleNormalIsogenyComplement k C (D.factor i) hC.isSemisimple
      (D.inclusion i) (D.isClosedSubgroup_inclusion i) hA.smooth hA.connectedSpace
      (D.isNormal_range_inclusion i)
  let m := commutingSubgroupMultiplicationHom (D.inclusion i) n hc
  have : IsIso m := hC.central_isogeny_isIso _ m hprod hm
  have hscProd : IsSimplyConnected (D.factor i ⊗ N) := hC.of_iso (asIso m)
  refine ⟨{
    group := N
    simplyConnected := hscProd.of_tensor_right hAs hN
    iso := asIso m
    left_eq := ?_ }⟩
  apply Grp.hom_ext
  change lift (𝟙 (D.factor i).X) (toUnit _ ≫ η[N.X]) ≫
    subgroupMultiplication (D.inclusion i) n = (D.inclusion i).hom.hom
  rw [comp_subgroupMultiplication, Category.id_comp]
  change (D.inclusion i).hom.hom * ((1 : (D.factor i).X ⟶ N.X) ≫ n.hom.hom) = _
  rw [MonObj.one_comp, mul_one]

/-- Choose a complement independently of any future extension-field model. -/
def factorComplement (hC : IsSimplyConnected C) (i : D.Index) : D.FactorComplement i :=
  Classical.choice (D.nonempty_factorComplement hC i)

variable (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]
  (H : GroupScheme (Spec (CommRingCat.of E)))
  [IsAffine H.X.left] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Use an explicitly prescribed field, group and Weil presentation in the
actual covering product. The extension and factor are definitionally the
supplied `E` and `H`. -/
def weilFactorOfIso (hC : IsSimplyConnected C) (i : D.Index)
    (hH : IsSimplyConnected H) (hHA : IsAbsolutelyAlmostSimple H)
    (e : D.factor i ≅ AffineWeil.groupScheme k E H) :
    SimplyConnectedWeilFactor (D.inclusion i) := by
  let N := D.factorComplement hC i
  let eprod : AffineWeil.groupScheme k E H ⊗ N.group ≅ C :=
    (e.symm ⊗ᵢ Iso.refl N.group) ≪≫ N.iso
  refine {
    extension := E
    factor := H
    simplyConnected := hH
    absolutelyAlmostSimple := hHA
    weilIso := e
    complement := N.group
    complement_simplyConnected := N.simplyConnected
    productIso := eprod
    product_simplyConnected := hC.of_iso eprod
    left_eq := ?_ }
  have hleft : lift (𝟙 (AffineWeil.groupScheme k E H))
      (Grp.homMk (toUnit _ ≫ η[N.group.X])) ≫ (e.inv ⊗ₘ 𝟙 N.group) =
      e.inv ≫ lift (𝟙 (D.factor i)) (Grp.homMk (toUnit _ ≫ η[N.group.X])) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst_assoc,
        Category.id_comp, lift_fst]
    · simp only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]
      apply Grp.hom_ext
      change (toUnit _ ≫ η[N.group.X]) = e.inv.hom.hom ≫ (toUnit _ ≫ η[N.group.X])
      rw [← Category.assoc, toUnit_unique (e.inv.hom.hom ≫ toUnit _) (toUnit _)]
  change (lift (𝟙 _) (Grp.homMk (toUnit _ ≫ η[N.group.X])) ≫
      (e.inv ⊗ₘ 𝟙 N.group)) ≫ N.iso.hom = e.inv ≫ D.inclusion i
  rw [hleft, Category.assoc, N.left_eq]

@[simp] theorem weilFactorOfIso_extension (hC : IsSimplyConnected C) (i : D.Index)
    (hH : IsSimplyConnected H) (hHA : IsAbsolutelyAlmostSimple H)
    (e : D.factor i ≅ AffineWeil.groupScheme k E H) :
    (D.weilFactorOfIso E H hC i hH hHA e).extension = E := rfl

@[simp] theorem weilFactorOfIso_factor (hC : IsSimplyConnected C) (i : D.Index)
    (hH : IsSimplyConnected H) (hHA : IsAbsolutelyAlmostSimple H)
    (e : D.factor i ≅ AffineWeil.groupScheme k E H) :
    (D.weilFactorOfIso E H hC i hH hHA e).factor = H := rfl

end SimplyConnectedAlmostSimpleProduct

namespace SimplyConnectedWeilFactor

variable {k : Type u} [Field k]
  {C A : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom]
  {j : A ⟶ C} (F : SimplyConnectedWeilFactor j)

/-- Assemble the complete original component witness from a prescribed
actual Weil-factor cover and the entire Cartan/full-star comparison. -/
def componentFactor (hj : IsClosedSubgroup j) (d : TitsIndexData C) (a : d.Vertex)
    (index : TitsIndexData F.factor) (v : index.Vertex ≃ d.CartanComponent a)
    (hcartan : ∀ b c, d.cartan (v b).val (v c).val = index.cartan b c)
    (hstabilizer : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
      d.CartanConnected a (d.star σ a) →
        ∃ τ : SeparableClosure F.extension ≃ₐ[F.extension] SeparableClosure F.extension,
          ∀ b, (v (index.star τ b)).val = d.star σ (v b).val)
    (hstar : ∀ (τ : SeparableClosure F.extension ≃ₐ[F.extension] SeparableClosure F.extension),
      ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        ∀ b, (v (index.star τ b)).val = d.star σ (v b).val) :
    d.ComponentFactor a where
  extension := F.extension
  factor := F.factor
  simplyConnected := F.simplyConnected
  absolutelyAlmostSimple := F.absolutelyAlmostSimple
  complement := F.complement
  complement_simplyConnected := F.complement_simplyConnected
  cover := F.cover (𝟙 C)
  cover_simplyConnected := F.product_simplyConnected
  cover_centralIsogeny := F.cover_centralIsogeny (isCentralIsogeny_id C)
  index := index
  vertexEquiv := v
  cartan_eq := hcartan
  stabilizer_lift := hstabilizer
  star_lift := hstar
  anisotropic := F.anisotropic_of_isFinite hj (𝟙 C)

end SimplyConnectedWeilFactor
end Langlands.GroupScheme
