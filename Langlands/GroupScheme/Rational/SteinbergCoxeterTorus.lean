import Langlands.LinearAlgebra.CoxeterFixedSpace
import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Torus.CommutatorEnd
import Langlands.GroupScheme.Torus.CharacterFaithfullyFlat
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity

/-! # Faithful flatness of the actual Coxeter torus commutator -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Commutator

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The character kernel of the actual commutator map is the Weyl fixed lattice. -/
theorem comap_torusCommutatorEnd_eq_zero_iff (n : normalizerPoints i)
    (χ : characterLattice T) :
    characterLattice.comapHom (CommGroupScheme.groupHom (torusCommutatorEnd i n)) χ = 0 ↔
      weylAction i n χ = χ := by
  change ((normalizingAut i n).hom - 𝟙 T) ≫ χ = 0 ↔
    (normalizingAut i n).inv ≫ χ = χ
  rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero]
  constructor
  · intro h
    have hh := congrArg (fun f => (normalizingAut i n).inv ≫ f) h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hh.symm
  · intro h
    have hh := congrArg (fun f => (normalizingAut i n).hom ≫ f) h
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hh.symm

end Commutator

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

/-- A supplied simple-reflection representative as a point of the actual normalizer. -/
def SimpleReflectionRepresentative.normalizerPoint {a : p.base.support}
    (n : p.SimpleReflectionRepresentative a) : normalizerPoints p.inclusion :=
  ⟨n.point, n.torusAut, n.normalizes⟩

theorem SimpleReflectionRepresentative.weylAction_normalizerPoint {a : p.base.support}
    (n : p.SimpleReflectionRepresentative a) :
    weylAction p.inclusion n.normalizerPoint = p.rootDatum.reflection a := by
  have h := (isNormalizingPoint_normalizingAut p.inclusion n.normalizerPoint).unique
    p.inclusion n.normalizes
  change characterAut (normalizingAut p.inclusion n.normalizerPoint) = _
  rw [h]
  exact n.characterAut_eq

variable {r : ℕ} (e : Fin r ≃ p.base.support)
    (n : p.SimpleReflectionRepresentatives)

/-- The ordered product of the supplied actual normalizer points. -/
def coxeterNormalizer : normalizerPoints p.inclusion :=
  (List.ofFn fun j => (n (e j)).normalizerPoint).prod

/-- Its action on the full character lattice is the actual ordered Coxeter product. -/
theorem weylAction_coxeterNormalizer :
    weylAction p.inclusion (coxeterNormalizer e n) =
      Langlands.LinearAlgebra.orderedCoxeter p.base e := by
  simp only [coxeterNormalizer, map_list_prod, List.map_ofFn, Function.comp_def,
    SimpleReflectionRepresentative.weylAction_normalizerPoint,
    Langlands.LinearAlgebra.orderedCoxeter]

/-- For a semisimple group the supplied ordered normalizer product fixes no nonzero character. -/
theorem weylAction_coxeterNormalizer_eq_self_iff (hG : IsSemisimple G)
    (χ : characterLattice p.torus) :
    weylAction p.inclusion (coxeterNormalizer e n) χ = χ ↔ χ = 0 := by
  have : Module.Finite ℤ (characterLattice p.torus) := p.isSplitTorus.finite_characterLattice
  have hfin : Finite (cocharacterLattice p.torus ⧸ p.rootDatum.corootSpan ℤ) :=
    p.rootDatum.finite_quotient_rootSpan_iff_corootSpan.mp
      (hG.finite_quotient_rootSpan p.isSplitTorus p.isMaximalTorus.2.1 p.isRootDatum)
  rw [weylAction_coxeterNormalizer]
  exact Langlands.LinearAlgebra.orderedCoxeter_eq_self_iff_eq_zero p.base e hfin χ

/-- The actual torus endomorphism `t ↦ N t N⁻¹ t⁻¹` for the ordered normalizer product. -/
def coxeterTorusEnd : p.torus ⟶ p.torus :=
  torusCommutatorEnd p.inclusion (coxeterNormalizer e n)

/-- Its full character pullback is injective for every semisimple split pinning. -/
theorem coxeterTorusEnd_injective_characterPullback (hG : IsSemisimple G) :
    Function.Injective (characterLattice.comapHom
      (CommGroupScheme.groupHom (coxeterTorusEnd e n))) := by
  intro χ ψ h
  have hz : characterLattice.comapHom (CommGroupScheme.groupHom (coxeterTorusEnd e n))
      (χ - ψ) = 0 := by rw [map_sub, h, sub_self]
  have hf := (comap_torusCommutatorEnd_eq_zero_iff p.inclusion
    (coxeterNormalizer e n) (χ - ψ)).mp hz
  exact sub_eq_zero.mp ((weylAction_coxeterNormalizer_eq_self_iff e n hG (χ - ψ)).mp hf)

/-- The actual Coxeter torus commutator is faithfully flat over an arbitrary field. -/
theorem coxeterTorusEnd_flat_and_surjective (hG : IsSemisimple G) :
    Flat (CommGroupScheme.groupHom (coxeterTorusEnd e n)).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom (coxeterTorusEnd e n)).hom.hom.left :=
  p.isSplitTorus.flat_and_surjective_of_injective_characterPullback p.isSplitTorus
    (CommGroupScheme.groupHom (coxeterTorusEnd e n))
    (coxeterTorusEnd_injective_characterPullback e n hG)

end SplitPinning

end Langlands.GroupScheme
