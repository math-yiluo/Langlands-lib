import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionHelpers

/-! # Additive Hom vanishing for multiplicative-type extensions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Multiplicative-type groups have no nonzero homomorphism to the additive group. -/
theorem IsMultiplicativeType.hom_vector_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G)
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) : f = 0 := by
  obtain ⟨L, hL, aL, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let v := VectorGroup.baseChangeIso (n := 1) (CommRingCat.ofHom (algebraMap k L))
  have hz := Diagonalizable.hom_vector_eq_zero Λ
    (e.inv ≫ (GroupScheme.baseChange b).map f ≫ v.hom)
  have hf : (GroupScheme.baseChange b).map f = 0 := by
    apply (cancel_mono v.hom).mp
    apply (cancel_epi e.inv).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hz
  obtain ⟨hs, hfl, hqc⟩ := fieldExtension_fpqc k L
  let := hs
  let := hfl
  let := hqc
  apply (GroupScheme.baseChange b).map_injective
  rw [hf]
  apply Grp.hom_ext
  exact ((Over.pullback b).map_one (X := G.X)
    (M := (VectorGroup.groupScheme (CommRingCat.of k) 1).X)).symm

/-- The zero homomorphism is the unique additive-group-valued homomorphism. -/
@[instance_reducible]
def IsMultiplicativeType.additiveHomUnique
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G) :
    Unique (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) where
  default := 0
  uniq := hG.hom_vector_eq_zero

namespace RelativeRoot.IsFppfQuotient

variable {H G K : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) [Mono i.hom.hom] {p : G ⟶ K}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)

include i hq

/-- The middle group of a multiplicative-type extension is affine and finite type. -/
theorem affine_finiteType_of_multiplicativeType (hH : IsMultiplicativeType H)
    (hK : IsMultiplicativeType K) :
    IsAffineHom G.X.hom ∧ LocallyOfFiniteType G.X.hom := by
  let := hH.isAffineHom
  let := hK.isAffineHom
  let := hK.locallyOfFiniteType
  exact hq.affine_finiteType_source i

/-- Extensions of multiplicative-type groups have only the zero map to the additive group. -/
theorem hom_vector_eq_zero_of_multiplicativeType (hH : IsMultiplicativeType H)
    (hK : IsMultiplicativeType K)
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) : f = 0 := by
  let := hH.isAffineHom
  let := hq.isAffineHom_of_kernel i
  let := hH.additiveHomUnique
  let := hK.additiveHomUnique
  exact hq.hom_eq_zero_of_kernel_quotient i f

end RelativeRoot.IsFppfQuotient

end Langlands.GroupScheme
