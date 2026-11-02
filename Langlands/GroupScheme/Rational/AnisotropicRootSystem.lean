import Langlands.GroupScheme.Rational.Statement

/-! # The actual relative root system for anisotropic groups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace RelativeRootSystem

/-- The empty root pairing on a zero vector space, with its actual evaluation pairing. -/
def emptyPairing (J : Type u) [IsEmpty J] (V : Type v) [AddCommGroup V] [Module ℚ V]
    [Subsingleton V] : RootPairing J ℚ V (Module.Dual ℚ V) where
  toLinearMap := Module.Dual.eval ℚ V
  isPerfPair_toLinearMap :=
    { bijective_left := Function.bijective_of_subsingleton' _
      bijective_right := Function.bijective_of_subsingleton' _ }
  root := ⟨isEmptyElim, fun i => isEmptyElim i⟩
  coroot := ⟨isEmptyElim, fun i => isEmptyElim i⟩
  root_coroot_two i := isEmptyElim i
  reflectionPerm i := isEmptyElim i
  reflectionPerm_root i := isEmptyElim i
  reflectionPerm_coroot i := isEmptyElim i

instance (J : Type u) [IsEmpty J] (V : Type v) [AddCommGroup V] [Module ℚ V]
    [Subsingleton V] : (emptyPairing J V).IsRootSystem where
  span_root_eq_top := Subsingleton.elim _ _
  span_coroot_eq_top := Subsingleton.elim _ _

instance (J : Type u) [IsEmpty J] (V : Type v) [AddCommGroup V] [Module ℚ V]
    [Subsingleton V] : (emptyPairing J V).IsCrystallographic where
  exists_value i := isEmptyElim i

end RelativeRootSystem

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual rational root span is zero when the relative root set is empty. -/
theorem relativeRootSpan_eq_bot_of_relativeRoots_eq_empty [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} (hroots : relativeRoots i = ∅) : relativeRootSpan i = ⊥ := by
  simp [relativeRootSpan, ratSpan, hroots]

/-- With empty roots and trivial actual Weyl quotient, all clauses of the published
relative-root-system proposition hold. -/
theorem hasRelativeRootSystem_of_empty [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (hroots : relativeRoots i = ∅)
    [Subsingleton (relativeWeylGroup i)] : HasRelativeRootSystem i := by
  have : Subsingleton (relativeRootSpan i) :=
    Submodule.subsingleton_iff_eq_bot.mpr (relativeRootSpan_eq_bot_of_relativeRoots_eq_empty hroots)
  let P := RelativeRootSystem.emptyPairing PEmpty.{u + 1} (relativeRootSpan i)
  refine ⟨PEmpty.{u + 1}, inferInstance, P, inferInstance, inferInstance, rfl, ?_, ?_, ?_⟩
  · rw [hroots, Set.image_empty, Set.range_eq_empty P.root, Set.image_empty]
  · exact Subsingleton.elim _ _
  · exact Function.injective_of_subsingleton _

/-- Every point centralizes a split subtorus of an anisotropic group. -/
theorem IsAnisotropic.centralizerPoints_eq_top (hG : IsAnisotropic G)
    {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) : centralizerPoints i = ⊤ := by
  have := hG.subsingleton_hom_of_isSplitSubtorus hi G
  apply top_unique
  intro n _
  rw [mem_centralizerPoints]
  exact Subsingleton.elim _ _

/-- The actual normalizer modulo centralizer quotient is trivial for an anisotropic group. -/
theorem IsAnisotropic.subsingleton_relativeWeylGroup (hG : IsAnisotropic G)
    {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) : Subsingleton (relativeWeylGroup i) := by
  change Subsingleton (normalizerPoints i ⧸ (centralizerPoints i).subgroupOf (normalizerPoints i))
  rw [hG.centralizerPoints_eq_top hi, Subgroup.top_subgroupOf]
  exact QuotientGroup.subsingleton_quotient_top

/-- An anisotropic group's split subtorus has the actual empty relative root system,
including the faithful action of the actual trivial Weyl quotient. -/
theorem IsAnisotropic.hasRelativeRootSystem [IsAffineHom G.X.hom] (hG : IsAnisotropic G)
    {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) :
    haveI := hi.mono
    HasRelativeRootSystem i := by
  have := hi.mono
  have := hG.subsingleton_relativeWeylGroup hi
  exact hasRelativeRootSystem_of_empty i (hG.relativeRoots_eq_empty hi)

end Langlands.GroupScheme
