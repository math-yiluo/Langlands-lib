import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.DirectedUnions
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Unitary central characters and nontrivial Jacquet modules along sub and quotient maps

A unitary central character passes to a subrepresentation and to a quotient. A normalized
Jacquet exponent makes its Jacquet module nontrivial. Nontriviality of the normalized Jacquet
module of an actual represented parabolic passes from a subrepresentation or a quotient to
the ambient representation: the Jacquet functor preserves injective maps, because the
radical's point image is a limit of compact subgroups, and it preserves surjective maps.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section CentralCharacter

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- A unitary central character restricts along an injective morphism. -/
def unitaryCentralCharacterOfInjective {A B : SmoothRep.{0, _, v} ℂ Γ}
    (c : UnitaryCentralCharacter B.representation) (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) :
    UnitaryCentralCharacter A.representation where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z x := hf <| by
    rw [(SmoothRep.hom f).isIntertwining, c.acts, map_smul]

/-- A unitary central character descends along a surjective morphism. -/
def unitaryCentralCharacterOfSurjective {A B : SmoothRep.{0, _, v} ℂ Γ}
    (c : UnitaryCentralCharacter A.representation) (f : A ⟶ B)
    (hf : Function.Surjective (SmoothRep.hom f)) :
    UnitaryCentralCharacter B.representation where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z y := by
    obtain ⟨x, rfl⟩ := hf y
    rw [← (SmoothRep.hom f).isIntertwining, c.acts, map_smul]

end CentralCharacter

section Jacquet

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance jacquetNontrivialityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- A normalized Jacquet exponent makes the normalized Jacquet module nontrivial. -/
theorem nontrivial_jacquet_of_isNormalizedJacquetExponent (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj π) := by
  have hne := ((isNormalizedJacquetExponent_iff_isOpen_ker_and p l r hp hl hr hmul ha π χ).mp
    hχ).2
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hne
  refine le_antisymm (fun v _ => ?_) bot_le
  rw [Subsingleton.elim v 0]
  exact Submodule.zero_mem (⊥ : Submodule ℂ _)

/-- The normalized Jacquet module of a subrepresentation embeds in that of the ambient
representation, so its nontriviality passes to the ambient representation. Here `k` is a
nonarchimedean local field, so that the radical's point image is a limit of compact
subgroups. -/
theorem nontrivial_jacquet_of_injective [ValuativeRel k] [IsNonarchimedeanLocalField k]
    {W π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (f : W ⟶ π) (hf : Function.Injective (SmoothRep.hom f))
    [Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj W)] :
    Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj π) :=
  (normalizedJacquetFunctor_map_injective (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr)
    (isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1) f hf).nontrivial

/-- The normalized Jacquet module of a quotient is a quotient of that of the ambient
representation, so its nontriviality passes to the ambient representation. -/
theorem nontrivial_jacquet_of_surjective {W π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (f : π ⟶ W) (hf : Function.Surjective (SmoothRep.hom f))
    [Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj W)] :
    Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj π) := by
  have hsurj : Function.Surjective
      (SmoothRep.hom ((jacquetFunctor p l r hp hr hl hmul).map f)) := by
    intro y
    obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective W.representation
      (pointImage (r ≫ p)) 1 y
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x,
      normalizedJacquetFunctor_map_mk _ _ _ _ f x⟩
  exact hsurj.nontrivial

end Jacquet

end Langlands.Aubert.General.RepresentedParabolic
