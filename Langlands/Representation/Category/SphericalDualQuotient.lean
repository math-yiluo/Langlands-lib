import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Contragredient.FixedExtension
import Langlands.Representation.Classification.ConstituentRelations

/-! Actual spherical quotients obtained by dualizing embeddings. -/

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compact-open fixed vectors in a smooth representation give nonzero fixed
vectors in its actual smooth contragredient. -/
theorem fixedVectors_smoothContragredient_ne_bot
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (h : fixedVectors ρ K.toSubgroup ≠ ⊥) :
    fixedVectors (smoothContragredient ρ) K.toSubgroup ≠ ⊥ := by
  have : Nontrivial (fixedVectors ρ K.toSubgroup) :=
    Submodule.nontrivial_iff_ne_bot.mpr h
  let e := smoothDualCompactFixedEquiv ρ hρ K hK
  have : Nontrivial (fixedVectors (smoothContragredient ρ) K.toSubgroup) :=
    e.toEquiv.nontrivial
  exact Submodule.nontrivial_iff_ne_bot.mp inferInstance

namespace SmoothRep

/-- Dualize an actual embedding into the dual of `A`, then precompose with
canonical evaluation of `A` into its smooth bidual. -/
def dualQuotientMap
    (A B : SmoothRep.{0,uG,uV} ℂ G)
    (j : B.representation.IntertwiningMap (smoothContragredient A.representation)) :
    A.representation.IntertwiningMap (smoothContragredient B.representation) :=
  (contragredientMap j).comp (smoothBidual A.isSmooth)

theorem dualQuotientMap_surjective
    (hG : CompactOpenCofinal G) (A B : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.IsAdmissible)
    (j : B.representation.IntertwiningMap (smoothContragredient A.representation))
    (hj : Function.Injective j) : Function.Surjective (dualQuotientMap A B j) := by
  exact (contragredientMap_surjective_of_injective_of_compact_cofinal hG B.isSmooth
    (isSmooth_smoothContragredient A.representation) j hj).comp
      (smoothBidual_surjective_of_compact_cofinal hG A.representation hA)

/-- A chosen actual surjective intertwiner onto the irreducible spherical dual
of an admissible spherical object embedded in the dual of `A`. -/
def sphericalDualQuotient
    (hG : CompactOpenCofinal G) (A B : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible) (hBi : B.IsIrreducible)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hBK : fixedVectors B.representation K.toSubgroup ≠ ⊥)
    (j : B.representation.IntertwiningMap (smoothContragredient A.representation))
    (hj : Function.Injective j) :
    {q : A.representation.IntertwiningMap (smoothContragredient B.representation) //
      Function.Surjective q ∧
      Representation.IsIrreducible (smoothContragredient B.representation) ∧
      fixedVectors (smoothContragredient B.representation) K.toSubgroup ≠ ⊥} :=
  ⟨dualQuotientMap A B j, dualQuotientMap_surjective hG A B hA j hj,
    (isIrreducible_contragredient_iff hG B hB).mpr hBi,
    fixedVectors_smoothContragredient_ne_bot B.representation B.isSmooth K hK hBK⟩

theorem isIrreducibleSphericalQuotient_of_dual_embedding
    (hG : CompactOpenCofinal G) (A B : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible) (hBi : B.IsIrreducible)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hBK : fixedVectors B.representation K.toSubgroup ≠ ⊥)
    (j : B.representation.IntertwiningMap (smoothContragredient A.representation))
    (hj : Function.Injective j) :
    Classification.IsIrreducibleQuotient A.representation
      (smoothContragredient B.representation) ∧
      fixedVectors (smoothContragredient B.representation) K.toSubgroup ≠ ⊥ := by
  let q := sphericalDualQuotient hG A B hA hB hBi K hK hBK j hj
  exact ⟨⟨q.property.2.1, q.val, q.property.1⟩, q.property.2.2⟩

end SmoothRep
end Langlands
