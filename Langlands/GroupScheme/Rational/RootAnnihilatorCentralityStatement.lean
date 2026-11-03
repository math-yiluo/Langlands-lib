import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Lie.SubgroupEqualityStatement

/-! # Root annihilation and central cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- An integral cocharacter annihilating every actual relative root is central.
The group is smooth, connected and affine; reductivity and maximality of the
split torus are unnecessary for this criterion. -/
def RootAnnihilatorCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (_ : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    (∀ α ∈ relativeRoots i, latticePairing T α ν = 0) →
      IsCentral (CommGroupScheme.groupHom ν ≫ i)

section ZeroWeight

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Vanishing of every relative-root pairing puts every actual Lie vector in
the zero weight space of the cocharacter. -/
theorem weightSpace_zero_eq_top_of_annihilates_relativeRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (hν : ∀ α ∈ relativeRoots i, latticePairing T α ν = 0) :
    weightSpace (CommGroupScheme.groupHom ν ≫ i) 0 = ⊤ := by
  classical
  apply top_unique
  rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top]
  refine iSup_le fun α => ?_
  by_cases hbot : weightSpace i α = ⊥
  · rw [hbot]
    exact bot_le
  have hcomp : ν ≫ α = 0 := by
    apply (gmEndEquiv k).injective
    by_cases hα : α = 0
    · simp [hα]
    · simpa only [latticePairing_apply, map_zero] using hν α ⟨hα, hbot⟩
  simpa only [hcomp] using weightSpace_le_comp ν i α

end ZeroWeight

section Centrality

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- A full all-refinement centralizer is equivalent to centrality of the
actual commutative-group-scheme map. -/
theorem isCentral_iff_torusCentralizer_eq_top (i : T.toGrp ⟶ G) :
    IsCentral i ↔ torusCentralizer i = ⊤ := by
  constructor
  · intro hi
    apply SubgroupFunctor.ext
    intro U
    apply top_unique
    intro g _ V a t
    exact (commute_of_mem_center (hi V t) (a ≫ g)).symm
  · intro hi U t V a g
    have hg : g ∈ (torusCentralizer i).carrier V := by
      rw [hi]
      exact Subgroup.mem_top _
    have hc := hg V (𝟙 V) (a ≫ t)
    simpa only [Category.id_comp, Category.assoc] using hc.symm

/-- A full dynamic centralizer says precisely that the cocharacter is central
on every test scheme. -/
theorem isCentral_iff_dynamicCentralizer_eq_top
    (χ : (Gm S).toGrp ⟶ G) :
    IsCentral χ ↔ Dynamic.centralizer χ = ⊤ := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer]
  exact isCentral_iff_torusCentralizer_eq_top χ

end Centrality

end Langlands.GroupScheme
