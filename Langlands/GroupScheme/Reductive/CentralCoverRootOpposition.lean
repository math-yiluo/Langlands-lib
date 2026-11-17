import Langlands.GroupScheme.Reductive.RankOneCentralCoverRoots
import Langlands.GroupScheme.CentralIsogeny.NonzeroWeightEquivalence
import Langlands.GroupScheme.CentralIsogeny.RootComparison

/-! # Actual root opposition from a supplied rank-one central cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section SourceGeometry

variable {S : Scheme.{u}} {G H : GroupScheme S} {f : G ⟶ H}

/-- Finiteness of a central isogeny preserves affineness over the base. -/
theorem IsCentralIsogeny.isAffineHom_source [IsAffineHom H.X.hom]
    (hf : IsCentralIsogeny f) : IsAffineHom G.X.hom := by
  have : IsFinite f.hom.hom.left := hf.isFinite
  rw [← Over.w f.hom.hom]
  infer_instance

/-- Finiteness of a central isogeny preserves local finite type over the base. -/
theorem IsCentralIsogeny.locallyOfFiniteType_source [LocallyOfFiniteType H.X.hom]
    (hf : IsCentralIsogeny f) : LocallyOfFiniteType G.X.hom := by
  have : IsFinite f.hom.hom.left := hf.isFinite
  rw [← Over.w f.hom.hom]
  infer_instance

end SourceGeometry

section RootPullback

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {T U : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual torus-compatible central isogeny identifies the two actual root sets. -/
def IsCentralIsogeny.rootPullbackEquiv
    {f : G ⟶ H} (hf : IsCentralIsogeny f)
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp)
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) (t : T ⟶ U)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsq : i ≫ f = CommGroupScheme.groupHom t ≫ j) :
    {χ : characterLattice U // χ ∈ roots j} ≃
      {ψ : characterLattice T // ψ ∈ roots i} := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  exact Set.BijOn.equiv _ (roots_bijOn_of_comp_eq hT hU t i j f hsq
    (RealTorusSpace.characterRestrict_injective_of_epi t)
    (roots_comp_eq_of_centralIsogeny f hf i hT))

/-- Equality or opposition of source roots descends through a torus-compatible
central isogeny. -/
theorem IsCentralIsogeny.eq_or_eq_neg_of_source
    {f : G ⟶ H} (hf : IsCentralIsogeny f)
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp)
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) (t : T ⟶ U)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsq : i ≫ f = CommGroupScheme.groupHom t ≫ j)
    (hopp : ∀ α ∈ roots i, ∀ β ∈ roots i, α = β ∨ α = -β)
    {α β : characterLattice U} (hα : α ∈ roots j) (hβ : β ∈ roots j) :
    α = β ∨ α = -β := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj : Function.Injective (fun χ : characterLattice U => t ≫ χ) :=
    RealTorusSpace.characterRestrict_injective_of_epi t
  have hroots := roots_bijOn_of_comp_eq hT hU t i j f hsq hinj
    (roots_comp_eq_of_centralIsogeny f hf i hT)
  rcases hopp _ (hroots.mapsTo hα) _ (hroots.mapsTo hβ) with h | h
  · exact Or.inl (hinj h)
  · apply Or.inr
    apply hinj
    simpa only [Preadditive.comp_neg] using h

end RootPullback

section Opposition

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "D" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))
local notation "SL" => SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)
local notation "d" => SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)

/-- A supplied standard rank-one central cover forces equality or opposition of roots.
Finite morphisms supply the affine and finite-type geometry of the source product. -/
theorem eq_or_eq_neg_of_sl2_centralCover
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (C : CommGroupScheme (Spec (CommRingCat.of k))) (hC : IsSplitTorus C.toGrp)
    (f : SL ⊗ C.toGrp ⟶ G) (hf : IsCentralIsogeny f)
    (t : CommGroupScheme.prod D C ⟶ T)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsq : (d ⊗ₘ 𝟙 C.toGrp) ≫ f = CommGroupScheme.groupHom t ≫ i)
    {α β : characterLattice T} (hα : α ∈ roots i) (hβ : β ∈ roots i) :
    α = β ∨ α = -β := by
  have : IsAffineHom (SL ⊗ C.toGrp).X.hom := hf.isAffineHom_source
  have : LocallyOfFiniteType (SL ⊗ C.toGrp).X.hom := hf.locallyOfFiniteType_source
  have hD : IsSplitTorus (D).toGrp := isSplitTorus_splitTorus _
  exact hf.eq_or_eq_neg_of_source (T := CommGroupScheme.prod D C) (U := T)
    (hD.tensor hC) hT (d ⊗ₘ 𝟙 C.toGrp) i t ht hsq
    (fun _ ha _ hb => eq_or_eq_neg_of_mem_roots_sl2_tensor C hC ha hb) hα hβ

end Opposition

end Langlands.GroupScheme
