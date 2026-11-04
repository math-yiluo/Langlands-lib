import Langlands.GroupScheme.CentralIsogeny.RootDatumHomAssembly
import Langlands.GroupScheme.CentralIsogeny.RootComparison
import Langlands.GroupScheme.CentralIsogeny.WeightDimensionComparison
import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.GroupScheme.CentralIsogeny.RestrictionIsomorphism
import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # Root-datum morphisms from explicit geometric comparisons -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {φ : G ⟶ G'}

/-- Explicit self-centralizer and dimension comparisons give the root bijection
for a central isogeny with isogenous torus restriction. -/
theorem IsCentralIsogeny.roots_bijOn_of_comparisons
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hdim : Lie.dimension G = Lie.dimension G') :
    Set.BijOn (fun χ : characterLattice T' => t ≫ χ) (roots i') (roots i) := by
  have := hT.isAffineHom
  have := hT'.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj := RealTorusSpace.characterRestrict_injective_of_epi t
  have hzero := Lie.finrank_zeroWeight_eq_comp_of_torus_isogeny
    i i' hself hself' hT hT' φ t ht htiso
  have hroots := roots_comp_eq_of_central_kernel_of_dimensions
    φ hφ.isCentral_kernelι i hT hdim hzero
  exact roots_bijOn_of_comp_eq hT hT' t i i' φ ht hinj hroots

variable {J : Type v} {J' : Type w}
  (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))

/-- The actual morphism on supplied root data, retaining the geometric
self-centralizer, ambient dimension, torus-isogeny and full Weyl finiteness inputs. -/
def IsCentralIsogeny.rootDatumHomOfComparisons
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hdim : Lie.dimension G = Lie.dimension G')
    (hweyl : haveI : IsClosedImmersion i'.hom.hom.left := hi'
      Finite (weylImage i'))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    RootPairing.Hom P' P := by
  have hroot := hφ.roots_bijOn_of_comparisons hT hT' hi hi' t ht htiso hself hself' hdim
  rw [← hP.2.1, ← hP'.2.1] at hroot
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have : Epi (CommGroupScheme.groupHom t).hom.hom := Over.epi_of_epi_left _
  have : Epi (CommGroupScheme.groupHom t) :=
    (Grp.forget (Over (Spec (CommRingCat.of k)))).epi_of_epi_map
      (inferInstanceAs (Epi (CommGroupScheme.groupHom t).hom.hom))
  have : Finite (weylImage i') := hweyl
  exact RootDatumHom.ofRootCoroot P P' t hP.1 hP'.1 hroot
    (fun _ _ h => hP.coroot_comp_of_finite_weylImage i i' φ t ht hP' hT h)

/-- With a maximal source torus, the conditional construction satisfies every
map, injectivity and isomorphism clause of the central-isogeny root-datum target. -/
theorem IsCentralIsogeny.rootDatumHomOfComparisons_spec
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hdim : Lie.dimension G = Lie.dimension G')
    (hweyl : haveI : IsClosedImmersion i'.hom.hom.left := hi'
      Finite (weylImage i'))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    let f := hφ.rootDatumHomOfComparisons P P' hT hT' hi.2.1 hi' t ht htiso
      hself hself' hdim hweyl hP hP'
    (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
    (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) ∧
    Function.Injective f.weightMap ∧ Function.Injective f.coweightMap ∧
    (IsIso φ ↔ Function.Bijective f.weightMap) := by
  dsimp only
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · exact RealTorusSpace.characterRestrict_injective_of_epi t
  · exact hφ.cocharacterMapInt_injective_of_square hi.2.1 hi' t ht
  · exact (hφ.isIso_iff_torusRestriction_of_selfCentralizing
      hi hT'.isTorus hi' t ht hself).trans
      (hT.isIso_iff_bijective_characterPullback hT' t)

end Langlands.GroupScheme
