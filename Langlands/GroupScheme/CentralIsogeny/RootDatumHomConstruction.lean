import Langlands.GroupScheme.CentralIsogeny.NonzeroWeightEquivalence
import Langlands.GroupScheme.CentralIsogeny.RootDatumReduction
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Actual root-datum morphisms for central isogenies -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Construction

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {φ : G ⟶ G'}

/-- The actual root pullback is a bijection for a central isogeny and an
isogenous restriction of split tori. -/
theorem IsCentralIsogeny.roots_bijOn_of_torusRestriction
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t)) :
    Set.BijOn (fun χ : characterLattice T' => t ≫ χ) (roots i') (roots i) := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  exact roots_bijOn_of_comp_eq hT hT' t i i' φ ht
    (RealTorusSpace.characterRestrict_injective_of_epi t)
    (roots_comp_eq_of_centralIsogeny φ hφ i hT)

variable {J : Type v} {J' : Type w}
  (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))

/-- Actual character pullback and cocharacter pushforward form a morphism of
any supplied actual root data, with no self-centralizer or dimension premise. -/
def IsCentralIsogeny.rootDatumHomOfCentralIsogeny
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    RootPairing.Hom P' P := by
  have hroot := hφ.roots_bijOn_of_torusRestriction hT hT' t ht htiso
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
  have : Finite (weylImage i') := splitTorusWeylImageFinite k G' T' hT' i' hi'
  exact RootDatumHom.ofRootCoroot P P' t hP.1 hP'.1 hroot
    (fun _ _ h => hP.coroot_comp_of_finite_weylImage i i' φ t ht hP' hT h)

/-- The constructed maps are the actual lattice maps, and both are injective. -/
theorem IsCentralIsogeny.rootDatumHomOfCentralIsogeny_spec
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    let f := hφ.rootDatumHomOfCentralIsogeny P P' hT hT' hi' t ht htiso hP hP'
    (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
    (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) ∧
    Function.Injective f.weightMap ∧ Function.Injective f.coweightMap := by
  dsimp only
  have : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := htiso.1
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  exact ⟨fun _ => rfl, fun _ => rfl,
    RealTorusSpace.characterRestrict_injective_of_epi t,
    cocharacterMapInt_injective_of_isFinite t⟩

/-- Under the full-kernel containment, the constructed weight map detects
whether the original central isogeny is invertible. -/
theorem IsCentralIsogeny.rootDatumHomOfCentralIsogeny_isIso_iff
    (hφ : IsCentralIsogeny φ)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (hker : SubgroupFunctor.range (kernelι φ) ≤ SubgroupFunctor.range i)
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    let f := hφ.rootDatumHomOfCentralIsogeny P P' hT hT' hi' t ht htiso hP hP'
    IsIso φ ↔ Function.Bijective f.weightMap := by
  dsimp only
  change IsIso φ ↔ Function.Bijective (fun χ : characterLattice T' => t ≫ χ)
  rw [← hT.isIso_iff_bijective_characterPullback hT' t]
  constructor
  · intro h
    exact hi.isIso_factor_of_isIso hT'.isTorus hi' φ t ht
  · intro h
    have : IsIso t := h
    have : IsIso (CommGroupScheme.groupHom t) := by
      refine ⟨⟨CommGroupScheme.groupHom (inv t), ?_, ?_⟩⟩
      · exact congrArg CommGroupScheme.groupHom (IsIso.hom_inv_id t)
      · exact congrArg CommGroupScheme.groupHom (IsIso.inv_hom_id t)
    have : IsClosedImmersion i'.hom.hom.left := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    exact hφ.isIsogeny.isIso_of_kernel_range_le_of_restriction ht hker

end Construction

/-- The full published target is reduced to containment of each full central
kernel in the supplied source maximal torus. This premise is not proved here. -/
theorem centralIsogenyRootDatumHom_of_kernel_containment
    (hker : ∀ (k : Type u) [Field k]
      (G G' : GroupScheme (Spec (CommRingCat.of k)))
      (_hG : IsConnectedReductive G) (_hG' : IsConnectedReductive G')
      (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus i →
      ∀ (φ : G ⟶ G'), IsCentralIsogeny φ →
        SubgroupFunctor.range (kernelι φ) ≤ SubgroupFunctor.range i) :
    CentralIsogenyRootDatumHomStatement.{u} := by
  intro k _ G G' hG hG' T T' hT hT' i i' hi hi' φ t hφ ht J J' P P' hP hP'
  have := hG.isAffineHom
  have := hG'.isAffineHom
  have := hG.smooth
  have := hG'.smooth
  have htiso := hφ.isIsogeny_torusRestriction hG hG' hT hT' hi hi' t ht
  let f := hφ.rootDatumHomOfCentralIsogeny P P' hT hT' hi'.2.1 t ht htiso hP hP'
  obtain ⟨hw, hcw, hinj, hcinj⟩ :=
    hφ.rootDatumHomOfCentralIsogeny_spec P P' hT hT' hi'.2.1 t ht htiso hP hP'
  exact ⟨f, hw, hcw, hinj, hcinj,
    hφ.rootDatumHomOfCentralIsogeny_isIso_iff P P' hT hT' hi hi'.2.1 t ht htiso
      (hker k G G' hG hG' T i hT hi φ hφ) hP hP'⟩

end Langlands.GroupScheme
