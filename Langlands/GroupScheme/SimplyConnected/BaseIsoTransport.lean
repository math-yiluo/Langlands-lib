import Langlands.GroupScheme.SimplyConnected.CoverComparison
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Descent.Data

/-! # Simply connected covers under isomorphisms of base fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]

/-- Connected reductivity transports along a bijective map of base fields. -/
theorem IsConnectedReductive.baseChange_of_bijective
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (φ : k →+* K) (hφ : Function.Bijective φ) :
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) := by
  let E := IsAlgClosure.equivOfEquiv (AlgebraicClosure k) (AlgebraicClosure K)
    (RingEquiv.ofBijective φ hφ)
  let c := Spec.map (CommRingCat.ofHom E.toRingHom)
  let b := Spec.map (CommRingCat.ofHom φ)
  have hcomm : toAlgebraicClosure K ≫ b = c ≫ toAlgebraicClosure k := by
    dsimp only [toAlgebraicClosure, b, c]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun θ : k →+* AlgebraicClosure K =>
      Spec.map (CommRingCat.ofHom θ))
      (IsAlgClosure.equivOfEquiv_comp_algebraMap (AlgebraicClosure k)
        (AlgebraicClosure K) (RingEquiv.ofBijective φ hφ)).symm
  let e :=
    Descent.pullbackComparison b (toAlgebraicClosure K)
        (toAlgebraicClosure K ≫ b) rfl G ≪≫
      (Descent.pullbackComparison (toAlgebraicClosure k) c
        (toAlgebraicClosure K ≫ b) hcomm.symm G).symm
  have : IsIso b := isIso_SpecMap_iff.mpr hφ
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  refine ⟨inferInstanceAs (Smooth (pullback.snd G.X.hom b)),
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b)),
    connectedSpace_baseChange_of_isIso b G, ?_⟩
  exact (HasTrivialUnipotentRadical.baseChange_of_bijective E.toRingHom E.bijective
    hG.hasTrivialGeometricUnipotentRadical).of_iso e

/-- Connected reductivity transports along an isomorphism of field spectra. -/
theorem IsConnectedReductive.baseChange_of_isIso
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsConnectedReductive ((GroupScheme.baseChange b).obj G) := by
  have hφ : Function.Bijective (Spec.preimage b).hom := by
    apply isIso_SpecMap_iff.mp
    simpa only [Spec.map_preimage] using (inferInstance : IsIso b)
  simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using
    hG.baseChange_of_bijective (Spec.preimage b).hom hφ

/-- Semisimplicity transports along an isomorphism of base fields. -/
theorem IsSemisimple.baseChange_of_isIso
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsSemisimple ((GroupScheme.baseChange b).obj G) :=
  ⟨hG.isConnectedReductive.baseChange_of_isIso b, hG.hasFiniteCenter.baseChange b⟩

/-- Algebraic simple connectedness transports along an isomorphism of base fields. -/
theorem IsSimplyConnected.baseChange_of_isIso
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsSimplyConnected ((GroupScheme.baseChange b).obj G) := by
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  refine ⟨hG.isSemisimple.baseChange_of_isIso b, ?_⟩
  intro H q hH hq
  have : IsIso (R.map q ≫ (e.app G).hom) :=
    hG.central_isogeny_isIso (R.obj H) _
      (hH.baseChange_of_isIso (inv b)) ((hq.baseChange (inv b)).comp_iso (e.app G))
  have : IsIso (R.map q) := IsIso.of_isIso_comp_right (R.map q) (e.app G).hom
  exact isIso_of_baseChange (inv b) q

/-- The explicit central-cover universal property transports along a base-field isomorphism. -/
theorem HasCentralCoverUniversalProperty.baseChange_of_isIso
    {C G : GroupScheme (Spec (CommRingCat.of k))} {π : C ⟶ G}
    (hπ : HasCentralCoverUniversalProperty π)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    HasCentralCoverUniversalProperty ((GroupScheme.baseChange b).map π) := by
  let F := GroupScheme.baseChange b
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  let d := baseChangeSectionNatIso (inv b) b (IsIso.hom_inv_id b)
  let E := CategoryTheory.Equivalence.mk F R e.symm d
  let ff : R.FullyFaithful := E.fullyFaithfulInverse
  intro H q hH hq
  let q₀ := R.map q ≫ (e.app G).hom
  obtain ⟨a₀, ha₀, hu₀⟩ := hπ (R.obj H) q₀
    (hH.baseChange_of_isIso (inv b)) ((hq.baseChange (inv b)).comp_iso (e.app G))
  let a : F.obj C ⟶ H := ff.preimage ((e.app C).hom ≫ a₀)
  have hRa : R.map a = (e.app C).hom ≫ a₀ := ff.map_preimage _
  have hnat : R.map (F.map π) ≫ (e.app G).hom = (e.app C).hom ≫ π :=
    e.hom.naturality π
  have back (t : F.obj C ⟶ H) (ht : t ≫ q = F.map π) :
      ((e.app C).inv ≫ R.map t) ≫ q₀ = π := by
    dsimp only [q₀]
    rw [Category.assoc, ← Category.assoc (R.map t), ← R.map_comp, ht,
      hnat, Iso.inv_hom_id_assoc]
  refine ⟨a, ?_, ?_⟩
  · apply ff.map_injective
    apply (cancel_mono (e.app G).hom).mp
    rw [R.map_comp, hRa]
    simp only [Category.assoc]
    change (e.app C).hom ≫ (a₀ ≫ q₀) = _
    rw [ha₀, hnat]
  · intro t ht
    apply ff.map_injective
    apply (cancel_epi (e.app C).inv).mp
    rw [hRa, Iso.inv_hom_id_assoc]
    exact hu₀ _ (back t ht)

/-- The full supplied cover transports along an isomorphism of base fields. -/
theorem IsSimplyConnectedCover.baseChange_of_isIso
    {C G : GroupScheme (Spec (CommRingCat.of k))} {π : C ⟶ G}
    (hπ : IsSimplyConnectedCover π)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsSimplyConnectedCover ((GroupScheme.baseChange b).map π) :=
  ⟨hπ.isSemisimple.baseChange_of_isIso b, hπ.isSimplyConnected.baseChange_of_isIso b,
    hπ.isCentralIsogeny.baseChange b, hπ.universal.baseChange_of_isIso b⟩

namespace IsSimplyConnectedCover

variable {C G : GroupScheme (Spec (CommRingCat.of k))}
variable {C' G' : GroupScheme (Spec (CommRingCat.of K))}
variable {π : C ⟶ G} {π' : C' ⟶ G'}

/-- Compare supplied covers across a base-field isomorphism and a target isomorphism. -/
def isoOverBaseIso (hπ : IsSimplyConnectedCover π) (hπ' : IsSimplyConnectedCover π')
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b]
    (e : (GroupScheme.baseChange b).obj G ≅ G') :
    (GroupScheme.baseChange b).obj C ≅ C' :=
  (hπ.baseChange_of_isIso b).isoOver hπ' e

/-- The comparison has the specified lifting equation after the actual pullback. -/
@[reassoc]
theorem isoOverBaseIso_hom_comp
    (hπ : IsSimplyConnectedCover π) (hπ' : IsSimplyConnectedCover π')
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b]
    (e : (GroupScheme.baseChange b).obj G ≅ G') :
    (hπ.isoOverBaseIso hπ' b e).hom ≫ π' =
      (GroupScheme.baseChange b).map π ≫ e.hom :=
  (hπ.baseChange_of_isIso b).isoOver_hom_comp hπ' e

/-- Every homomorphism with that equation is the canonical comparison. -/
theorem hom_eq_isoOverBaseIso
    (hπ : IsSimplyConnectedCover π) (hπ' : IsSimplyConnectedCover π')
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b]
    (e : (GroupScheme.baseChange b).obj G ≅ G')
    (a : (GroupScheme.baseChange b).obj C ⟶ C')
    (ha : a ≫ π' = (GroupScheme.baseChange b).map π ≫ e.hom) :
    a = (hπ.isoOverBaseIso hπ' b e).hom :=
  (hπ.baseChange_of_isIso b).hom_eq_isoOver hπ' e a ha

/-- Lifts across the two specified isomorphisms are unique among all homomorphisms. -/
theorem existsUnique_lift_over_baseIso
    (hπ : IsSimplyConnectedCover π) (hπ' : IsSimplyConnectedCover π')
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b]
    (e : (GroupScheme.baseChange b).obj G ≅ G') :
    ∃! a : (GroupScheme.baseChange b).obj C ⟶ C',
      a ≫ π' = (GroupScheme.baseChange b).map π ≫ e.hom :=
  (hπ.baseChange_of_isIso b).existsUnique_lift_iso hπ' e

end IsSimplyConnectedCover

end Langlands.GroupScheme
