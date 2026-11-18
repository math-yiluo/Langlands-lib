import Langlands.GroupScheme.Reductive.StarActionScalarExtension
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.Rational.DominantHighestWeight

/-! # Pinned isomorphisms of Galois pinning data and highest-weight representations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitPinning

variable {F : Type u} [Field F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {p : SplitPinning G} {q : SplitPinning H}

section WeightSpaces

variable (E : G ≅ H) (τ : p.torus ≅ q.torus)
  (hsq : p.inclusion ≫ E.hom = CommGroupScheme.groupHom τ.hom ≫ q.inclusion)
  {n : Type} [Fintype n] [DecidableEq n]

include hsq in
/-- Weight spaces correspond under restriction along a group isomorphism that carries the split
torus of `p` to that of `q`. -/
theorem representationWeightSpace_restrict_iso (ρ : MatrixRepresentation H n)
    (μ : characterLattice q.torus) :
    p.representationWeightSpace (ρ.restrict E.hom) ((characterLattice.congr τ).symm μ) =
      q.representationWeightSpace ρ μ := by
  let := p.isSplitTorus.isAffineHom
  let := q.isSplitTorus.isAffineHom
  let t : q.torus.toGrp ≅ p.torus.toGrp :=
    { hom := CommGroupScheme.groupHom τ.inv
      inv := CommGroupScheme.groupHom τ.hom
      hom_inv_id := congrArg Additive.toMul τ.inv_hom_id
      inv_hom_id := congrArg Additive.toMul τ.hom_inv_id }
  unfold representationWeightSpace
  rw [MatrixRepresentation.restrict_comp, hsq, ← MatrixRepresentation.restrict_comp]
  refine (MatrixRepresentation.characterSpace_restrict_iso (ρ.restrict q.inclusion) t
    ((rationalCharacters.equivCharacterLattice p.torus).symm
      ((characterLattice.congr τ).symm μ))).trans ?_
  congr 1
  change Additive.ofMul (CommGroupScheme.groupHom (τ.inv ≫ τ.hom ≫ μ)) = μ
  rw [Iso.inv_hom_id_assoc]
  rfl

end WeightSpaces

section RootDatumEquiv

variable (e : RootPairing.Equiv p.rootDatum q.rootDatum)
  (hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)

include hb in
/-- A base-preserving equivalence of root data maps the monoid of nonnegative integral
combinations of simple roots onto the corresponding monoid. -/
theorem map_positiveRootMonoid :
    p.positiveRootMonoid.map e.weightEquiv.toLinearMap.toAddMonoidHom = q.positiveRootMonoid := by
  rw [positiveRootMonoid, positiveRootMonoid, AddMonoidHom.map_mclosure]
  congr 1
  ext χ
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨⟨e.indexEquiv a, (hb a).mp a.2⟩,
      (RootPairing.Hom.root_weightMap_apply _ _ a.1 e.toHom).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨p.rootDatum.root (e.indexEquiv.symm b),
      ⟨⟨e.indexEquiv.symm b, (hb _).mpr (by simp)⟩, rfl⟩, ?_⟩
    change e.toHom.weightMap (p.rootDatum.root (e.indexEquiv.symm b)) = q.rootDatum.root b
    rw [RootPairing.Hom.root_weightMap_apply _ _ _ e.toHom, Equiv.apply_symm_apply]

include hb in
theorem weightMap_mem_positiveRootMonoid_iff (χ : characterLattice p.torus) :
    e.weightMap χ ∈ q.positiveRootMonoid ↔ χ ∈ p.positiveRootMonoid := by
  rw [← map_positiveRootMonoid e hb]
  exact AddSubmonoid.mem_map_iff_mem e.weightEquiv.injective

include hb in
/-- A base-preserving equivalence of root data preserves dominance. -/
theorem isDominantWeight_weightMap_iff (χ : characterLattice p.torus) :
    q.IsDominantWeight (e.weightMap χ) ↔ p.IsDominantWeight χ := by
  have hpair : ∀ a, q.rootDatum.toLinearMap (e.weightMap χ)
      (q.rootDatum.coroot (e.indexEquiv a)) =
        p.rootDatum.toLinearMap χ (p.rootDatum.coroot a) := by
    intro a
    have h := e.toLinearMap_weightEquiv χ (q.rootDatum.coroot (e.indexEquiv a))
    rw [RootPairing.Equiv.coweightEquiv_apply,
      RootPairing.Hom.coroot_coweightMap_apply _ _ _ e.toHom, Equiv.symm_apply_apply] at h
    exact h
  constructor
  · intro h a
    rw [← hpair]
    exact h ⟨e.indexEquiv a, (hb a).mp a.2⟩
  · intro h b
    have hb' : e.indexEquiv.symm b ∈ p.base.support := (hb _).mpr (by simp)
    have := hpair (e.indexEquiv.symm b)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact h ⟨_, hb'⟩

end RootDatumEquiv

section HighestWeight

variable (E : G ≅ H) (τ : p.torus ≅ q.torus)
  (hsq : p.inclusion ≫ E.hom = CommGroupScheme.groupHom τ.hom ≫ q.inclusion)
  (e : RootPairing.Equiv p.rootDatum q.rootDatum)
  (he : ∀ χ, e.weightMap χ = characterLattice.congr τ χ)
  (hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
  {n : Type} [Fintype n] [DecidableEq n]

include hsq he in
theorem representationWeightSpace_restrict_iso_weightMap (ρ : MatrixRepresentation H n)
    (χ : characterLattice p.torus) :
    p.representationWeightSpace (ρ.restrict E.hom) χ =
      q.representationWeightSpace ρ (e.weightMap χ) := by
  rw [← representationWeightSpace_restrict_iso E τ hsq ρ (e.weightMap χ), he,
    AddEquiv.symm_apply_apply]

include hsq he hb in
/-- Highest-weight representations correspond under restriction along a group isomorphism
compatible with the split tori and a base-preserving equivalence of root data. -/
theorem isHighestWeight_restrict_iso_iff (ρ : MatrixRepresentation H n)
    (lam : characterLattice p.torus) :
    p.IsHighestWeight (ρ.restrict E.hom) lam ↔ q.IsHighestWeight ρ (e.weightMap lam) := by
  have hW := representationWeightSpace_restrict_iso_weightMap E τ hsq e he ρ
  have hirr : (ρ.restrict E.hom).IsIrreducible ↔ ρ.IsIrreducible := by
    unfold MatrixRepresentation.IsIrreducible
    simp only [MatrixRepresentation.isStableSubspace_restrict_iso_iff ρ E]
  have hsup : (⨆ μ, p.representationWeightSpace (ρ.restrict E.hom) μ) =
      ⨆ ν, q.representationWeightSpace ρ ν := by
    simp only [hW]
    exact e.weightEquiv.toEquiv.iSup_comp (g := fun ν => q.representationWeightSpace ρ ν)
  unfold IsHighestWeight
  rw [hirr, hsup, hW]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h ν hν
    obtain ⟨μ, rfl⟩ := e.weightEquiv.surjective ν
    have hμ := h μ (by rwa [hW])
    rw [← weightMap_mem_positiveRootMonoid_iff e hb, map_sub] at hμ
    exact hμ
  · intro h μ hμ
    rw [hW] at hμ
    have := h (e.weightMap μ) hμ
    rwa [← map_sub, weightMap_mem_positiveRootMonoid_iff e hb] at this

end HighestWeight

end SplitPinning

namespace GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]

local instance galoisPinningIsoAffine {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom (algebraBaseMap k K))
  infer_instance

/-- A pinned isomorphism of Galois pinning data: isomorphisms over `k` of the groups and of
the tori, compatible with the inclusions, and a base-preserving equivalence of the root data
over `K` whose weight map is the character map induced by the torus isomorphism. -/
structure Iso (d : GaloisPinningData k K G) (d' : GaloisPinningData k K G') where
  /-- The isomorphism of groups over `k`. -/
  groupIso : G ≅ G'
  /-- The isomorphism of tori over `k`. -/
  torusIso : d.torus ≅ d'.torus
  square : d.inclusion ≫ groupIso.hom = CommGroupScheme.groupHom torusIso.hom ≫ d'.inclusion
  /-- The equivalence of root data over `K`. -/
  rootDatumEquiv : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum
  weightMap_eq : ∀ χ, rootDatumEquiv.weightMap χ =
    characterLattice.congr ((CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso torusIso) χ
  base_iff : ∀ a, a ∈ d.toSplitPinning.base.support ↔
    rootDatumEquiv.indexEquiv a ∈ d'.toSplitPinning.base.support

namespace Iso

variable {d : GaloisPinningData k K G} {d' : GaloisPinningData k K G'} (f : d.Iso d')

/-- The isomorphism of the groups over `K`. -/
def baseChangeGroupIso :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G' :=
  (GroupScheme.baseChange (algebraBaseMap k K)).mapIso f.groupIso

/-- The isomorphism of the split tori over `K`. -/
def baseChangeTorusIso : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus :=
  (CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso f.torusIso

theorem baseChange_square :
    d.toSplitPinning.inclusion ≫ f.baseChangeGroupIso.hom =
      CommGroupScheme.groupHom f.baseChangeTorusIso.hom ≫ d'.toSplitPinning.inclusion := by
  change (GroupScheme.baseChange (algebraBaseMap k K)).map d.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map f.groupIso.hom =
    (GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f.torusIso.hom) ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map d'.inclusion
  rw [← Functor.map_comp, ← Functor.map_comp, f.square]

/-- The weight map of a pinned isomorphism: `χ ↦ χ ∘ t⁻¹` for the torus isomorphism `t` over
`K`. -/
def weightMap : characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
    characterLattice d'.toSplitPinning.torus :=
  f.rootDatumEquiv.weightEquiv

theorem weightMap_apply (χ : characterLattice d.toSplitPinning.torus) :
    f.weightMap χ = f.rootDatumEquiv.weightMap χ :=
  rfl

theorem weightMap_eq_comp (χ : characterLattice d.toSplitPinning.torus) :
    f.weightMap χ =
      (CommGroupScheme.baseChange (algebraBaseMap k K)).map f.torusIso.inv ≫ χ :=
  f.weightMap_eq χ

/-- The weight map intertwines the Galois actions on characters. -/
theorem weightMap_galoisRepresentation (σ : K ≃ₐ[k] K)
    (χ : characterLattice d.toSplitPinning.torus) :
    f.weightMap (characterLattice.galoisRepresentation k K d.torus σ χ) =
      characterLattice.galoisRepresentation k K d'.torus σ (f.weightMap χ) := by
  rw [f.weightMap_eq_comp, f.weightMap_eq_comp]
  exact (characterLattice.galoisRepresentation_naturality k K f.torusIso.inv σ χ).symm

/-- Dominant weights correspond under a pinned isomorphism. -/
theorem isDominantWeight_weightMap_iff (χ : characterLattice d.toSplitPinning.torus) :
    d'.toSplitPinning.IsDominantWeight (f.weightMap χ) ↔ d.toSplitPinning.IsDominantWeight χ :=
  SplitPinning.isDominantWeight_weightMap_iff f.rootDatumEquiv f.base_iff χ

/-- A representation of `G'_K` has highest weight `f.weightMap λ` exactly when its restriction to
`G_K` along the pinned isomorphism has highest weight `λ`. -/
theorem isHighestWeight_restrict_iff {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G') n)
    (lam : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.IsHighestWeight (ρ.restrict f.baseChangeGroupIso.hom) lam ↔
      d'.toSplitPinning.IsHighestWeight ρ (f.weightMap lam) :=
  SplitPinning.isHighestWeight_restrict_iso_iff f.baseChangeGroupIso f.baseChangeTorusIso
    f.baseChange_square f.rootDatumEquiv f.weightMap_eq f.base_iff ρ lam

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]

/-- **Star compatibility.** A pinned isomorphism intertwines the star actions. -/
theorem rootDatumEquiv_comp_starAction (σ : K ≃ₐ[k] K) :
    f.rootDatumEquiv.comp (d.starAction σ).val =
      (d'.starAction σ).val.comp f.rootDatumEquiv :=
  starAction_comp_of_character_intertwining d d' f.rootDatumEquiv f.base_iff σ σ
    (f.weightMap_galoisRepresentation σ)

theorem starAction_weightMap (σ : K ≃ₐ[k] K) (χ : characterLattice d.toSplitPinning.torus) :
    (d'.starAction σ).val.weightEquiv (f.weightMap χ) =
      f.weightMap ((d.starAction σ).val.weightEquiv χ) := by
  have h := congrArg (fun g : RootPairing.Equiv d.toSplitPinning.rootDatum
    d'.toSplitPinning.rootDatum => g.weightMap χ) (f.rootDatumEquiv_comp_starAction σ)
  exact h.symm

/-- Star-fixed weights correspond under a pinned isomorphism. -/
theorem isStarFixedWeight_weightMap_iff (χ : characterLattice d.toSplitPinning.torus) :
    d'.IsStarFixedWeight (f.weightMap χ) ↔ d.IsStarFixedWeight χ := by
  refine forall_congr' fun σ => ?_
  rw [f.starAction_weightMap]
  exact f.weightMap.injective.eq_iff

end Iso

end GaloisPinningData

end Langlands.GroupScheme
