import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGroupQuotient
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.GroupScheme.Torus.SplitPointTopology

/-! # Compact rational covers of actual norm-one adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]

/-- A compact set of actual norm-one adelic points meets every principal left coset. -/
def HasCompactNormOneRationalCover
    (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  ∃ Ω : Set (normOneSubgroup F G), IsCompact Ω ∧
    ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
      rationalNormOne F G q * g ∈ Ω

/-- Compact representatives give compactness of the actual norm-one rational quotient. -/
theorem HasCompactNormOneRationalCover.compactSpace
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : HasCompactNormOneRationalCover G) :
    CompactSpace (NormOneRationalQuotient F G) := by
  obtain ⟨Ω, hΩ, hcover⟩ := hG
  have himage : LeftCosetSpace.mk (rationalNormOneSubgroup F G) '' Ω = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective _ c
    obtain ⟨q, hq⟩ := hcover g
    exact ⟨rationalNormOne F G q * g, hq,
      LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup F G)
        ⟨rationalNormOne F G q, ⟨q, rfl⟩⟩ g⟩
  exact isCompact_univ_iff.mp (himage ▸ hΩ.image (LeftCosetSpace.continuous_mk _))

/-- A surjective actual norm-one map transports compact rational representatives. -/
theorem HasCompactNormOneRationalCover.map
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    (hG : HasCompactNormOneRationalCover G) (f : G ⟶ H)
    (hf : Function.Surjective (mapNormOne F G H f)) :
    HasCompactNormOneRationalCover H := by
  obtain ⟨Ω, hΩ, hcover⟩ := hG
  refine ⟨mapNormOne F G H f '' Ω, hΩ.image (mapNormOne F G H f).continuous, ?_⟩
  intro h
  obtain ⟨g, rfl⟩ := hf h
  obtain ⟨q, hq⟩ := hcover g
  refine ⟨G.affinePointsTarget f (CommAlgCat.of F F) q,
    rationalNormOne F G q * g, hq, ?_⟩
  rw [map_mul, mapNormOne_rationalNormOne]

/-- The compact-cover property is invariant under genuine group-scheme isomorphisms. -/
theorem HasCompactNormOneRationalCover.of_iso
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    (e : G ≅ H) (hH : HasCompactNormOneRationalCover H) :
    HasCompactNormOneRationalCover G := by
  apply hH.map e.inv
  intro g
  refine ⟨mapNormOne F G H e.hom g, ?_⟩
  apply Subtype.ext
  change ((g : AdelicGroupPoints F G) ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = _
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun f : G ⟶ G => f.hom.hom) e.hom_inv_id
  rw [Category.assoc, he, Category.comp_id]

variable (F)

/-- Finite products of the norm-one idele fundamental set give compact representatives
for the actual finite split torus, including the rank-zero torus. -/
theorem hasCompactNormOneRationalCover_splitTorus
    (I : Type u) [Fintype I] :
    HasCompactNormOneRationalCover (splitTorus (Spec (CommRingCat.of F)) I) := by
  classical
  let T := splitTorus (Spec (CommRingCat.of F)) I
  let e := splitTorus.affinePointsHomeomorph I (CommRingCat.of F)
    (CommAlgCat.of F (Adeles F))
  obtain ⟨C, hC, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  let D : Set (AdelicGroupPoints F T) := e.symm '' (Set.univ.pi fun _ : I => C)
  have hD : IsCompact D :=
    (isCompact_univ_pi fun _ : I => hC).image e.symm.continuous
  refine ⟨((↑) : normOneSubgroup F T → AdelicGroupPoints F T) ⁻¹' D,
    (isClosed_normOneSubgroup F T).isClosedEmbedding_subtypeVal.isCompact_preimage hD, ?_⟩
  intro g
  have hnorm : ∀ i : I, e (g : AdelicGroupPoints F T) i ∈
      NormOneIdeleClass.normOneIdeles F := by
    intro i
    exact (mem_normOneSubgroup F T _).mp g.property
      (CategoryTheory.Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of F))).toGrp) i)
  choose a ha using fun i => hcover (e (g : AdelicGroupPoints F T) i) (hnorm i)
  let q : RationalGroupPoints F T :=
    (splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F F)).symm a
  have hq : ∀ i : I, e (rational F T q) i = diagonalUnits F (a i) := by
    intro i
    have hn := character_rational F T
      (CategoryTheory.Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of F))).toGrp) i) q
    change e (rational F T q) i = diagonalUnits F
      (splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F F) q i) at hn
    simpa only [q, MulEquiv.apply_symm_apply] using hn
  refine ⟨q, ?_⟩
  change (rational F T q * (g : AdelicGroupPoints F T)) ∈ D
  refine ⟨e (rational F T q * (g : AdelicGroupPoints F T)),
    Set.mem_univ_pi.mpr (fun i => ?_), e.symm_apply_apply _⟩
  rw [map_mul, Pi.mul_apply, hq]
  exact ha i

/-- Every actual split torus over a number field has compact norm-one rational
representatives; its given splitting is used only through proved point homeomorphisms. -/
theorem hasCompactNormOneRationalCover_of_isSplitTorus
    (T : GroupScheme (Spec (CommRingCat.of F))) (hT : IsSplitTorus T) :
    HasCompactNormOneRationalCover T := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  exact (hasCompactNormOneRationalCover_splitTorus F I).of_iso e

/-- The multiplicative group is the rank-one case, on its actual adelic carrier. -/
theorem hasCompactNormOneRationalCover_gm :
    HasCompactNormOneRationalCover (Gm (Spec (CommRingCat.of F))).toGrp :=
  (hasCompactNormOneRationalCover_splitTorus F PUnit).of_iso (splitTorus.gmIso _)

end Langlands.Global.AdelicGroupPoints
