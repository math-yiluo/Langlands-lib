import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Reductive.PinningScalarCoherence
import Langlands.GroupScheme.Torus.LatticeGaloisScalarExtension
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Cocharacter transport along towers of fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace cocharacterLattice

open StarActionFiniteStage

variable (F E M : Type u) [Field F] [Field E] [Field M]
  [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

local notation "b" => algebraBaseMap F E
local notation "j" => algebraBaseMap E M
local notation "c" => algebraBaseMap F M
local notation "hc" => Lie.algebraBaseMap_tower (k := F) (K := E) (L := M)
local notation "TE" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "TM" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "iso" => towerIsoOf b j T c hc

/-- Extend the lattice through the canonical comparison to the direct base change. -/
def towerExtension : cocharacterLattice TE →+ cocharacterLattice TM :=
  ((cocharacterLattice.congr (iso).symm).toAddMonoidHom).comp
    (cocharacterLattice.baseChange j TE)

/-- If the intermediate torus is split, the actual cocharacter extension is bijective. -/
theorem towerExtension_bijective (hT : IsSplitTorus (TE).toGrp) :
    Function.Bijective (towerExtension F E M T) :=
  (cocharacterLattice.congr (iso).symm).bijective.comp
    (hT.cocharacterLattice_baseChange_bijective j TE)

/-- Extending both lattices preserves their pairing. -/
theorem pairing_towerExtension (χ : characterLattice TE) (ν : cocharacterLattice TE) :
    latticePairing TM (towerCharacterOf b j T c hc χ) (towerExtension F E M T ν) =
      latticePairing TE χ ν := by
  change latticePairing TM
      (characterLattice.congr (iso).symm (characterLattice.baseChange j TE χ))
      (cocharacterLattice.congr (iso).symm (cocharacterLattice.baseChange j TE ν)) = _
  rw [latticePairing_congr, latticePairing_baseChange]

/-- Compatible coefficient automorphisms commute with extension of split cocharacters. -/
theorem towerExtension_galois (hT : IsSplitTorus (TE).toGrp)
    (σ : E ≃ₐ[F] E) (τ : M ≃ₐ[F] M)
    (h : ∀ x : E, τ (algebraMap E M x) = algebraMap E M (σ x))
    (ν : cocharacterLattice TE) :
    towerExtension F E M T (galoisRepresentation F E T σ ν) =
      galoisRepresentation F M T τ (towerExtension F E M T ν) := by
  have hTM : IsSplitTorus (TM).toGrp := by
    exact IsSplitTorus.of_iso (groupTowerIsoOf b j c hc T.toGrp) (hT.baseChange j)
  have hcomm : j ≫ galoisBaseMap F E σ = galoisBaseMap F M τ ≫ j := by
    change Spec.map (CommRingCat.ofHom (algebraMap E M)) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap E M))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => (h x).symm
  have hchar : Function.Surjective (towerCharacterOf b j T c hc) :=
    (characterLattice.congr (iso).symm).surjective.comp
      (hT.characterLattice_baseChange_bijective j TE).surjective
  have hχ (χ : characterLattice TE) :
      towerCharacterOf b j T c hc (characterLattice.galoisRepresentation F E T σ χ) =
        characterLattice.galoisRepresentation F M T τ (towerCharacterOf b j T c hc χ) :=
    towerCharacterOf_transport b j T c hc (galoisBaseMap F E σ) (galoisBaseMap_over F E σ)
      (galoisBaseMap F M τ) (galoisBaseMap_over F M τ) hcomm χ
  apply hTM.isPerfPair_latticePairing.bijective_right.injective
  ext χ'
  obtain ⟨χ, rfl⟩ := hchar χ'
  let χ₀ := characterLattice.galoisRepresentation F E T σ⁻¹ χ
  have hs : characterLattice.galoisRepresentation F E T σ χ₀ = χ :=
    Representation.self_inv_apply _ _ _
  change latticePairing TM (towerCharacterOf b j T c hc χ)
      (towerExtension F E M T (galoisRepresentation F E T σ ν)) =
    latticePairing TM (towerCharacterOf b j T c hc χ)
      (galoisRepresentation F M T τ (towerExtension F E M T ν))
  rw [← hs, pairing_towerExtension, latticePairing_galoisRepresentation,
    hχ, latticePairing_galoisRepresentation, pairing_towerExtension]

/-- Changing ground field in a tower intertwines the cocharacter action of
an automorphism over the intermediate field with its restriction of scalars. -/
theorem galoisRepresentation_scalarExtension (hT : IsSplitTorus (TM).toGrp)
    (σ : M ≃ₐ[E] M) (ν : cocharacterLattice TM) :
    cocharacterLattice.congr iso (galoisRepresentation F M T (σ.restrictScalars F) ν) =
      galoisRepresentation E M TE σ (cocharacterLattice.congr iso ν) := by
  have hTE : IsSplitTorus ((CommGroupScheme.baseChange j).obj TE).toGrp :=
    IsSplitTorus.of_iso (groupTowerIsoOf b j c hc T.toGrp).symm hT
  apply hTE.isPerfPair_latticePairing.bijective_right.injective
  ext χ'
  obtain ⟨χ, rfl⟩ := (characterLattice.congr iso).surjective χ'
  let χ₀ := characterLattice.galoisRepresentation F M T (σ.restrictScalars F)⁻¹ χ
  have hχ₀ : characterLattice.galoisRepresentation F M T (σ.restrictScalars F) χ₀ = χ :=
    Representation.self_inv_apply _ _ _
  have hχ (ψ : characterLattice TM) :
      characterLattice.congr iso (characterLattice.galoisRepresentation F M T
          (σ.restrictScalars F) ψ) =
        characterLattice.galoisRepresentation E M TE σ (characterLattice.congr iso ψ) :=
    characterLattice.galoisRepresentation_scalarExtension hc T σ ψ
  change latticePairing ((CommGroupScheme.baseChange j).obj TE) (characterLattice.congr iso χ)
      (cocharacterLattice.congr iso (galoisRepresentation F M T (σ.restrictScalars F) ν)) =
    latticePairing ((CommGroupScheme.baseChange j).obj TE) (characterLattice.congr iso χ)
      (galoisRepresentation E M TE σ (cocharacterLattice.congr iso ν))
  rw [← hχ₀, latticePairing_congr, latticePairing_galoisRepresentation,
    hχ, latticePairing_galoisRepresentation, latticePairing_congr]


end cocharacterLattice

/-- On split tori, cocharacter extension is bijective and intertwines compatible
coefficient automorphisms. The tower isomorphism identifies the action over an
intermediate field with the restricted action over the ground field. -/
def CocharacterFieldTransportStatement : Prop :=
  ∀ (F E M : Type u) [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M]
    (T : CommGroupScheme (Spec (CommRingCat.of F))),
    let b := algebraBaseMap F E
    let j := algebraBaseMap E M
    let c := algebraBaseMap F M
    let TE := (CommGroupScheme.baseChange b).obj T
    let TM := (CommGroupScheme.baseChange c).obj T
    let e := StarActionFiniteStage.towerIsoOf b j T c Lie.algebraBaseMap_tower
    (IsSplitTorus TE.toGrp → Function.Bijective (cocharacterLattice.towerExtension F E M T) ∧
      ∀ (σ : E ≃ₐ[F] E) (τ : M ≃ₐ[F] M),
        (∀ x : E, τ (algebraMap E M x) = algebraMap E M (σ x)) →
        ∀ ν : cocharacterLattice TE,
          cocharacterLattice.towerExtension F E M T
            (cocharacterLattice.galoisRepresentation F E T σ ν) =
          cocharacterLattice.galoisRepresentation F M T τ
            (cocharacterLattice.towerExtension F E M T ν)) ∧
    (IsSplitTorus TM.toGrp → ∀ (σ : M ≃ₐ[E] M) (ν : cocharacterLattice TM),
      cocharacterLattice.congr e
          (cocharacterLattice.galoisRepresentation F M T (σ.restrictScalars F) ν) =
        cocharacterLattice.galoisRepresentation E M TE σ (cocharacterLattice.congr e ν))

theorem cocharacterFieldTransport : CocharacterFieldTransportStatement.{u} := by
  intro F E M _ _ _ _ _ _ _ T
  exact ⟨fun hT => ⟨cocharacterLattice.towerExtension_bijective F E M T hT,
      cocharacterLattice.towerExtension_galois F E M T hT⟩,
    cocharacterLattice.galoisRepresentation_scalarExtension F E M T⟩

end Langlands.GroupScheme
