import Langlands.GroupScheme.Reductive.RootDatumBaseChangeStatement
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Actual split root data commute with field extension -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Normalizer

variable {S S' : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    {i : T.toGrp ⟶ G}

/-- A normalizing representative remains realizable after any base change. -/
theorem IsNormalizingPoint.exists_baseChange
    {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (b : S' ⟶ S) :
    ∃ n' : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X,
      IsNormalizingPoint ((GroupScheme.baseChange b).map i) n'
        ((CommGroupScheme.baseChange b).mapIso σ) := by
  have hc : HomConjugate i (CommGroupScheme.groupHom σ.hom ≫ i) := ⟨n, hn⟩
  obtain ⟨n', hn'⟩ := hc.baseChange b
  refine ⟨n', ?_⟩
  change _ = (GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom) ≫
    (GroupScheme.baseChange b).map i
  rw [← Functor.map_comp]
  exact hn'

/-- Character pullback commutes with the inverse-precomposition action. -/
theorem characterAut_baseChange (b : S' ⟶ S) (σ : T ≅ T)
    (χ : characterLattice T) :
    characterAut ((CommGroupScheme.baseChange b).mapIso σ)
      (characterLattice.baseChange b T χ) =
        characterLattice.baseChange b T (characterAut σ χ) := by
  change (CommGroupScheme.baseChange b).map σ.inv ≫ characterLattice.baseChange b T χ =
    characterLattice.baseChange b T (σ.inv ≫ χ)
  exact (characterLattice.baseChange_precomp b σ.inv χ).symm

end Normalizer

section RootDatum

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- Canonical lattice transport carries a supplied actual root datum to the
actual root datum of the pulled-back torus homomorphism. -/
theorem IsRootDatumOf.baseChange {J : Type v}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) :
    IsRootDatumOf ((GroupScheme.baseChange b).map i)
      (SplitRootDatum.baseChange b T hT P) := by
  refine ⟨SplitRootDatum.baseChange_toLinearMap b T hT P hP.1, ?_, ?_⟩
  · rw [roots_baseChange G T hT i]
    change Set.range (fun α => characterLattice.baseChange b T (P.root α)) =
      (characterLattice.baseChange b T) '' roots i
    rw [Set.range_comp', hP.2.1]
  · intro α
    obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
    obtain ⟨n', hn'⟩ := hn.exists_baseChange b
    refine ⟨n', (CommGroupScheme.baseChange b).mapIso σ, hn', ?_⟩
    apply LinearEquiv.ext
    intro χ'
    obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective χ'
    change characterAut ((CommGroupScheme.baseChange b).mapIso σ)
      (characterLattice.baseChange b T χ) =
        (SplitRootDatum.baseChange b T hT P).reflection α
          (characterLattice.baseChange b T χ)
    rw [characterAut_baseChange, SplitRootDatum.baseChange_reflection, hσ]

end RootDatum

/-- Actual root-datum compatibility for every field extension, at arbitrary universe. -/
theorem splitRootDatumFieldExtension : SplitRootDatumFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG T hT i _ J P hP
  have := hG.isAffineHom
  have := hG.smooth
  exact hP.baseChange (K := K) G T hT i

end Langlands.GroupScheme
