import Langlands.GroupScheme.Torus.RelativeTransporterEtaleLift
import Langlands.GroupScheme.Torus.HenselianNormalizerLifting

/-! # Pointed etale normalizer lifts with a prescribed integral torus action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    {G : GroupScheme (Spec R)} (i : T.toGrp ⟶ G) (σ : T ≅ T)

/-- Pointed etale data for an actual normalizing section with a fixed torus action. -/
structure PointedEtaleNormalizerData (s : Spec R)
    (n₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X) where
  neighbourhood : Scheme.{u}
  affine : IsAffine neighbourhood
  projection : neighbourhood ⟶ Spec R
  residuePoint : Spec ((Spec R).residueField s) ⟶ neighbourhood
  etale : Etale projection
  residue_over : residuePoint ≫ projection = (Spec R).fromSpecResidueField s
  sectionPoint : Over.mk (𝟙 neighbourhood) ⟶ ((GroupScheme.baseChange projection).obj G).X
  isNormalizing : IsNormalizingPoint ((GroupScheme.baseChange projection).map i) sectionPoint
    ((CommGroupScheme.baseChange projection).mapIso σ)
  recovers : residuePoint ≫ sectionPoint.left ≫ Limits.pullback.fst G.X.hom projection = n₀.left

set_option maxHeartbeats 800000 in
/-- A prescribed residue transporter for a split torus and its specified action lifts
etale locally to an actual normalizing section, recovering the residue point exactly. -/
def pointedEtaleNormalizerOfTransporter [IsAffine G.X.left]
    (hT : IsSplitTorus T.toGrp) (hG : Smooth G.X.hom) (s : Spec R)
    (n₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X)
    (hn₀ : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i n₀) :
    PointedEtaleNormalizerData i σ s n₀ := Classical.choice <| by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let eD : (Diagonalizable.groupScheme R (I → ℤ)).toGrp ≅ T.toGrp :=
    Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ e.symm
  let d₀ := PointwiseSchemeAction.pointedEtaleTransporter
    (eD.hom ≫ CommGroupScheme.groupHom σ.hom ≫ i) (eD.hom ≫ i)
    hG s n₀ (hn₀.precomp eD.hom)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show d₀.residuePoint default ∈ (⊤ : d₀.neighbourhood.Opens) from trivial)
  have hrange : Set.range d₀.residuePoint ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    change d₀.residuePoint x ∈ U
    have hx : x = default := Subsingleton.elim _ _
    rw [hx]
    exact hxU
  let b := IsOpenImmersion.lift hU.fromSpec d₀.residuePoint hrange
  have hb : b ≫ hU.fromSpec = d₀.residuePoint := IsOpenImmersion.lift_fac ..
  let : Etale d₀.projection := d₀.etale
  let a : Over.mk (hU.fromSpec ≫ d₀.projection) ⟶ Over.mk d₀.projection :=
    Over.homMk hU.fromSpec rfl
  let d : PointwiseSchemeAction.PointedEtaleTransporterData
      (eD.hom ≫ CommGroupScheme.groupHom σ.hom ≫ i) (eD.hom ≫ i) s n₀ :=
    { neighbourhood := Spec Γ(d₀.neighbourhood, U)
      projection := hU.fromSpec ≫ d₀.projection
      residuePoint := b
      etale := inferInstance
      residue_over := by rw [← Category.assoc, hb, d₀.residue_over]
      pointMap := a ≫ d₀.pointMap
      isTransporter := d₀.isTransporter.restrict a
      recovers := by
        apply Over.OverMorphism.ext
        change b ≫ (hU.fromSpec ≫ d₀.pointMap.left) = n₀.left
        rw [← Category.assoc, hb]
        exact congrArg Over.Hom.left d₀.recovers }
  refine ⟨⟨d.neighbourhood, inferInstance, d.projection, d.residuePoint, d.etale, d.residue_over,
    d.baseChangedSection, ?_, d.baseChangedSection_recovers⟩⟩
  apply isNormalizingPoint_of_isTransporter
  have h := d.baseChangedSection_isTransporter.precomp
    ((GroupScheme.baseChange d.projection).map eD.inv)
  simp only [← Functor.map_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h
  rw [Functor.map_comp] at h
  exact h

/-- A residue-fibre point regarded as a point of the original group. -/
def residueNormalizerPoint (s : Spec R)
    (n₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj G).X) :
    Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X :=
  (Over.homMk (𝟙 _) (by simp) :
      Over.mk ((Spec R).fromSpecResidueField s) ⟶
        (Over.map ((Spec R).fromSpecResidueField s)).obj (Over.mk (𝟙 _))) ≫
    baseChangePointsEquiv ((Spec R).fromSpecResidueField s) G _ n₀

/-- An actual normalizing point on a residue fibre lifts over an affine pointed
etale neighbourhood with its prescribed integral action and exact residue recovery. -/
def pointedEtaleNormalizerOfNormalizing [IsAffine G.X.left]
    (hT : IsSplitTorus T.toGrp) (hG : Smooth G.X.hom) (s : Spec R)
    (n₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (hn₀ : IsNormalizingPoint
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map i) n₀
      ((CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).mapIso σ)) :
    PointedEtaleNormalizerData i σ s (residueNormalizerPoint s n₀) := by
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map
        (CommGroupScheme.groupHom σ.hom ≫ i))
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map i) n₀ := by
    rw [Functor.map_comp]
    exact hn₀.isTransporter
  exact pointedEtaleNormalizerOfTransporter i σ hT hG s _
    ((ht.baseChangePointsEquiv _).restrict _)

/-- A residue normalizer lift together with an integral lift of its torus action. -/
structure PointedEtaleResidueNormalizerData (s : Spec R)
    (n₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (σ₀ : (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T ≅
      (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T) where
  action : T ≅ T
  action_recovers :
    (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).mapIso action = σ₀
  lift : PointedEtaleNormalizerData i action s (residueNormalizerPoint s n₀)

/-- Every specified residue normalizer of a split torus lifts over an affine
pointed etale neighbourhood, with exact point and torus-action recovery. -/
def pointedEtaleNormalizer [IsAffine G.X.left]
    (hT : IsSplitTorus T.toGrp) (hG : Smooth G.X.hom) (s : Spec R)
    (n₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (σ₀ : (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T ≅
      (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T)
    (hn₀ : IsNormalizingPoint
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map i) n₀ σ₀) :
    PointedEtaleResidueNormalizerData i s n₀ σ₀ := Classical.choice <| by
  obtain ⟨σ, hσ⟩ := hT.automorphism_fieldBaseChange_surjective
    ((Spec R).fromSpecResidueField s) σ₀
  have hn : IsNormalizingPoint
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map i) n₀
      ((CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).mapIso σ) := by
    exact (congrArg (fun τ => IsNormalizingPoint
      (T := (CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T)
      ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).map i) n₀ τ) hσ).mpr hn₀
  exact ⟨⟨σ, hσ, pointedEtaleNormalizerOfNormalizing i σ hT hG s n₀ hn⟩⟩

end Langlands.GroupScheme
