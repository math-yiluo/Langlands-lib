import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Morphisms.FiniteFlatSourceDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation

/-! # Abelian-scheme properties descend along finite étale surjections of the source -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent

variable {X Y S : Scheme.{u}}

/-- Separatedness descends along a surjective universally closed morphism of the source. -/
theorem isSeparated_of_comp_of_surjective_of_universallyClosed (p : X ⟶ Y) (g : Y ⟶ S)
    [Surjective p] [UniversallyClosed p] [IsSeparated (p ≫ g)] : IsSeparated g := by
  let π : pullback (p ≫ g) (p ≫ g) ⟶ pullback g g :=
    pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ p) (by simp [pullback.condition])
  have hπ : UniversallyClosed π :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hΔ : pullback.diagonal (p ≫ g) ≫ π = p ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · simp only [π, Category.assoc]
      erw [pullback.lift_fst]
      simp
    · simp only [π, Category.assoc]
      erw [pullback.lift_snd]
      simp
  have hrange :
      Set.range (pullback.diagonal g) = π '' Set.range (pullback.diagonal (p ≫ g)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := p.surjective y
      refine ⟨pullback.diagonal (p ≫ g) x, ⟨x, rfl⟩, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun φ => φ x) hΔ
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      refine ⟨p x, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using (congrArg (fun φ => φ x) hΔ).symm
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact π.isClosedMap _ (pullback.diagonal (p ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Geometric connectedness descends along a surjective morphism of the source. -/
theorem geometricallyConnected_of_comp_of_surjective (p : X ⟶ Y) (g : Y ⟶ S)
    [Surjective p] [GeometricallyConnected (p ≫ g)] : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hW : IsPullback (pullback.fst p fst) (pullback.snd p fst ≫ snd) (p ≫ g) y :=
    (IsPullback.of_hasPullback p fst).paste_vert h
  have : ConnectedSpace ↥(pullback p fst) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hW
  exact (pullback.snd p fst).surjective.connectedSpace (pullback.snd p fst).continuous

/-- If `q` is finite, étale and surjective and `q ≫ g` is smooth, proper and has geometrically
connected fibres over a locally noetherian base, then so is `g`. -/
theorem smooth_isProper_geometricallyConnected_of_comp (q : X ⟶ Y) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [IsFinite q] [Etale q] [Surjective q] [Smooth (q ≫ g)]
    [IsProper (q ≫ g)] [GeometricallyConnected (q ≫ g)] :
    Smooth g ∧ IsProper g ∧ GeometricallyConnected g := by
  have : LocallyOfFiniteType g :=
    Langlands.AlgebraicGeometry.FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
      q g
  have : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective q g
  have : IsSeparated g := isSeparated_of_comp_of_surjective_of_universallyClosed q g
  refine ⟨Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation q g,
    (isProper_iff g).2 ⟨inferInstance, inferInstance, inferInstance⟩,
    geometricallyConnected_of_comp_of_surjective q g⟩

end Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}}

/-- A commutative group scheme receiving a finite étale surjective scheme morphism over `S` from
an abelian scheme, over a locally noetherian base, is an abelian scheme. The morphism need not be
a homomorphism. -/
def ofFiniteEtaleSurjective [IsLocallyNoetherian S] (A : AbelianScheme S) (B : CommGroupScheme S)
    (q : A.X.left ⟶ B.X.left) (hq : q ≫ B.X.hom = A.X.hom) [IsFinite q] [Etale q]
    [Surjective q] : AbelianScheme S :=
  have : Smooth (q ≫ B.X.hom) := by rw [hq]; infer_instance
  have : IsProper (q ≫ B.X.hom) := by rw [hq]; infer_instance
  have : GeometricallyConnected (q ≫ B.X.hom) := by rw [hq]; infer_instance
  have h := FiniteEtaleQuotientPropertyDescent.smooth_isProper_geometricallyConnected_of_comp q
    B.X.hom
  { B with
    smooth := h.1
    proper := h.2.1
    geometricallyConnected := h.2.2 }

@[simp] theorem ofFiniteEtaleSurjective_toCommGroupScheme [IsLocallyNoetherian S]
    (A : AbelianScheme S) (B : CommGroupScheme S) (q : A.X.left ⟶ B.X.left)
    (hq : q ≫ B.X.hom = A.X.hom) [IsFinite q] [Etale q] [Surjective q] :
    (ofFiniteEtaleSurjective A B q hq).toCommGroupScheme = B := rfl

end Langlands.AbelianScheme
