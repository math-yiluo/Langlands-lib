import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.Rational.SplitTorusDominationRefinement
import Langlands.GroupScheme.Torus.GeometricallyIntegral
import Langlands.GroupScheme.ImageGenerationSourceTransport
import Langlands.GroupScheme.Derived.CommutatorEnvelope
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Operations on pointed split-torus domination -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite product of split tori is split over the same base. -/
theorem IsSplitTorus.pi {S : Scheme.{u}} {I : Type u} [Finite I]
    (T : I → GroupScheme S) (h : ∀ i, IsSplitTorus (T i)) :
    IsSplitTorus (GroupScheme.pi T) := by
  refine Finite.induction_empty_option
    (P := fun J => ∀ (_ : Finite J) (T : J → GroupScheme S),
      (∀ j, IsSplitTorus (T j)) → IsSplitTorus (GroupScheme.pi T))
    ?_ ?_ ?_ I inferInstance T h
  · intro α β e ih _ T hT
    have : Finite α := Finite.of_equiv β e.symm
    exact IsSplitTorus.of_iso (piEquivIso e T).symm (ih this _ fun a => hT (e a))
  · intro _ T _
    exact IsSplitTorus.of_iso (piEmptyIso T) (isSplitTorus_splitTorus PEmpty)
  · intro α _ ih _ T hT
    exact IsSplitTorus.of_iso (piOptionIso T)
      ((hT none).tensor (ih inferInstance _ fun a => hT (some a)))

variable {k : Type u} [Field k]
variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

namespace HasPointedSplitTorusDomination

/-- A dominant pointed finite ordered power of a split torus is a split-torus
parametrization. The map need not be a group homomorphism. -/
theorem of_power {P : GroupScheme (Spec (CommRingCat.of k))}
    (hP : IsSplitTorus P) (p : P.X ⟶ H.X)
    (hp : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p = 1)
    (n : ℕ) (hd : IsDominant (orderedPowerMap p n).left) :
    HasPointedSplitTorusDomination H := by
  let Q := GroupScheme.pi fun _ : ULift.{u} (Fin n) => P
  let q := piFinitePowerHom P n ≫ orderedPowerMap p n
  refine ⟨Q, q, IsSplitTorus.pi _ fun _ => hP, ⟨?_⟩,
    PointedTorusEnvelope.piFinitePowerHom_orderedPowerMap_one p hp n⟩
  apply hd.denseRange.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨(finitePowerPiHom P n).left x, ?_⟩
  have h := congrArg (fun h => (h ≫ orderedPowerMap p n).left x)
    (finitePowerPiHom_comp P n)
  simpa only [q, Category.assoc, Category.id_comp, Over.comp_left,
    Scheme.Hom.comp_apply] using h

/-- A dominant group homomorphism carries a supplied parametrization to its
target, keeping its ground field and its split-torus source. -/
theorem postcomp (h : HasPointedSplitTorusDomination H) (q : H ⟶ K)
    [IsDominant q.hom.hom.left] : HasPointedSplitTorusDomination K := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  have : IsDominant p.left := hd
  refine ⟨P, p ≫ q.hom.hom, hP, ?_, ?_⟩
  · change IsDominant (p.left ≫ q.hom.hom.left)
    infer_instance
  · rw [← Category.assoc, hp, MonObj.one_comp]

/-- Products of two supplied parametrizations give a parametrization of the
product. Reduced targets suffice to turn dominance into schematic dominance. -/
theorem tensor [IsReduced H.X.left] [IsReduced K.X.left]
    [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]
    [Flat H.X.hom] [Flat K.X.hom]
    (hH : HasPointedSplitTorusDomination H)
    (hK : HasPointedSplitTorusDomination K) :
    HasPointedSplitTorusDomination (H ⊗ K) := by
  obtain ⟨P, p, hP, hdP, hp⟩ := hH
  obtain ⟨Q, q, hQ, hdQ, hq⟩ := hK
  have : IsDominant p.left := hdP
  have : IsDominant q.left := hdQ
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : IsSchemeTheoreticallyDominant q.left :=
    IsSchemeTheoreticallyDominant.of_isDominant q.left
  have : Smooth Q.X.hom := hQ.smooth
  have : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P hP.isTorus
  have : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ.isTorus
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  have : QuasiCompact p.left := inferInstance
  have : QuasiCompact q.left := inferInstance
  have := ImageGeneration.isSchemeTheoreticallyDominant_whiskerRight p Q.X
  have := ImageGeneration.isSchemeTheoreticallyDominant_whiskerLeft q H.X
  have : IsSchemeTheoreticallyDominant (p ⊗ₘ q).left := by
    rw [MonoidalCategory.tensorHom_def, Over.comp_left]
    infer_instance
  have : IsAffine (P ⊗ Q).X.left := by
    change IsAffine (pullback P.X.hom Q.X.hom)
    infer_instance
  have : IsAffine (H ⊗ K).X.left := by
    change IsAffine (pullback H.X.hom K.X.hom)
    infer_instance
  have : QuasiCompact (p ⊗ₘ q).left := inferInstance
  refine ⟨P ⊗ Q, p ⊗ₘ q, hP.tensor hQ, inferInstance, ?_⟩
  apply hom_ext
  · rw [Category.assoc, tensorHom_fst, ← Category.assoc, MonObj.one_comp, hp, MonObj.one_comp]
  · rw [Category.assoc, tensorHom_snd, ← Category.assoc, MonObj.one_comp, hq, MonObj.one_comp]

end HasPointedSplitTorusDomination

namespace GeneratedImage

/-- A generated subgroup of a pointed split-torus image inherits split-torus
domination from any dominant finite ordered power of its canonical factor. -/
theorem hasPointedSplitTorusDomination
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (hP : IsSplitTorus P) (f : P.X ⟶ G.X)
    (hf : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ f = 1)
    (D : GeneratedImage f) (hD : D.HasSmoothConnectedGeneration) :
    HasPointedSplitTorusDomination D.group := by
  have : Mono D.inclusion.hom.hom := D.represents.1
  have hp : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ D.factor = 1 := by
    apply (cancel_mono D.inclusion.hom.hom).1
    rw [Category.assoc, D.factor_comp, hf, MonObj.one_comp]
  obtain ⟨n, -, hn⟩ := hD.2.2.2
  exact HasPointedSplitTorusDomination.of_power hP D.factor hp n hn

/-- A generated-image representative is unchanged by schematically dominant
precomposition of its source. -/
def ofSchematicallyDominantPrecomp {V W : Over (Spec (CommRingCat.of k))}
    (p : V ⟶ W) [IsSchemeTheoreticallyDominant p.left] (f : W ⟶ G.X)
    (D : GeneratedImage (p ≫ f)) : GeneratedImage f where
  group := D.group
  inclusion := D.inclusion
  closed := D.closed
  represents := by
    refine ⟨D.represents.1, le_antisymm ?_ ?_⟩
    · intro T x hx K i hi hf
      apply D.range_le i hi ?_ T hx
      obtain ⟨a, ha⟩ := hf
      exact ⟨p ≫ a, by rw [Category.assoc, ha]⟩
    · exact closedImageEnvelope_le f D.inclusion D.closed
        ⟨D.sourceFactor p f, D.sourceFactor_comp p f⟩

end GeneratedImage

/-- Pointed image generation from an actual split torus gives a smooth affine
geometrically connected subgroup with a pointed split-torus parametrization. -/
theorem exists_splitTorus_generatedImage
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {P : GroupScheme (Spec (CommRingCat.of k))} (hP : IsSplitTorus P)
    (f : P.X ⟶ G.X)
    (hf : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ f = 1) :
    ∃ D : GeneratedImage f,
      D.HasSmoothConnectedGeneration ∧ HasPointedSplitTorusDomination D.group := by
  have : Smooth P.X.hom := hP.smooth
  have : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P hP.isTorus
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G
    inferInstance inferInstance P.X inferInstance inferInstance
    hP.isTorus.geometricallyIntegral 1 f hf
  exact ⟨D, hD, D.hasPointedSplitTorusDomination hP f hf hD⟩

namespace HasPointedSplitTorusDomination

/-- The subgroup generated by a pointed morphism out of a reduced group with a
split-torus parametrization again has a split-torus parametrization. -/
theorem generatedImage [IsReduced H.X.left] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : HasPointedSplitTorusDomination H) (f : H.X ⟶ G.X)
    (hf : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) ≫ f = 1)
    (D : GeneratedImage f) : HasPointedSplitTorusDomination D.group := by
  obtain ⟨P, p, hP, hd, hp⟩ := hH
  have : IsDominant p.left := hd
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have hpf : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ (p ≫ f) = 1 := by
    rw [← Category.assoc, hp, hf]
  obtain ⟨E, -, hE⟩ := exists_splitTorus_generatedImage hP (p ≫ f) hpf
  exact hE.of_iso ((E.ofSchematicallyDominantPrecomp p f).iso D)

/-- The actual derived subgroup of a smooth affine group inherits pointed
split-torus domination. -/
theorem derivedSubgroup [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasPointedSplitTorusDomination G) {D : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ G) (hd : IsDerivedSubgroup d) :
    HasPointedSplitTorusDomination D := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  have : Smooth (G ⊗ G).X.hom := smooth_tensor G.X G.X inferInstance inferInstance
  have : IsReduced (G ⊗ G).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (G ⊗ G).X.hom
  apply (hG.tensor hG).generatedImage (commutatorMap (𝟙 G) (𝟙 G)) ?_ hd.generatedImage
  rw [commutatorMap_points]
  simp only [MonObj.one_comp, inv_one, mul_one]

end HasPointedSplitTorusDomination

end Langlands.GroupScheme
