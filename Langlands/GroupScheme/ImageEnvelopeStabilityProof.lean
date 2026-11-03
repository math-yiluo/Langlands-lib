import Langlands.GroupScheme.ImageGenerationStatement
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof

/-! # Stability of closed image envelopes under affine group actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B} (b : AutomorphicAction H G)

/-- The subgroup of points whose whole orbit, after every refinement, lies in `F`. -/
def orbitCore (F : SubgroupFunctor G) : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over B) (c : T' ⟶ T) (h : T' ⟶ H.X),
        b.act h (c ≫ g) ∈ F.carrier T'}
      one_mem' := by
        intro T' c h
        rw [MonObj.comp_one, b.act_one]
        exact (F.carrier T').one_mem
      mul_mem' := by
        intro g g' hg hg' T' c h
        rw [MonObj.comp_mul, b.act_mul_right]
        exact (F.carrier T').mul_mem (hg T' c h) (hg' T' c h)
      inv_mem' := by
        intro g hg T' c h
        rw [GrpObj.comp_inv, b.act_inv]
        exact (F.carrier T').inv_mem (hg T' c h) }
  comp_mem c g hg T' d h := by
    rw [← Category.assoc]
    exact hg T' (d ≫ c) h

theorem orbitCore_le (F : SubgroupFunctor G) : b.orbitCore F ≤ F := by
  intro T g hg
  simpa only [Category.id_comp, b.act_one_left] using hg T (𝟙 T) 1

/-- The all-refinement orbit condition is detected at the universal acting point. -/
theorem mem_orbitCore_iff_universal (F : SubgroupFunctor G)
    {T : Over B} (g : T ⟶ G.X) :
    g ∈ (b.orbitCore F).carrier T ↔
      b.act (fst H.X T) (snd H.X T ≫ g) ∈ F.carrier (H.X ⊗ T) := by
  constructor
  · intro hg
    exact hg _ (snd H.X T) (fst H.X T)
  · intro hg T' c h
    simpa only [b.naturality, lift_fst, lift_snd_assoc] using
      F.comp_mem (lift h c) hg

theorem orbitCore_isStable (F : SubgroupFunctor G) : b.IsStable (b.orbitCore F) := by
  intro T h g hg T' c h'
  rw [b.naturality, ← b.act_mul_left]
  exact hg T' c (h' * (c ≫ h))

/-- An equivariant source lying in `F` lies in its orbit core. -/
theorem orbitCore_containsImage {V : Over B} (a : PointwiseSchemeAction H V)
    (f : V ⟶ G.X) (hf : a.IsEquivariant b.toPointwiseSchemeAction f)
    (F : SubgroupFunctor G) (hF : F.ContainsImage f) :
    (b.orbitCore F).ContainsImage f := by
  intro T v T' c h
  have he : a.act h (c ≫ v) ≫ f = b.act h ((c ≫ v) ≫ f) := hf T' h (c ≫ v)
  rw [← Category.assoc, ← he]
  exact hF T' (a.act h (c ≫ v))

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- For an affine acting group over a field, the orbit core of every actual
closed subgroup is again represented by an actual closed subgroup. -/
theorem orbitCore_range_isClosedRepresentable (b : AutomorphicAction H G)
    (hH : IsAffineHom H.X.hom) {K : GroupScheme (Spec (CommRingCat.of k))}
    (i : K ⟶ G) (hi : IsClosedSubgroup i) :
    (b.orbitCore (SubgroupFunctor.range i)).IsClosedRepresentable := by
  let D : Over (Spec (CommRingCat.of k)) := pullback b.hom i.hom.hom
  let d : D ⟶ H.X ⊗ G.X := pullback.fst b.hom i.hom.hom
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback b.hom i.hom.hom).map
        (Over.forget (Spec (CommRingCat.of k)))).flip hi
  have hcoords : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule H.X :=
    ⟨CommAlgCat.of (CommRingCat.of k) k, inferInstance, inferInstance⟩
  obtain ⟨Z, j, hj, hZ⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
      (CommRingCat.of k) H.X hH inferInstance hcoords G.X D d hd
  have hcore : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (b.orbitCore (SubgroupFunctor.range i)).carrier T ↔
        ∃ z : T ⟶ Z, z ≫ j = g := by
    intro T g
    rw [hZ T g, b.mem_orbitCore_iff_universal, SubgroupFunctor.mem_range]
    have hlift : lift (fst H.X T) (snd H.X T ≫ g) = H.X ◁ g := by
      apply hom_ext <;> simp
    change (∃ y : H.X ⊗ T ⟶ K.X,
      y ≫ i.hom.hom = lift (fst H.X T) (snd H.X T ≫ g) ≫ b.hom) ↔ _
    rw [hlift]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨pullback.lift (H.X ◁ g) y hy.symm, pullback.lift_fst _ _ _⟩
    · rintro ⟨q, hq⟩
      refine ⟨q ≫ pullback.snd b.hom i.hom.hom, ?_⟩
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (fun t => t ≫ b.hom) hq
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  exact SubgroupFunctor.isClosedRepresentable_of_scheme _ j hcore

/-- An equivariant image has stable closed envelope under any affine acting
group over a field, with no regularity assumptions on the source or target. -/
theorem closedImageEnvelope_isStable {V : Over (Spec (CommRingCat.of k))}
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (a : PointwiseSchemeAction H V) (f : V ⟶ G.X)
    (hf : a.IsEquivariant b.toPointwiseSchemeAction f) :
    b.IsStable (closedImageEnvelope f) := by
  intro T h g hg K i hi hfi
  obtain ⟨C, j, hj, hjclosed⟩ := b.orbitCore_range_isClosedRepresentable hH i hi
  have hcore : (b.orbitCore (SubgroupFunctor.range i)).ContainsImage f :=
    b.orbitCore_containsImage a f hf _ ((factorsThrough_iff_containsImage f i).1 hfi)
  have hgle := closedImageEnvelope_le_of_containsImage f j hj hjclosed hcore
  have hgcore := hgle T hg
  simpa only [Category.id_comp] using hgcore T (𝟙 T) h

end AutomorphicAction

/-- Split-torus stability of the same minimal closed pointed-image envelope. -/
theorem pointedImageEnvelopeStability : PointedImageEnvelopeStabilityStatement.{u} := by
  intro k _ G _hG _hAff V _hVAff _hVFin _hVInt _v₀ f _hv₀ S hS a b hf
  exact b.closedImageEnvelope_isStable hS.isAffineHom a f hf

end Langlands.GroupScheme
