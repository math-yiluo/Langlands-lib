import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentationTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRadiusSpectrum
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-! # Bounded coefficient base change of weighted rational quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- Images of the actual source fractions under every bounded map have the
weighted monomial bound, including the empty monomial in zero quotients. -/
theorem hasBoundedMonomials_map_fraction
    (E : Type v) [NormedCommRing E] [NormedAlgebra K E]
    (α : BoundedAlgHom K (algebra K A s g f) E) :
    HasBoundedMonomials s E (fun j => α (fraction K A s g f j)) := by
  obtain ⟨C, hC, hα⟩ := α.bounded
  refine ⟨C, hC, fun d => ?_⟩
  have hm : StrictTateAlgebra.monomialValue (Fin m) E
      (fun j => α (fraction K A s g f j)) d =
        α (StrictTateAlgebra.monomialValue (Fin m) (algebra K A s g f)
          (fraction K A s g f) d) := by
    simp only [StrictTateAlgebra.monomialValue, Finsupp.prod, map_prod, map_pow]
  rw [hm]
  exact (hα _).trans (mul_le_mul_of_nonneg_left
    (monomialValue_norm_le_weight s (algebra K A s g f)
      (norm_one_le K (algebra K A s g f)) (fraction K A s g f)
      (norm_fraction_le K A s g f) d) hC.le)

namespace BaseChange

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {m : ℕ}
  {s : PositivePolyradius (Fin m)}
  {g : GeneralizedTateAlgebra A.polyradius K}
  {f : Fin m → GeneralizedTateAlgebra A.polyradius K}
  {g' : GeneralizedTateAlgebra B.polyradius K}
  {f' : Fin m → GeneralizedTateAlgebra B.polyradius K}
  {φ : BoundedAlgHom K A B}
  (hg : φ (presentationMap K A g) = presentationMap K B g')
  (hf : ∀ j, φ (presentationMap K A (f j)) = presentationMap K B (f' j))

include hg hf in
/-- Unit generation survives an arbitrary bounded coefficient homomorphism.
Only equality of the displayed coefficient classes is needed. -/
theorem generatesUnitIdeal (hunit : GeneratesUnitIdeal K A g f) :
    GeneratesUnitIdeal K B g' f' := by
  let J : Ideal B := Ideal.span (insert (presentationMap K B g')
    (Set.range fun j => presentationMap K B (f' j)))
  have hle : Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) ≤
        Ideal.comap φ.toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · change φ (presentationMap K A g) ∈ J
      rw [hg]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · change φ (presentationMap K A (f j)) ∈ J
      rw [hf j]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))
  have h1 := hle (show (1 : A) ∈ Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) by
    rw [hunit]
    trivial)
  exact J.eq_top_iff_one.mpr (by simpa only [Ideal.mem_comap, map_one] using h1)

include hg hf in
/-- The target inequalities are exactly the inverse image of the source
inequalities under the actual coefficient spectrum map. -/
theorem locus_eq_preimage :
    locus K B s g' f' =
      (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' locus K A s g f := by
  ext x
  change (∀ j, x (presentationMap K B (f' j)) ≤ s j * x (presentationMap K B g')) ↔
    ∀ j, x (φ (presentationMap K A (f j))) ≤ s j * x (φ (presentationMap K A g))
  simp only [hg, hf]

variable (E : Type v) [NormedCommRing E] [NormedAlgebra K E]
  (α : BoundedAlgHom K (algebra K A s g f) E)
  (β : BoundedAlgHom K B E)
  (hcompat : α.comp (baseMap K A s g f) = β.comp φ)

include hg hf hcompat in
/-- Agreement over the original algebra transfers the source fraction
equations to the actual target coefficient classes. -/
theorem fraction_equation (j : Fin m) :
    β (presentationMap K B g') * α (fraction K A s g f j) =
      β (presentationMap K B (f' j)) := by
  have hbase (a : A) : β (φ a) = α (baseMap K A s g f a) :=
    (congrArg (fun χ => χ a) hcompat).symm
  rw [← hg, ← hf j, hbase, hbase]
  change α.toAlgHom (baseMap K A s g f (presentationMap K A g)) *
    α.toAlgHom (fraction K A s g f j) = _
  rw [← map_mul]
  exact congrArg α (RationalPresentation.fraction_equation K A s g f j)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- Descend weighted convergent evaluation at the source fraction images
through the actual target rational equations. No generation is assumed. -/
def pushoutLift : BoundedAlgHom K (algebra K B s g' f') E :=
  liftFromBase K B s g' f' E β (fun j => α (fraction K A s g f j))
    (hasBoundedMonomials_map_fraction K A s g f E α)
    (fraction_equation hg hf E α β hcompat)

theorem pushoutLift_comp_baseMap :
    (pushoutLift hg hf E α β hcompat).comp (baseMap K B s g' f') = β :=
  liftFromBase_comp_baseMap K B s g' f' E β _
    (hasBoundedMonomials_map_fraction K A s g f E α)
    (fraction_equation hg hf E α β hcompat)

@[simp] theorem pushoutLift_fraction (j : Fin m) :
    pushoutLift hg hf E α β hcompat (fraction K B s g' f' j) =
      α (fraction K A s g f j) :=
  liftFromBase_fraction K B s g' f' E β _
    (hasBoundedMonomials_map_fraction K A s g f E α)
    (fraction_equation hg hf E α β hcompat) j

variable [CompleteSpace K]

/-- The existing bounded coefficient comparison is the other leg of the
actual quotient pushout. -/
theorem pushoutLift_comp_transport :
    (pushoutLift hg hf E α β hcompat).comp
      (presentationTransport K s g f g' f' φ hg hf) = α := by
  apply hom_ext K A s g f E
  · intro a
    change pushoutLift hg hf E α β hcompat
      (presentationTransport K s g f g' f' φ hg hf (baseMap K A s g f a)) = _
    rw [presentationTransport_baseMap]
    exact (congrArg (fun χ => χ (φ a))
      (pushoutLift_comp_baseMap hg hf E α β hcompat)).trans
        (congrArg (fun χ => χ a) hcompat).symm
  · intro j
    change pushoutLift hg hf E α β hcompat
      (presentationTransport K s g f g' f' φ hg hf (fraction K A s g f j)) = _
    rw [presentationTransport_fraction, pushoutLift_fraction]

/-- Both legs determine a bounded map out of the target quotient, even
without unit generation or completeness of the receiving algebra. -/
theorem hom_ext
    {F : Type v} [NormedCommRing F] [NormedAlgebra K F]
    (θ η : BoundedAlgHom K (algebra K B s g' f') F)
    (htransport : θ.comp (presentationTransport K s g f g' f' φ hg hf) =
      η.comp (presentationTransport K s g f g' f' φ hg hf))
    (hbase : θ.comp (baseMap K B s g' f') = η.comp (baseMap K B s g' f')) :
    θ = η := by
  apply RationalPresentation.hom_ext K B s g' f' F
  · intro b
    exact congrArg (fun χ => χ b) hbase
  · intro j
    have h := congrArg (fun χ => χ (fraction K A s g f j)) htransport
    simpa only [BoundedAlgHom.comp_apply, presentationTransport_fraction] using h

include hcompat in
/-- The target rational quotient is the bounded pushout along arbitrary
bounded coefficient change among complete ultrametric normed K-algebras.
The target universe is independent and no unit-generation hypothesis is used. -/
theorem existsUnique_pushoutLift :
    ∃! θ : BoundedAlgHom K (algebra K B s g' f') E,
      θ.comp (presentationTransport K s g f g' f' φ hg hf) = α ∧
        θ.comp (baseMap K B s g' f') = β := by
  refine ⟨pushoutLift hg hf E α β hcompat,
    ⟨pushoutLift_comp_transport hg hf E α β hcompat,
      pushoutLift_comp_baseMap hg hf E α β hcompat⟩, ?_⟩
  intro θ hθ
  apply hom_ext hg hf θ (pushoutLift hg hf E α β hcompat)
  · exact hθ.1.trans (pushoutLift_comp_transport hg hf E α β hcompat).symm
  · exact hθ.2.trans (pushoutLift_comp_baseMap hg hf E α β hcompat).symm

open CategoryTheory CategoryTheory.Limits

/-- Lift arbitrary compatible continuous maps through the actual inverse-image
locus and the proved target spectrum homeomorphism. -/
def spectrumLift (hunit : GeneratesUnitIdeal K A g f)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum B)) (q : C(X, BanachSpectrum (algebra K A s g f)))
    (hpq : ∀ x, BanachSpectrum.comap φ.toBoundedRingHom (p x) =
      spectrumMap K A s g f (q x)) :
    C(X, BanachSpectrum (algebra K B s g' f')) := by
  have hmem : ∀ x, p x ∈ locus K B s g' f' := by
    intro x
    rw [locus_eq_preimage hg hf]
    change BanachSpectrum.comap φ.toBoundedRingHom (p x) ∈ locus K A s g f
    rw [hpq x]
    exact spectrumMap_mem_locus K A s g f (q x)
  exact ⟨fun x => (locusHomeomorph K B s g' f'
      (generatesUnitIdeal hg hf hunit)).symm ⟨p x, hmem x⟩,
    (locusHomeomorph K B s g' f' (generatesUnitIdeal hg hf hunit)).symm.continuous.comp
      (p.continuous.subtype_mk hmem)⟩

omit [CompleteSpace K] in
@[simp] theorem spectrumMap_spectrumLift (hunit : GeneratesUnitIdeal K A g f)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum B)) (q : C(X, BanachSpectrum (algebra K A s g f)))
    (hpq : ∀ x, BanachSpectrum.comap φ.toBoundedRingHom (p x) =
      spectrumMap K A s g f (q x)) (x : X) :
    spectrumMap K B s g' f' (spectrumLift hg hf hunit p q hpq x) = p x :=
  congrArg Subtype.val
    ((locusHomeomorph K B s g' f' (generatesUnitIdeal hg hf hunit)).apply_symm_apply _)

@[simp] theorem presentationSpectrumMap_spectrumLift (hunit : GeneratesUnitIdeal K A g f)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum B)) (q : C(X, BanachSpectrum (algebra K A s g f)))
    (hpq : ∀ x, BanachSpectrum.comap φ.toBoundedRingHom (p x) =
      spectrumMap K A s g f (q x)) (x : X) :
    presentationSpectrumMap K s g f g' f' φ hg hf
      (spectrumLift hg hf hunit p q hpq x) = q x := by
  apply spectrumMap_injective K A s g f hunit
  calc
    spectrumMap K A s g f (presentationSpectrumMap K s g f g' f' φ hg hf
        (spectrumLift hg hf hunit p q hpq x)) =
        BanachSpectrum.comap φ.toBoundedRingHom
          (spectrumMap K B s g' f' (spectrumLift hg hf hunit p q hpq x)) :=
      ContinuousMap.congr_fun (presentationSpectrumMap_naturality K s g f g' f' φ hg hf) _
    _ = BanachSpectrum.comap φ.toBoundedRingHom (p x) :=
      congrArg _ (spectrumMap_spectrumLift hg hf hunit p q hpq x)
    _ = spectrumMap K A s g f (q x) := hpq x

omit [CompleteSpace K] in
/-- The projection to the target coefficient spectrum determines the lift. -/
theorem spectrumLift_unique (hunit : GeneratesUnitIdeal K A g f)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum B)) (q : C(X, BanachSpectrum (algebra K A s g f)))
    (hpq : ∀ x, BanachSpectrum.comap φ.toBoundedRingHom (p x) =
      spectrumMap K A s g f (q x))
    (r : C(X, BanachSpectrum (algebra K B s g' f')))
    (hr : ∀ x, spectrumMap K B s g' f' (r x) = p x) :
    r = spectrumLift hg hf hunit p q hpq := by
  apply ContinuousMap.ext
  intro x
  apply spectrumMap_injective K B s g' f' (generatesUnitIdeal hg hf hunit)
  rw [hr, spectrumMap_spectrumLift]

/-- The square uses the actual bounded coefficient map and quotient transport. -/
def spectrumCone :
    PullbackCone (TopCat.ofHom (BanachSpectrum.comapContinuous φ.toBoundedRingHom))
      (TopCat.ofHom (spectrumMap K A s g f)) :=
  PullbackCone.mk (TopCat.ofHom (spectrumMap K B s g' f'))
    (TopCat.ofHom (presentationSpectrumMap K s g f g' f' φ hg hf)) (by
      apply TopCat.ext
      intro x
      exact (ContinuousMap.congr_fun
        (presentationSpectrumMap_naturality K s g f g' f' φ hg hf) x).symm)

/-- Under source unit generation, the explicit target quotient spectrum is
the topological pullback along arbitrary bounded coefficient change. -/
def spectrumConeIsLimit (hunit : GeneratesUnitIdeal K A g f) :
    IsLimit (spectrumCone (s := s) hg hf) :=
  PullbackCone.IsLimit.mk _
    (fun S => TopCat.ofHom (spectrumLift hg hf hunit S.fst.hom S.snd.hom
      (fun x => ConcreteCategory.congr_hom S.condition x)))
    (fun S => by
      apply TopCat.ext
      intro x
      exact spectrumMap_spectrumLift hg hf hunit S.fst.hom S.snd.hom
        (fun y => ConcreteCategory.congr_hom S.condition y) x)
    (fun S => by
      apply TopCat.ext
      intro x
      exact presentationSpectrumMap_spectrumLift hg hf hunit S.fst.hom S.snd.hom
        (fun y => ConcreteCategory.congr_hom S.condition y) x)
    (fun S m hm _ => by
      apply TopCat.ext
      intro x
      exact congrArg (fun r : C(S.pt, BanachSpectrum (algebra K B s g' f')) => r x)
        (spectrumLift_unique hg hf hunit S.fst.hom S.snd.hom
          (fun y => ConcreteCategory.congr_hom S.condition y) m.hom
          (fun y => ConcreteCategory.congr_hom hm y)))

end BaseChange
end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
