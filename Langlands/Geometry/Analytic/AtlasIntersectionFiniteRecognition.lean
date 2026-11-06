import Langlands.Geometry.Analytic.AtlasDomainTensorIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteRecognition

/-! # Recognition of intersections from finite local algebra comparisons -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- Changing the represented algebra by a bounded equivalence preserves the
full universal property and the literal locus in the unchanged base. -/
theorem Represents.postcomp_equiv {f : BoundedAlgHom K A B}
    {S : Set (BanachSpectrum A)} (hf : Represents K f S)
    (e : BoundedAlgEquiv K B C) :
    Represents K (e.toBoundedAlgHom.comp f) S := by
  refine ⟨hf.1, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hf.hasImageIn (e.spectrumHomeomorph y)
    · intro hx
      obtain ⟨y, hy⟩ := hf.2.1.symm ▸ hx
      refine ⟨e.spectrumHomeomorph.symm y, ?_⟩
      change BanachSpectrum.comap f.toBoundedRingHom
        (e.spectrumHomeomorph (e.spectrumHomeomorph.symm y)) = x
      rw [e.spectrumHomeomorph.apply_symm_apply]
      exact hy
  · intro R φ hφ
    obtain ⟨ψ, hψ, huniq⟩ := hf.2.2 R φ hφ
    refine ⟨ψ.comp e.symm.toBoundedAlgHom, ?_, ?_⟩
    · apply BoundedAlgHom.ext
      intro a
      change ψ (e.symm (e (f a))) = φ a
      rw [e.symm_apply_apply]
      exact congrArg (fun q : BoundedAlgHom K A R => q a) hψ
    · intro χ hχ
      have hχ' : χ.comp e.toBoundedAlgHom = ψ := by
        apply huniq
        exact hχ
      apply BoundedAlgHom.ext
      intro c
      have h := congrArg (fun q : BoundedAlgHom K B R => q (e.symm c)) hχ'
      simpa using h

end Langlands.Analytic.PresentedAffinoidAlgebra

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- Local comparison data for a global candidate algebra. No global domain
representation or global spectral injectivity is supplied as input. -/
structure FiniteIntersectionData (U V : LocalDomain a)
    (Q : PresentedAffinoidAlgebra K)
    (f : BoundedAlgHom K U.algebra Q) (g : BoundedAlgHom K V.algebra Q) where
  cover : Domain.FiniteCover (Domain.whole K Q)
  piece : Fin cover.size → LocalDomain a
  left : ∀ i, piece i ⟶ U
  right : ∀ i, piece i ⟶ V
  equiv : ∀ i, BoundedAlgEquiv K (cover.obj i).algebra (piece i).algebra
  left_eq : ∀ i, (equiv i).toBoundedAlgHom.comp ((cover.obj i).baseMap.comp f) =
    (left i).restriction
  right_eq : ∀ i, (equiv i).toBoundedAlgHom.comp ((cover.obj i).baseMap.comp g) =
    (right i).restriction
  locus_eq : (⋃ i, (piece i).locus) = U.locus ∩ V.locus
  saturated : ∀ i, (cover.obj i).locus =
    (BanachSpectrum.comap f.toBoundedRingHom) ⁻¹' (U.ambientMap ⁻¹' (piece i).locus)

namespace FiniteIntersectionData

variable {U V : LocalDomain a} {Q : PresentedAffinoidAlgebra K}
  {f : BoundedAlgHom K U.algebra Q} {g : BoundedAlgHom K V.algebra Q}
  (d : FiniteIntersectionData U V Q f g)

/-- Each unchanged cover algebra represents its full local piece over U. -/
theorem component_represents (i : Fin d.cover.size) :
    Represents K ((d.cover.obj i).baseMap.comp f) (U.ambientMap ⁻¹' (d.piece i).locus) := by
  have h := (d.left i).represents.postcomp_equiv (d.equiv i).symm
  have heq : (d.equiv i).symm.toBoundedAlgHom.comp (d.left i).restriction =
      (d.cover.obj i).baseMap.comp f := by
    apply BoundedAlgHom.ext
    intro b
    have hb := congrArg (fun q : BoundedAlgHom K U.algebra (d.piece i).algebra => q b)
      (d.left_eq i)
    change (d.equiv i).symm ((d.left i).restriction b) = _
    rw [← hb]
    exact (d.equiv i).symm_apply_apply _
  rw [heq] at h
  exact h

/-- The local full representation used to test injectivity of the composite. -/
def componentOverLeft (i : Fin d.cover.size) : Domain K U.algebra where
  algebra := (d.cover.obj i).algebra
  baseMap := (d.cover.obj i).baseMap.comp f
  locus := U.ambientMap ⁻¹' (d.piece i).locus
  represents := d.component_represents i

include d in
/-- Saturation forces two points with the same image into one local component;
injectivity there follows from its proved full representation. -/
theorem spectrum_injective : Function.Injective (BanachSpectrum.comap f.toBoundedRingHom) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := d.cover.covers x (Set.mem_univ x)
  have hy : y ∈ (d.cover.obj i).locus := by
    rw [d.saturated i] at hi ⊢
    change U.ambientMap (BanachSpectrum.comap f.toBoundedRingHom y) ∈ (d.piece i).locus
    change U.ambientMap (BanachSpectrum.comap f.toBoundedRingHom x) ∈ (d.piece i).locus at hi
    rw [← hxy]
    exact hi
  obtain ⟨x', hx'⟩ := (d.cover.obj i).represents.2.1.symm ▸ hi
  obtain ⟨y', hy'⟩ := (d.cover.obj i).represents.2.1.symm ▸ hy
  have hlocal : (d.componentOverLeft i).spectrumMap x' =
      (d.componentOverLeft i).spectrumMap y' := by
    change BanachSpectrum.comap f.toBoundedRingHom
        (BanachSpectrum.comap (d.cover.obj i).baseMap.toBoundedRingHom x') =
      BanachSpectrum.comap f.toBoundedRingHom
        (BanachSpectrum.comap (d.cover.obj i).baseMap.toBoundedRingHom y')
    rw [hx', hy']
    exact hxy
  have h := (Domain.spectrumEmbedding K U.algebra (d.componentOverLeft i)).injective hlocal
  exact hx'.symm.trans ((congrArg
    (BanachSpectrum.comap (d.cover.obj i).baseMap.toBoundedRingHom) h).trans hy')

/-- Finite full-domain recognition constructs the missing global universal
property while retaining exactly Q and f. -/
def recognizedDomain : Domain K U.algebra :=
  d.cover.domainOfFiniteCover f d.spectrum_injective (fun i => by
    rw [(d.component_represents i).2.1]
    exact d.component_represents i)

theorem component_ambient_left (i : Fin d.cover.size)
    (x : BanachSpectrum (d.piece i).algebra) :
    U.ambientMap (BanachSpectrum.comap f.toBoundedRingHom
      ((d.cover.obj i).spectrumMap ((d.equiv i).spectrumHomeomorph x))) =
        (d.piece i).ambientMap x := by
  calc
    _ = U.ambientMap ((d.left i).spectrumMap x) := by
      congr 1
      exact BanachSpectrum.ext fun b =>
        congrArg (fun q : BoundedAlgHom K U.algebra (d.piece i).algebra => x (q b))
          (d.left_eq i)
    _ = _ := (d.left i).ambientMap_naturality x

include d in
/-- The global candidate's literal ambient image is exactly the intersection. -/
theorem range_ambient : Set.range (fun x : BanachSpectrum Q =>
    U.ambientMap (BanachSpectrum.comap f.toBoundedRingHom x)) = U.locus ∩ V.locus := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := d.cover.covers x (Set.mem_univ x)
    rw [d.saturated i] at hi
    rw [← d.locus_eq]
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hy
    rw [← d.locus_eq] at hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx⟩ := (d.piece i).range_ambientMap.symm ▸ hi
    exact ⟨(d.cover.obj i).spectrumMap ((d.equiv i).spectrumHomeomorph x),
      (d.component_ambient_left i x).trans hx⟩

/-- Extend the recognized domain through U into its original atlas chart. -/
def intersection : LocalDomain a := U.extend d.recognizedDomain

theorem intersection_locus : d.intersection.locus = U.locus ∩ V.locus := by
  rw [intersection, extend_locus]
  change U.ambientMap '' Set.range (BanachSpectrum.comap f.toBoundedRingHom) = _
  rw [← Set.range_comp]
  exact d.range_ambient

/-- The canonical inclusion into the first unchanged input. -/
def leftInclusion : d.intersection ⟶ U :=
  Inclusion.ofSubset _ _ (by rw [d.intersection_locus]; exact Set.inter_subset_left)

/-- The canonical inclusion into the second unchanged input. -/
def rightInclusion : d.intersection ⟶ V :=
  Inclusion.ofSubset _ _ (by rw [d.intersection_locus]; exact Set.inter_subset_right)

theorem leftInclusion_restriction : d.leftInclusion.restriction = f := by
  have h : d.leftInclusion = U.extendInclusion d.recognizedDomain :=
    @Subsingleton.elim (Inclusion d.intersection U) inferInstance _ _
  exact congrArg Inclusion.restriction h

/-- Every local piece includes canonically into the recognized global domain. -/
def componentInclusion (i : Fin d.cover.size) : d.piece i ⟶ d.intersection :=
  Inclusion.ofSubset _ _ (by
    rw [d.intersection_locus, ← d.locus_eq]
    exact Set.subset_iUnion (fun j => (d.piece j).locus) i)

theorem componentInclusion_restriction (i : Fin d.cover.size) :
    (d.componentInclusion i).restriction =
      (d.equiv i).toBoundedAlgHom.comp (d.cover.obj i).baseMap := by
  apply d.recognizedDomain.represents.hom_ext (d.piece i).algebra
  change (d.componentInclusion i).restriction.comp f =
    ((d.equiv i).toBoundedAlgHom.comp (d.cover.obj i).baseMap).comp f
  rw [BoundedAlgHom.comp_assoc, d.left_eq i]
  have h : d.componentInclusion i ≫ d.leftInclusion = d.left i :=
    @Subsingleton.elim (Inclusion (d.piece i) U) inferInstance _ _
  have heq := congrArg Inclusion.restriction h
  change (d.componentInclusion i).restriction.comp d.leftInclusion.restriction =
    (d.left i).restriction at heq
  rw [d.leftInclusion_restriction] at heq
  exact heq

/-- Equality is checked after full bounded cover restrictions. Pointwise
spectrum equality is not used to identify the second algebra map. -/
theorem rightInclusion_restriction : d.rightInclusion.restriction = g := by
  apply BoundedAlgHom.ext
  intro b
  apply d.cover.algebra_ext_of_restrict_eq
  intro i
  have hbase : (d.cover.map i).restriction = (d.cover.obj i).baseMap := by
    have h := (d.cover.map i).comp_baseMap
    change (d.cover.map i).restriction = (d.cover.obj i).baseMap at h
    exact h
  change (d.cover.map i).restriction (d.rightInclusion.restriction b) =
    (d.cover.map i).restriction (g b)
  rw [hbase]
  apply (d.equiv i).toAlgEquiv.injective
  have h : d.componentInclusion i ≫ d.rightInclusion = d.right i :=
    @Subsingleton.elim (Inclusion (d.piece i) V) inferInstance _ _
  have heq := congrArg Inclusion.restriction h
  change (d.componentInclusion i).restriction.comp d.rightInclusion.restriction =
    (d.right i).restriction at heq
  rw [d.componentInclusion_restriction i] at heq
  exact (congrArg (fun q : BoundedAlgHom K V.algebra (d.piece i).algebra => q b)
    heq).trans (congrArg
      (fun q : BoundedAlgHom K V.algebra (d.piece i).algebra => q b) (d.right_eq i).symm)

/-- Admissibility of the candidate's genuine tensor map transfers to the
actual canonical full-domain inclusion restrictions without changing algebras. -/
theorem tensor_isAdmissibleEpi
    (h : (CompletedTensorAlgebra.lift f g).IsAdmissibleEpi) :
    (CompletedTensorAlgebra.lift d.leftInclusion.restriction
      d.rightInclusion.restriction).IsAdmissibleEpi := by
  rw [d.leftInclusion_restriction, d.rightInclusion_restriction]
  exact h

end FiniteIntersectionData
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
