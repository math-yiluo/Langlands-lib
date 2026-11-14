import Langlands.Sheaf.Equivariant.AnalyticEtaleSupport

/-! # Descent of global étale supports to underlying analytic points -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {R : Type (max u (v + 1) uL)} [CommRing R]

private theorem etaleSelf_fiber_eq (x : (localizedFieldPointFunctor L).obj X)
    (p q : (etalePoints L h x).fiber.obj (etaleSelf X)) : p = q := by
  apply ULift.ext
  apply Subtype.ext
  exact ((localizedFieldPointFunctor L).map_id_apply X p.down.1).symm.trans
    (p.down.2.trans (q.down.2.symm.trans
      ((localizedFieldPointFunctor L).map_id_apply X q.down.1)))

/-- A global section has zero germ at a field-valued point exactly when it
vanishes on an étale neighborhood of the underlying point, assuming point
lifting. -/
theorem not_mem_support_etaleSelf_iff (hlift : EtalePointLifting L (X := X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) (x : (localizedFieldPointFunctor L).obj X) :
    x ∉ support (etalePoints L h) F s ↔
      ∃ (U : EtaleSite X) (f : U ⟶ etaleSelf X),
        pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map U.hom) ∧
          F.map f.op s = 0 := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  constructor
  · intro hx
    let p : (etalePoints L h x).fiber.obj (etaleSelf X) :=
      ULift.up ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩
    have hz : (etalePoints L h x).toPresheafFiber (etaleSelf X) p F s =
        (etalePoints L h x).toPresheafFiber (etaleSelf X) p F 0 := by
      rw [map_zero]
      by_contra hn
      exact hx ⟨p, hn⟩
    obtain ⟨U, f, q, _, hq⟩ :=
      ((etalePoints L h x).toPresheafFiber_eq_iff' _ _ s 0).mp hz
    refine ⟨U, f, ?_, by simpa only [map_zero] using hq⟩
    refine ⟨pointProjection L U.left q.down.1, ?_⟩
    exact (pointProjection_map L U.hom q.down.1).symm.trans
      (congrArg (pointProjection L X) q.down.2)
  · rintro ⟨U, f, hx, hz⟩ ⟨p, hp⟩
    obtain ⟨q⟩ := hlift x U hx
    let q' : (etalePoints L h x).fiber.obj U := ULift.up q
    have hq : (etalePoints L h x).fiber.map f q' = p :=
      etaleSelf_fiber_eq L h x _ _
    apply hp
    rw [← hq, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]

/-- Membership in the support of a global section depends only on the
underlying point, assuming point lifting. -/
theorem mem_support_etaleSelf_iff_of_projection_eq
    (hlift : EtalePointLifting L (X := X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X)))
    {x y : (localizedFieldPointFunctor L).obj X}
    (hxy : pointProjection L X x = pointProjection L X y) :
    x ∈ support (etalePoints L h) F s ↔ y ∈ support (etalePoints L h) F s := by
  classical
  apply not_iff_not.mp
  rw [not_mem_support_etaleSelf_iff L h hlift F s x,
    not_mem_support_etaleSelf_iff L h hlift F s y, hxy]

/-- The support of a global section, viewed as a set of underlying analytic
points. -/
def etaleUnderlyingSupport
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) : Set (localizedSpaceFunctor.obj X) :=
  pointProjection L X '' support (etalePoints L h) F s

/-- The support upstairs is the full inverse image of its underlying-point
image, assuming point lifting. -/
theorem support_etaleSelf_eq_preimage (hlift : EtalePointLifting L (X := X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    support (etalePoints L h) F s =
      pointProjection L X ⁻¹' etaleUnderlyingSupport L h F s := by
  apply Set.Subset.antisymm (Set.subset_preimage_image _ _)
  rintro x ⟨y, hy, hyx⟩
  exact (mem_support_etaleSelf_iff_of_projection_eq L h hlift F s hyx).mp hy

/-- If all underlying points come from field-valued points, the complement of
the underlying support consists of images of étale neighborhoods on which the
global section is zero. -/
theorem not_mem_etaleUnderlyingSupport_iff
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) (y : localizedSpaceFunctor.obj X) :
    y ∉ etaleUnderlyingSupport L h F s ↔
      ∃ (U : EtaleSite X) (f : U ⟶ etaleSelf X),
        y ∈ Set.range (localizedSpaceFunctor.map U.hom) ∧ F.map f.op s = 0 := by
  obtain ⟨x, rfl⟩ := hX y
  change x ∉ pointProjection L X ⁻¹' etaleUnderlyingSupport L h F s ↔ _
  rw [← support_etaleSelf_eq_preimage L h hlift F s,
    not_mem_support_etaleSelf_iff L h hlift F s x]

/-- Openness of étale structural maps makes the underlying support of a
global section closed, assuming point lifting and surjectivity of the
underlying-point projection. -/
theorem isClosed_etaleUnderlyingSupport
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    IsClosed (etaleUnderlyingSupport L h F s) := by
  apply isOpen_compl_iff.mp
  have heq : (etaleUnderlyingSupport L h F s)ᶜ =
      ⋃ (U : EtaleSite X) (f : U ⟶ etaleSelf X) (_ : F.map f.op s = 0),
        Set.range (localizedSpaceFunctor.map U.hom) := by
    ext y
    simp only [Set.mem_compl_iff, not_mem_etaleUnderlyingSupport_iff L h hlift hX F s,
      Set.mem_iUnion]
    constructor
    · rintro ⟨U, f, hy, hz⟩
      exact ⟨U, f, hz, hy⟩
    · rintro ⟨U, f, hz, hy⟩
      exact ⟨U, f, hy, hz⟩
  rw [heq]
  exact isOpen_iUnion fun U => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    (hopen U).isOpen_range

/-- The field-valued support itself is closed for its induced topology under
the same hypotheses. -/
theorem isClosed_support_etaleSelf
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    letI := pointTopology L X
    IsClosed (support (etalePoints L h) F s) := by
  let := pointTopology L X
  rw [support_etaleSelf_eq_preimage L h hlift F s]
  exact (isClosed_etaleUnderlyingSupport L h hlift hX hopen F s).preimage
    (isInducing_pointProjection L X).continuous

/-- For a global section, containment of its field-valued support in a compact
set is equivalent to compactness of its actual underlying support, assuming
point lifting, surjectivity and openness of étale maps. -/
theorem isCompactlySupported_etaleSelf_iff_isCompact_underlyingSupport
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    letI := pointTopology L X
    IsCompactlySupported (etalePoints L h) F s ↔
      IsCompact (etaleUnderlyingSupport L h F s) := by
  let := pointTopology L X
  rw [show IsCompactlySupported (etalePoints L h) F s ↔
      ∃ C : Set (localizedSpaceFunctor.obj X), IsCompact C ∧
        etaleUnderlyingSupport L h F s ⊆ C from
    exists_isCompact_superset_iff_of_surjective L hX _]
  constructor
  · rintro ⟨C, hC, hsC⟩
    exact hC.of_isClosed_subset
      (isClosed_etaleUnderlyingSupport L h hlift hX hopen F s) hsC
  · intro hs
    exact ⟨_, hs, Set.Subset.rfl⟩

end Langlands.Sheaf.Equivariant.Analytic
