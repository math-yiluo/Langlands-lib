import Langlands.GroupScheme.KernelCoreQuotient
import Langlands.GroupScheme.FactoredKernel
import Langlands.AlgebraicGeometry.FieldGroupSchemeHomogeneity
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.GroupScheme.SmoothConnectedZeroDimensional
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Dimension of quotients by smooth connected kernel cores -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ReducedSubgroup

variable {k : Type u} [Field k] [PerfectField k]
    (N : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType N.X.hom] [IsAffineHom N.X.hom]

/-- The reduced identity core has open underlying range in the full group. -/
theorem isOpen_range_identityCoreι :
    IsOpen (Set.range (identityCoreι N).hom.hom.left) := by
  change IsOpen (Set.range
    ((identityComponentι (reducedSubgroup N)).hom.hom.left ≫ redι N.X.left))
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact isOpen_image_redι _
    (IsOpenImmersion.isOpen_range (identityComponentι (reducedSubgroup N)).hom.hom.left)

end ReducedSubgroup

/-- The zero homomorphism has exactly the identity point as its topological range. -/
theorem range_zero_hom {k : Type u} [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))) :
    Set.range (0 : G ⟶ H).hom.hom.left = {IdentityComponent.identityPoint H} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact IdentityComponent.unit_left_apply H _
  · rintro rfl
    exact ⟨IdentityComponent.identityPoint G, IdentityComponent.unit_left_apply H _⟩

/-- A group homomorphism preserves the actual identity point. -/
theorem hom_identityPoint {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) :
    f.hom.hom.left (IdentityComponent.identityPoint G) =
      IdentityComponent.identityPoint H := by
  have h := IsMonHom.one_hom f.hom.hom
  exact congrArg (fun z => z.left (IdentityComponent.basePoint k)) h

/-- The identity point of a group scheme over a field is closed. -/
theorem isClosed_singleton_identityPoint {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsClosed ({IdentityComponent.identityPoint G} : Set G.X.left) := by
  have : IsClosedImmersion η[G.X].left :=
    isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left η[G.X].w
  have hr : Set.range η[G.X].left = {IdentityComponent.identityPoint G} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact IdentityComponent.unit_left_apply G _
    · rintro rfl
      exact ⟨IdentityComponent.basePoint k, rfl⟩
  rw [← hr]
  exact η[G.X].left.isClosedEmbedding.isClosed_range

/-- A connected smooth group of dimension zero over any field has only the zero homomorphism to any group scheme. -/
theorem eq_zero_of_smoothOfRelativeDimension_zero {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [ConnectedSpace G.X.left]
    (f : G ⟶ H) (h0 : SmoothOfRelativeDimension 0 G.X.hom) : f = 0 :=
  eq_zero_of_smoothOfRelativeDimension_zero_over_field f h0

/-- The underlying full kernel is the inverse image of the identity point. -/
theorem range_kernelι {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) :
    Set.range (kernelι f).hom.hom.left =
      f.hom.hom.left ⁻¹' {IdentityComponent.identityPoint H} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change f.hom.hom.left ((kernelι f).hom.hom.left z) = _
    rw [← Scheme.Hom.comp_apply, (kernel_isPullback_scheme f).w,
      Scheme.Hom.comp_apply]
    exact IdentityComponent.unit_left_apply H _
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
      (kernel_isPullback_scheme f) x (IdentityComponent.basePoint k) hx
    exact ⟨z, hz⟩

/-- The full kernel is homeomorphic to the topological identity fiber. -/
def kernelHomeo {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated H.X.hom]
    (f : G ⟶ H) :
    (kernel f).X.left ≃ₜ f.hom.hom.left ⁻¹' {IdentityComponent.identityPoint H} :=
  .trans (kernelι f).hom.hom.left.isClosedEmbedding.isEmbedding.toHomeomorph
    (.setCongr (range_kernelι f))

/-- An isolated identity in the full kernel makes the homomorphism quasi-finite
at the identity. -/
theorem quasiFiniteAt_identity_of_isOpen_kernel_identity {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated H.X.hom]
    (f : G ⟶ H) [LocallyOfFiniteType f.hom.hom.left]
    (hk : IsOpen ({IdentityComponent.identityPoint (kernel f)} : Set (kernel f).X.left)) :
    f.hom.hom.left.QuasiFiniteAt (IdentityComponent.identityPoint G) := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber,
    ← (f.hom.hom.left.fiberHomeo _).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  let e : (kernel f).X.left ≃ₜ
      f.hom.hom.left ⁻¹' {f.hom.hom.left (IdentityComponent.identityPoint G)} :=
    (kernelHomeo f).trans (.setCongr (by rw [hom_identityPoint f]))
  have ho := e.isOpen_image.mpr hk
  simp only [Set.image_singleton] at ho
  convert ho using 1
  congr 1
  apply Subtype.ext
  exact (hom_identityPoint (kernelι f)).symm

namespace KernelCoreQuotient

variable {k : Type u} [Field k] [PerfectField k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsSeparated A.X.hom]
    (f : G ⟶ A)

local instance dimension_kernel_locallyOfFiniteType : LocallyOfFiniteType (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

local instance dimension_kernel_isAffineHom : IsAffineHom (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

/-- The quotient projection kills the actual core, on every test scheme. -/
theorem inclusion_projection : inclusion f ≫ projection f = 0 := by
  apply (Grp.forget _).map_injective
  change (inclusion f).hom.hom ≫ (projection f).hom.hom = 1
  apply (mem_range_kernelι_iff (projection f) _).mp
  rw [(isFppfQuotient f).2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- The quotient induces the actual map of full kernels. -/
abbrev kernelMap : kernel f ⟶ kernel (factor f) :=
  FactoredKernel.map f (projection f) (factor f) (projection_factor f)

/-- The core becomes the identity of the descended full kernel. -/
theorem identityCoreι_kernelMap :
    ReducedSubgroup.identityCoreι (kernel f) ≫ kernelMap f = 0 := by
  apply (Grp.forget _).map_injective
  apply (cancel_mono (kernelι (factor f)).hom.hom).mp
  change (ReducedSubgroup.identityCoreι (kernel f)).hom.hom ≫
      (kernelMap f).hom.hom ≫ (kernelι (factor f)).hom.hom = _
  rw [← Grp.comp_hom_hom, FactoredKernel.map_comp]
  change (inclusion f ≫ projection f).hom.hom = _
  rw [inclusion_projection]
  exact (MonObj.one_comp _).symm

/-- The identity is isolated in the full descended scheme kernel. -/
theorem isOpen_singleton_kernel_identity :
    IsOpen ({IdentityComponent.identityPoint (kernel (factor f))} :
      Set (kernel (factor f)).X.left) := by
  have hi := ReducedSubgroup.isOpen_range_identityCoreι (kernel f)
  have ho := (kernelMap f).hom.hom.left.isOpenMap _ hi
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    ← Over.comp_left, ← Grp.comp_hom_hom, identityCoreι_kernelMap, range_zero_hom] at ho
  exact ho

instance locallyOfFiniteType_factor : LocallyOfFiniteType (factor f).hom.hom.left := by
  have : LocallyOfFiniteType ((factor f).hom.hom.left ≫ A.X.hom) := by
    rw [Over.w (factor f).hom.hom]
    infer_instance
  exact locallyOfFiniteType_of_comp (factor f).hom.hom.left A.X.hom

/-- The descended homomorphism is quasi-finite at its identity point. -/
theorem quasiFiniteAt_factor_identity :
    (factor f).hom.hom.left.QuasiFiniteAt (IdentityComponent.identityPoint (groupScheme f)) :=
  quasiFiniteAt_identity_of_isOpen_kernel_identity (factor f)
    (isOpen_singleton_kernel_identity f)

/-- A connected quotient by the kernel core has relative dimension at most
that of a smooth target of constant relative dimension. -/
theorem exists_relativeDimension_le [ConnectedSpace G.X.left]
    (n : ℕ) (hA : SmoothOfRelativeDimension n A.X.hom) :
    ∃ m : ℕ, m ≤ n ∧ SmoothOfRelativeDimension m (groupScheme f).X.hom := by
  obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    (groupScheme f).X.left _ (groupScheme f).X.hom inferInstance inferInstance
  have hle := Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension
    (groupScheme f).X.left A.X.left (factor f).hom.hom.left inferInstance
    (IdentityComponent.identityPoint (groupScheme f)) (quasiFiniteAt_factor_identity f)
  rw [Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
    k (groupScheme f).X.left (groupScheme f).X.hom m hm _
      (isClosed_singleton_identityPoint _),
    hom_identityPoint (factor f),
    Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
      k A.X.left A.X.hom n hA _ (isClosed_singleton_identityPoint _)] at hle
  exact ⟨m, by exact_mod_cast hle, hm⟩

/-- A nonzero map to a one-dimensional smooth group gives a one-dimensional
quotient by its smooth connected kernel core. -/
theorem smoothOfRelativeDimension_one [ConnectedSpace G.X.left]
    (hf : f ≠ 0) (hA : SmoothOfRelativeDimension 1 A.X.hom) :
    SmoothOfRelativeDimension 1 (groupScheme f).X.hom := by
  obtain ⟨m, hm, hdim⟩ := exists_relativeDimension_le f 1 hA
  have hm0 : m ≠ 0 := by
    intro heq
    subst m
    exact factor_ne_zero f hf
      (eq_zero_of_smoothOfRelativeDimension_zero (factor f) hdim)
  have heq : m = 1 := by omega
  exact heq ▸ hdim

end KernelCoreQuotient

end Langlands.GroupScheme
