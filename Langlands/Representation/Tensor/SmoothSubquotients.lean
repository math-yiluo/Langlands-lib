import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Tensor.ExternalSubquotient

/-! Actual smooth subquotients under group pullback and finite external tensor
products, with an explicit bridge to the unbundled representation relation. -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- The actual quotient of the presenting invariant subspace by the kernel of
its surjection is isomorphic to the presented smooth representation. -/
def subquotientPresentationIso
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (S : Subrepresentation A.representation)
    (q : S.toRepresentation.IntertwiningMap D.representation)
    (hq : Function.Surjective q) :
    subquotient A S q.ker ≅ D :=
  mkIso (Representation.Equiv.mk
    (q.toLinearMap.quotKerEquivOfSurjective hq) fun g => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ q g v)

/-- The two existing actual-subquotient formulations agree on smooth objects.
The unbundled relation puts its ambient representation first. -/
theorem isSubquotient_iff_representation
    {A D : SmoothRep.{0, uG, uV} ℂ G} :
    IsSubquotient D A ↔
      WeylBranchPieces.IsSubquotient A.representation D.representation := by
  constructor
  · rintro ⟨S, U, ⟨e⟩⟩
    refine ⟨S, (hom e.inv).comp (hom (mkQ (subrepresentation A S) U)), ?_⟩
    exact (hom_hom_surjective e.symm).comp (mkQ_surjective _ U)
  · rintro ⟨S, q, hq⟩
    exact ⟨S, q.ker, ⟨(subquotientPresentationIso S q hq).symm⟩⟩

/-- A common actual topological group pullback preserves actual subquotients. -/
theorem IsSubquotient.pullback
    {A D : SmoothRep.{0, uG, uV} ℂ G} (h : IsSubquotient D A)
    (e : H ≃ₜ* G) : IsSubquotient (pullback e D) (pullback e A) :=
  isSubquotient_iff_representation.mpr
    ((isSubquotient_iff_representation.mp h).comp e.toMonoidHom)

/-- A common group equivalence reflects as well as preserves actual
subquotients. -/
theorem isSubquotient_pullback_iff (e : H ≃ₜ* G)
    {A D : SmoothRep.{0, uG, uV} ℂ G} :
    IsSubquotient (pullback e D) (pullback e A) ↔ IsSubquotient D A := by
  constructor
  · intro h
    have h' := (isSubquotient_iff_representation.mp h).comp e.symm.toMonoidHom
    have hA : (A.representation.comp e.toMonoidHom).comp e.symm.toMonoidHom =
        A.representation := by
      ext g v
      change A.representation (e (e.symm g)) v = A.representation g v
      rw [e.apply_symm_apply]
    have hD : (D.representation.comp e.toMonoidHom).comp e.symm.toMonoidHom =
        D.representation := by
      ext g v
      change D.representation (e (e.symm g)) v = D.representation g v
      rw [e.apply_symm_apply]
    exact isSubquotient_iff_representation.mpr (by
      change WeylBranchPieces.IsSubquotient
        ((A.representation.comp e.toMonoidHom).comp e.symm.toMonoidHom)
        ((D.representation.comp e.toMonoidHom).comp e.symm.toMonoidHom) at h'
      rwa [hA, hD] at h')
  · exact fun h => h.pullback e

end Langlands.SmoothRep

namespace Langlands.FiniteTensor

universe uI uG uV uW

section LinearMaps

variable {ι : Type uI}
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The indexed tensor of injective complex linear maps is injective. -/
theorem piTensorMap_injective (f : ∀ i, V i →ₗ[ℂ] W i)
    (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  choose g hg using fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.mpr (hf i))
  have hgf : (PiTensorProduct.map g).comp (PiTensorProduct.map f) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simpa only [hg] using (PiTensorProduct.map_id (R := ℂ) (s := V))
  exact (show Function.LeftInverse (PiTensorProduct.map g) (PiTensorProduct.map f) from
    fun x => LinearMap.congr_fun hgf x).injective

/-- The indexed tensor of surjective complex linear maps is surjective. -/
theorem piTensorMap_surjective (f : ∀ i, V i →ₗ[ℂ] W i)
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (PiTensorProduct.map f) := by
  choose g hg using fun i =>
    LinearMap.exists_rightInverse_of_surjective (f i) (LinearMap.range_eq_top.mpr (hf i))
  have hfg : (PiTensorProduct.map f).comp (PiTensorProduct.map g) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simpa only [hg] using (PiTensorProduct.map_id (R := ℂ) (s := W))
  exact (show Function.RightInverse (PiTensorProduct.map g) (PiTensorProduct.map f) from
    fun x => LinearMap.congr_fun hfg x).surjective

end LinearMaps

section Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  {A D : ∀ i, SmoothRep.{0, uG, uV} ℂ (H i)}

omit [DecidableEq ι] in
/-- Factorwise actual smooth subquotients reassemble to an actual subquotient
of the entire external tensor product. -/
theorem isSubquotient_external
    (h : ∀ i, SmoothRep.IsSubquotient (D i) (A i)) :
    SmoothRep.IsSubquotient (externalSmoothObject D) (externalSmoothObject A) := by
  choose C i q hi hq using fun k => SmoothRep.isSubquotient_iff_exists.mp (h k)
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨externalSmoothObject C,
      (externalFunctor).map i, (externalFunctor).map q,
      piTensorMap_injective (fun k => (SmoothRep.hom (i k)).toLinearMap) hi,
      piTensorMap_surjective (fun k => (SmoothRep.hom (q k)).toLinearMap) hq⟩

/-- An actual occurrence of an external tensor of irreducible smooth factors
gives an actual occurrence in every corresponding ambient factor. -/
theorem isSubquotient_smooth_factor_of_external
    (hD : ∀ i, (D i).IsIrreducible)
    (h : SmoothRep.IsSubquotient (externalSmoothObject D) (externalSmoothObject A))
    (k : ι) : SmoothRep.IsSubquotient (D k) (A k) :=
  SmoothRep.isSubquotient_iff_representation.mpr
    (isSubquotient_factor_of_external
      (fun i => (A i).representation) (fun i => (D i).representation) hD
      (SmoothRep.isSubquotient_iff_representation.mp h) k)

end Smooth

end Langlands.FiniteTensor
