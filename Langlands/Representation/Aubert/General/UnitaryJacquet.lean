import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Unitary.HermitianDual

/-! # Conjugate-linear transport of Jacquet quotients for unitary representations -/

noncomputable section

namespace Langlands.Jacquet.Localization

universe uG uV uW

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A conjugate-linear equivariant map preserves the trivial-character relations. -/
theorem relations_one_le_comap_conjugate
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (U : Subgroup G)
    (f : V →ₗ⋆[ℂ] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = σ u (f v)) :
    relations ρ U 1 ≤ (relations σ U 1).comap f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  change f (ρ u v - ((1 : U →* ℂˣ) u : ℂ) • v) ∈ relations σ U 1
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hf]
  simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using
    sub_mem_relations σ U 1 u (f v)

/-- An equivariant conjugate-linear equivalence descends to the actual
trivial-character localization quotients, with the same formula on representatives. -/
def conjugateCoinvariantsEquiv
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (U : Subgroup G)
    (f : V ≃ₗ⋆[ℂ] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = σ u (f v)) :
    Coinvariants ρ U 1 ≃ₗ⋆[ℂ] Coinvariants σ U 1 := by
  let forward := (relations ρ U 1).mapQ (relations σ U 1) f.toLinearMap
    (relations_one_le_comap_conjugate ρ σ U f.toLinearMap hf)
  have hfi (u : U) (w : W) : f.symm (σ u w) = ρ u (f.symm w) := by
    apply f.injective
    simp only [f.apply_symm_apply, hf]
  let backward := (relations σ U 1).mapQ (relations ρ U 1) f.symm.toLinearMap
    (relations_one_le_comap_conjugate σ ρ U f.symm.toLinearMap hfi)
  refine LinearEquiv.ofLinearMap forward backward ?_ ?_
  · apply Submodule.linearMap_qext
    ext w
    change mk σ U 1 (f (f.symm w)) = mk σ U 1 w
    rw [f.apply_symm_apply]
  · apply Submodule.linearMap_qext
    ext v
    change mk ρ U 1 (f.symm (f v)) = mk ρ U 1 v
    rw [f.symm_apply_apply]

@[simp]
theorem conjugateCoinvariantsEquiv_mk
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (U : Subgroup G)
    (f : V ≃ₗ⋆[ℂ] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = σ u (f v)) (v : V) :
    conjugateCoinvariantsEquiv ρ σ U f hf (mk ρ U 1 v) = mk σ U 1 (f v) := rfl

end Langlands.Jacquet.Localization

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- An invariant positive form on an admissible smooth representation identifies,
conjugate-linearly, the carriers of its normalized Jacquet object and of the
same-subgroup normalized Jacquet object of its smooth contragredient. -/
def unitaryJacquetConjugateEquiv
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (b : InvariantPositiveForm A.representation) :
    ((normalizedJacquetFunctor U M hU hMU).obj A) ≃ₗ⋆[ℂ]
      ((normalizedJacquetFunctor U M hU hMU).obj A.contragredient) :=
  Jacquet.Localization.conjugateCoinvariantsEquiv
    A.representation (smoothContragredient A.representation) U
    (b.smoothDualEquiv hcofinal hA)
    (fun u v => b.toSmoothDual_apply_action hA.1 u v)

@[simp]
theorem unitaryJacquetConjugateEquiv_mk
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (b : InvariantPositiveForm A.representation) (v : A) :
    unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b
      (Jacquet.Localization.mk A.representation U 1 v) =
      Jacquet.Localization.mk (smoothContragredient A.representation) U 1
        (b.toSmoothDual hA.1 v) := rfl

/-- For an admissible unitarizable representation, the normalized Jacquet
object vanishes if and only if the same-subgroup Jacquet object of its smooth
dual vanishes. This is a same-subgroup comparison, with no opposite-duality claim. -/
theorem unitaryJacquet_subsingleton_iff
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (hunitary : IsUnitarizable A.representation) :
    Subsingleton ((normalizedJacquetFunctor U M hU hMU).obj A) ↔
      Subsingleton ((normalizedJacquetFunctor U M hU hMU).obj A.contragredient) := by
  obtain ⟨b⟩ := hunitary
  let e := unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b
  constructor
  · intro h
    exact ⟨fun x y => by
      rw [← e.apply_symm_apply x, ← e.apply_symm_apply y]
      exact congrArg e (@Subsingleton.elim _ h _ _)⟩
  · intro h
    exact ⟨fun x y => e.injective (@Subsingleton.elim _ h _ _)⟩

end Langlands.Aubert.General
