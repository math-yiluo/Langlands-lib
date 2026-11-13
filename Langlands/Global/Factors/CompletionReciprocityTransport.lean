import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.Global.Factors.HenniartCompositeMapStatement

/-!
# Transport of geometric reciprocity candidates along isomorphisms of p-adic fields

For a `ℚ_p`-algebra isomorphism `g : F ≅ E` of p-adic fields and a geometric
reciprocity candidate `eE` of `E`, some geometric reciprocity candidate `eF` of `F`
satisfies `rec_F (φ w) = g⁻¹ (rec_E w)` for the Weil-group isomorphism
`φ = extensionWeilEquiv F E g : W_E ≅ W_F`. The proof takes the geometric candidate
of `F` given by the published existence theorem and evaluates the published
transfer/inclusion square along `g`, whose image subgroup is all of `W_F`.

The completion form transports a geometric candidate of a p-adic field `K` along
`f : K ≅ F_v` to the canonical completion package `padicField v`, for the
Weil-group isomorphism `completionWeilEquiv v h K f`.
-/

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local

universe u v

/-- The transfer to a subgroup that contains every element is evaluation. -/
theorem transfer_eq_of_forall_mem {G A : Type*} [Group G] [CommGroup A] {H : Subgroup G}
    [H.FiniteIndex] (hH : ∀ g, g ∈ H) (ϕ : H →* A) (g : G) :
    MonoidHom.transfer ϕ g = ϕ ⟨g, hH g⟩ := by
  classical
  have hsub : Subsingleton (G ⧸ H) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr (hH _)
  let := H.fintypeQuotientOfFiniteIndex
  rw [GroupTheory.Transfer.transfer_eq_prod_section ϕ (τ := fun _ => 1)
    (fun _ => Subsingleton.elim _ _) g,
    Fintype.prod_subsingleton _ ((1 : G) : G ⧸ H)]
  congr 1
  apply Subtype.ext
  simp only [inv_one, one_mul, mul_one]

/-- **Transport of geometric reciprocity along a `ℚ_p`-algebra isomorphism.** For
`g : F ≅ E` and a geometric candidate `eE` of `E`, some geometric candidate `eF`
of `F` satisfies `rec_F (φ w) = g⁻¹ (rec_E w)` for `φ = extensionWeilEquiv F E g`. -/
theorem exists_geometric_extensionWeilEquiv {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p) (g : F.Carrier ≃ₐ[Padic p] E.Carrier)
    (eE : LocalFactor.RankOne.ReciprocityCandidate E)
    (hE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE) :
    ∃ eF : LocalFactor.RankOne.ReciprocityCandidate F,
      GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF ∧
      ∀ w : localWeilGroup E,
        (LocalFactor.RankOne.reciprocityUnits F eF (extensionWeilEquiv F E g w) :
            F.Carrier) =
          g.symm (LocalFactor.RankOne.reciprocityUnits E eE w : E.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  obtain ⟨eF, hF, -⟩ :=
    geometricWeilReciprocityExistenceUniqueness.{u} p F F.canonicalTopologicalData
  refine ⟨eF, hF, fun w => ?_⟩
  have := extensionWeilMap_range_finiteIndex F E g.toAlgHom
  have hsq := extensionWeilTransferReciprocity.{u, v} p F E g.toAlgHom eF eE hF hE
    (extensionWeilMap F E g.toAlgHom w)
  rw [transfer_eq_of_forall_mem (H := (extensionWeilMap F E g.toAlgHom).toMonoidHom.range)
    (fun y => MonoidHom.mem_range.mpr
      ⟨(extensionWeilEquiv F E g).symm y, (extensionWeilEquiv F E g).apply_symm_apply y⟩)]
    at hsq
  have hrange : (LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
      (InductionAlong.rangeInverse (extensionWeilMap F E g.toAlgHom).toMonoidHom
        (extensionWeilMap_injective F E g.toAlgHom))
        ⟨extensionWeilMap F E g.toAlgHom w,
          MonoidHom.mem_range.mpr ⟨_, (extensionWeilEquiv F E g).apply_symm_apply _⟩⟩ =
      LocalFactor.RankOne.reciprocityUnits E eE w := by
    rw [MonoidHom.comp_apply]
    exact congrArg (LocalFactor.RankOne.reciprocityUnits E eE)
      (InductionAlong.rangeInverse_apply (extensionWeilMap F E g.toAlgHom).toMonoidHom
        (extensionWeilMap_injective F E g.toAlgHom) w)
  rw [hrange] at hsq
  rw [hsq]
  change _ = g.symm (g _)
  rw [AlgEquiv.symm_apply_apply]
  rfl

end Langlands.LocalClassField

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic

universe u uK

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- **Transport of a geometric reciprocity candidate from `K` to `F_v`.** For every
geometric candidate `e` of `K` there is a geometric candidate `e'` of the completion
package `padicField v` with `rec_{F_v} (φ w) = f (rec_K w)`, where
`φ = completionWeilEquiv v h K f`. -/
theorem exists_geometric_completionReciprocity
    (e : Correspondence.ReciprocityCandidate K)
    (he : Correspondence.IsGeometricReciprocity K e) :
    letI := (padicFieldAt v h).algebra
    ∃ e' : Correspondence.ReciprocityCandidate (padicField v),
      Correspondence.IsGeometricReciprocity (padicField v) e' ∧
      ∀ w : localWeilGroup K,
        (LocalFactor.RankOne.reciprocityUnits (padicField v) e'
            (completionWeilEquiv v h K f w) : (padicField v).Carrier) =
          f (LocalFactor.RankOne.reciprocityUnits K e w : K.Carrier) := by
  subst h
  let := (padicFieldAt v rfl).algebra
  obtain ⟨e', he', hrel⟩ :=
    LocalClassField.exists_geometric_extensionWeilEquiv (padicFieldAt v rfl) K f.symm e he
  exact ⟨e', he', fun w => hrel w⟩

end Langlands.Global
