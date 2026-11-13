import Langlands.LocalFactor.NonabelianSystemFieldTransportVirtual
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.LocalClassField.AbelianizationTransport
import Langlands.HarmonicAnalysis.ConductorTransport

/-!
# Common-closure reciprocity families along an isomorphism of p-adic fields

For `g : F ≅ E` over `ℚ_p`, a reciprocity family on the closure of `E` gives one on
the closure of `F`: at `L`, abelianize `W_F(L) ≅ W_E(σ(L))`, apply the component at
`σ(L)`, and pull back along `L ≅ σ(L)`. Norm and normalization relations are
transported, so by uniqueness the transport of a normalized family is normalized.
-/

noncomputable section

universe u u₁ u₂

namespace Langlands.LocalFactor.NonabelianSystem.FieldTransport

open LocalClassField Weil.Local CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u₁} p) (E : PadicField.{u₂} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- The canonical topology on every finite intermediate field, viewed as a p-adic field. -/
local instance extensionTopology (K : PadicField.{u} p)
    (L : FiniteIntermediateExtension K.Carrier) :
    TopologicalSpace (L.asPadicField (p := p)).Carrier :=
  (L.asPadicField (p := p)).canonicalTopologicalData.topology

/-- The unit groups of `L ≅ σ(L)`, with their canonical topologies. -/
abbrev unitsEquiv (L : Extension F) :=
  PadicField.ConductorTransport.unitsEquiv (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L)

/-- The transported reciprocity family. -/
def transportFamily (eE : ReciprocityFamily E) : ReciprocityFamily F := fun L =>
  letI := (canonicalData F L).topology
  letI := (canonicalData E (mapExtension F E g L)).topology
  ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm.trans
    (eE (mapExtension F E g L))).trans (unitsEquiv F E g L).symm

theorem transportFamily_apply (eE : ReciprocityFamily E) (L : Extension F)
    (w : TopologicalAbelianization (weilSubgroup F L)) :
    transportFamily F E g eE L w =
      (unitsEquiv F E g L).symm
        (eE (mapExtension F E g L) ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm w)) :=
  rfl

theorem unitsEquiv_transportFamily (eE : ReciprocityFamily E) (L : Extension F)
    (w : TopologicalAbelianization (weilSubgroup F L)) :
    unitsEquiv F E g L (transportFamily F E g eE L w) =
      eE (mapExtension F E g L) ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm w) := by
  rw [transportFamily_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The abelianized nested inclusions commute with the subgroup isomorphisms. -/
theorem abelianizationCongr_symm_weilAbelianInclusion {M L : Extension F}
    (h : M.field ≤ L.field) (w : TopologicalAbelianization (weilSubgroup F L)) :
    (abelianizationCongr (subgroupWeilEquiv F E g M)).symm
        (M.weilAbelianInclusion L h (localResidueDegree F) w) =
      (mapExtension F E g M).weilAbelianInclusion (mapExtension F E g L)
        (mapExtension_mono F E g h) (localResidueDegree E)
        ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm w) := by
  refine QuotientGroup.induction_on w ?_
  intro x
  rfl

/-- The base-field degree is preserved on abelianizations. -/
theorem weilDegree_abelianizationCongr_symm (L : Extension F)
    (w : TopologicalAbelianization (weilSubgroup F L)) :
    (mapExtension F E g L).weilDegree (localResidueDegree E)
        ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm w) =
      L.weilDegree (localResidueDegree F) w := by
  refine QuotientGroup.induction_on w ?_
  intro x
  change localDegree E (((subgroupWeilEquiv F E g L).symm x : weilSubgroup E _) :
      localWeilGroup E) = localDegree F (x : localWeilGroup F)
  rw [← localDegree_weilEquiv F E g, subgroupWeilEquiv_symm_coe,
    ContinuousMulEquiv.apply_symm_apply]

/-- The field isomorphisms `M ≅ σ(M)` and `L ≅ σ(L)` commute with the inclusions. -/
theorem fieldEquiv_algebraMap_comp {M L : Extension F} (h : M.field ≤ L.field) :
    (IntermediateField.inclusion (mapExtension_mono F E g h)).toRingHom.comp
        (mapFieldRingEquiv F E g M : M.field →+* (mapExtension F E g M).field) =
      (mapFieldRingEquiv F E g L : L.field →+* (mapExtension F E g L).field).comp
        (IntermediateField.inclusion h).toRingHom :=
  RingHom.ext fun _ => rfl

/-- The field norm commutes with `L ≅ σ(L)`. -/
theorem mapFieldRingEquiv_norm {M L : Extension F} (h : M.field ≤ L.field) (x : L.field) :
    letI : Algebra M.field L.field := (IntermediateField.inclusion h).toAlgebra
    letI : Algebra (mapExtension F E g M).field (mapExtension F E g L).field :=
      (IntermediateField.inclusion (mapExtension_mono F E g h)).toAlgebra
    mapFieldRingEquiv F E g M (Algebra.norm M.field x) =
      Algebra.norm (mapExtension F E g M).field (mapFieldRingEquiv F E g L x) := by
  let : Algebra M.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : Algebra (mapExtension F E g M).field (mapExtension F E g L).field :=
    (IntermediateField.inclusion (mapExtension_mono F E g h)).toAlgebra
  have hn := Algebra.norm_eq_of_equiv_equiv (mapFieldRingEquiv F E g M)
    (mapFieldRingEquiv F E g L) (fieldEquiv_algebraMap_comp F E g h) x
  rw [hn]
  exact RingEquiv.apply_symm_apply _ _

/-- The unit norm commutes with `L ≅ σ(L)`. -/
theorem unitsEquiv_unitsNorm {M L : Extension F} (h : M.field ≤ L.field) (x : L.fieldˣ) :
    unitsEquiv F E g M (M.unitsNorm L h x) =
      (mapExtension F E g M).unitsNorm (mapExtension F E g L) (mapExtension_mono F E g h)
        (unitsEquiv F E g L x) := by
  apply Units.ext
  exact mapFieldRingEquiv_norm F E g h (x : L.field)

theorem transportFamily_normRelation (eE : ReciprocityFamily E)
    (hN : NormRelation E (canonicalData E) (localResidueDegree E) eE) :
    NormRelation F (canonicalData F) (localResidueDegree F) (transportFamily F E g eE) := by
  intro M L h
  apply MonoidHom.ext
  intro w
  apply (unitsEquiv F E g M).injective
  change unitsEquiv F E g M (transportFamily F E g eE M
      (M.weilAbelianInclusion L h (localResidueDegree F) w)) =
    unitsEquiv F E g M (M.unitsNorm L h (transportFamily F E g eE L w))
  rw [unitsEquiv_unitsNorm, unitsEquiv_transportFamily, unitsEquiv_transportFamily,
    abelianizationCongr_symm_weilAbelianInclusion]
  exact DFunLike.congr_fun (hN (mapExtension F E g M) (mapExtension F E g L)
    (mapExtension_mono F E g h)) _

theorem transportFamily_normalizationRelation (eE : ReciprocityFamily E)
    (hA : NormalizationRelation E (canonicalData E) (localResidueDegree E)
      E.canonicalTopologicalData eE) :
    NormalizationRelation F (canonicalData F) (localResidueDegree F)
      F.canonicalTopologicalData (transportFamily F E g eE) := by
  intro L w
  have hmap := PadicField.CanonicalTransport.normalizedAbs_map (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L)
    ((transportFamily F E g eE L w : L.fieldˣ) : L.field)
  have hu : fieldEquiv F E g L ((transportFamily F E g eE L w : L.fieldˣ) : L.field) =
      ((eE (mapExtension F E g L) ((abelianizationCongr (subgroupWeilEquiv F E g L)).symm w) :
        (mapExtension F E g L).fieldˣ) : (mapExtension F E g L).field) :=
    congrArg Units.val (unitsEquiv_transportFamily F E g eE L w)
  rw [hu] at hmap
  change (canonicalData F L).normalizedAbs _ = _
  refine hmap.symm.trans ?_
  refine (hA (mapExtension F E g L) _).trans ?_
  rw [weilDegree_abelianizationCongr_symm, PadicField.CanonicalTransport.residueCardinality_eq F E g]

/-- The transport of a normalized family is normalized. -/
theorem transportFamily_normalizedReciprocity (eE : ReciprocityFamily E)
    (hE : NormalizedReciprocity E eE) :
    NormalizedReciprocity F (transportFamily F E g eE) := by
  obtain ⟨e₀, h₀⟩ := commonClosureReciprocityExistence p F F.canonicalTopologicalData
  have heq : transportFamily F E g eE = e₀ :=
    ReciprocitySystemUniqueness.eq_of_norm_normalization F.canonicalTopologicalData
      (transportFamily_normRelation F E g eE hE.1.1) h₀.1.1
      (transportFamily_normalizationRelation F E g eE hE.2) h₀.2
      (ReciprocitySystemUniqueness.weilGaloisAbelianProjection_injective F)
  rw [heq]
  exact h₀

end Langlands.LocalFactor.NonabelianSystem.FieldTransport
