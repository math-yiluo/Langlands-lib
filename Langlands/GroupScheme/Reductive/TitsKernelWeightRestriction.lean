import Langlands.GroupScheme.Reductive.TitsKernelIndexChoice
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.Reductive.IntegralWeylVector

/-! # Actual fundamental-weight restriction to an anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

/-- Choose the actual torus morphism supplied by a kernel comparison. -/
def KernelComparison.torusMap (h : d.KernelComparison ι e) :
    e.pinning.torus ⟶ d.pinning.torus := h.choose

/-- Restrict actual absolute characters along the chosen kernel torus map. -/
def KernelComparison.weightRestriction (h : d.KernelComparison ι e) :
    characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
          d.pinning.torus) →ₗ[ℤ]
      characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
          e.pinning.torus) :=
  characterPrecompInt
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map h.torusMap)

/-- Simple coroots push forward to the corresponding actual ambient coroots. -/
theorem KernelComparison.coroot_comp_torusMap (h : d.KernelComparison ι e)
    (a : e.Vertex) :
    e.pinning.rootDatum.coroot a.val ≫
        (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
          h.torusMap =
      d.pinning.rootDatum.coroot (h.vertexEquiv a).val.val :=
  h.choose_spec.choose_spec.2.2.1 a.val

/-- Pairing a restricted character with a simple kernel coroot is the ambient
pairing at the corresponding zero vertex. -/
theorem KernelComparison.pairing_weightRestriction_simple (h : d.KernelComparison ι e)
    (x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)) (a : e.Vertex) :
    e.pinning.rootDatum.toLinearMap (h.weightRestriction x)
        (e.pinning.rootDatum.coroot a.val) =
      d.pinning.rootDatum.toLinearMap x
        (d.pinning.rootDatum.coroot (h.vertexEquiv a).val.val) := by
  change e.pinning.rootDatum.toLinearMap
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
        h.torusMap ≫ x) (e.pinning.rootDatum.coroot a.val) = _
  rw [e.pinning.isRootDatum.1, d.pinning.isRootDatum.1,
    latticePairing_precomp, h.coroot_comp_torusMap]

/-- The fundamental weight at an actual zero vertex restricts to the matching
fundamental weight of the actual kernel. -/
theorem KernelComparison.weightRestriction_fundamentalWeight_zero
    (h : d.KernelComparison ι e)
    (hd : d.pinning.rootDatum.corootSpan ℤ = ⊤)
    (he : e.pinning.rootDatum.corootSpan ℤ = ⊤) (a : d.zeroVertices) :
    h.weightRestriction
        (Langlands.RootDatum.fundamentalWeightBasis d.pinning.rootDatum d.pinning.base
          hd a.val) =
      Langlands.RootDatum.fundamentalWeightBasis e.pinning.rootDatum e.pinning.base
        he (h.vertexEquiv.symm a) := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq e.pinning.rootDatum e.pinning.base he
  intro b
  rw [h.pairing_weightRestriction_simple,
    Langlands.RootDatum.fundamentalWeightBasis_pairing,
    Langlands.RootDatum.fundamentalWeightBasis_pairing]
  have hb : (h.vertexEquiv b).val = a.val ↔ b = h.vertexEquiv.symm a := by
    constructor
    · intro hba
      have h' : h.vertexEquiv b = a := Subtype.ext hba
      calc
        b = h.vertexEquiv.symm (h.vertexEquiv b) :=
          (h.vertexEquiv.symm_apply_apply b).symm
        _ = h.vertexEquiv.symm a := congrArg h.vertexEquiv.symm h'
    · intro hba
      rw [hba, Equiv.apply_symm_apply]
  simp only [hb]

/-- The fundamental weight at a distinguished vertex restricts to zero in the
actual kernel's character lattice. -/
theorem KernelComparison.weightRestriction_fundamentalWeight_distinguished
    (h : d.KernelComparison ι e)
    (hd : d.pinning.rootDatum.corootSpan ℤ = ⊤)
    (he : e.pinning.rootDatum.corootSpan ℤ = ⊤)
    (a : d.Vertex) (ha : a ∈ d.distinguishedVertices) :
    h.weightRestriction
      (Langlands.RootDatum.fundamentalWeightBasis d.pinning.rootDatum d.pinning.base
        hd a) = 0 := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq e.pinning.rootDatum e.pinning.base he
  intro b
  rw [h.pairing_weightRestriction_simple,
    Langlands.RootDatum.fundamentalWeightBasis_pairing]
  have hb : (h.vertexEquiv b).val ≠ a := by
    intro hba
    have ha0 : a ∈ d.zeroVertices := hba ▸ (h.vertexEquiv b).property
    exact ha ha0
  simp [hb]

end Langlands.GroupScheme.TitsIndexData
