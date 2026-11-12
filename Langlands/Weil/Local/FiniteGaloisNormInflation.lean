import Langlands.Weil.Local.FiniteGaloisTower
import Langlands.Weil.Local.ExtensionNormReciprocity
import Langlands.GroupTheory.ExtensionNormInflation

/-! # Inflation of finite Galois Weil classes from the norm square -/

noncomputable section

namespace Langlands.Weil.Local

universe u

open LocalClassField LocalFactor.RankOne GroupExtensionPushout
open ClassFieldTheory.Local

namespace FiniteGaloisTower

/-- `cohomologyClass_inflate_norm` for a quotient map `q'` that equals `π ∘ q`. -/
theorem cohomologyClass_inflate_norm_of_comp {W : Type*} {G A Q B : Type u} [Group W] [Group G]
    [CommGroup A] [MulDistribMulAction G A] [Group Q] [CommGroup B] [MulDistribMulAction Q B]
    {q : W →* G} (π : G →* Q) [Fintype π.ker] (hπ : Function.Surjective π) (t : Section q)
    (r : q.ker →* A) (hr : ∀ (x : W) (n : q.ker), r (conjugateKernel q x n) = q x • r n)
    (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b) (q' : W →* Q) (hq' : π.comp q = q')
    (s : Section q') (r' : q'.ker →* B)
    (hr' : ∀ (x : W) (n : q'.ker), r' (conjugateKernel q' x n) = q' x • r' n)
    (hN : ∀ (x : q.ker) (hx : (x : W) ∈ q'.ker),
      ι (r' ⟨x, hx⟩) = ∏ h : π.ker, (h : G) • r x) :
    NormalizedTwoCocycle.cohomologyClass
        (NormalizedTwoCocycle.inflate π ι hι (s.cocycle r' hr')) =
      Fintype.card π.ker • NormalizedTwoCocycle.cohomologyClass (t.cocycle r hr) := by
  subst hq'
  exact cohomologyClass_inflate_norm π t r hr hπ ι hι s r' hr'
    (fun x => hN x (kernelInclusion π x).property)

variable {p : ℕ} [Fact p.Prime] (F E L : PadicField.{u} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier) (g : E.Carrier →ₐ[Padic p] L.Carrier)
  (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
  (hL : letI := extensionAlgebra F L (g.comp f); IsGalois F.Carrier L.Carrier)
  (hF1 : ∀ x : E.Carrier,
    extensionFieldEmbedding F L (g.comp f) (g x) = extensionFieldEmbedding F E f x)

/-- The kernel of the tower restriction `Gal(L/F) → Gal(E/F)` is the group of automorphisms
of `L` over `E`. -/
def towerKernelEquiv :
    letI := extensionAlgebra E L g
    (towerRestriction F E L f g hE).ker ≃ Gal(L.Carrier/E.Carrier) := by
  letI := extensionAlgebra F E f
  letI := extensionAlgebra F L (g.comp f)
  letI := extensionAlgebra E L g
  letI : IsScalarTower F.Carrier E.Carrier L.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact
    { toFun := fun h =>
        { (h : Gal(L.Carrier/F.Carrier)) with
          commutes' := fun z => by
            have h1 := towerRestriction_apply F E L f g hE h z
            rw [MonoidHom.mem_ker.mp h.property, AlgEquiv.one_apply] at h1
            exact h1.symm }
      invFun := fun τ => ⟨τ.restrictScalars F.Carrier, by
        rw [MonoidHom.mem_ker]
        apply AlgEquiv.ext
        intro z
        rw [AlgEquiv.one_apply]
        exact g.injective ((towerRestriction_apply F E L f g hE _ z).trans (τ.commutes z))⟩
      left_inv := fun h => Subtype.ext (AlgEquiv.ext fun _ => rfl)
      right_inv := fun τ => AlgEquiv.ext fun _ => rfl }

include hL in
/-- The product of the conjugates of a unit of `L` under the kernel of the tower restriction
is its norm to `E`. -/
theorem prod_towerKernel_smul (b : L.Carrierˣ) :
    letI := extensionAlgebra F L (g.comp f)
    letI := extensionAlgebra E L g
    letI := towerKernelFintype F E L f g hE
    ∏ h : (towerRestriction F E L f g hE).ker, (h : Gal(L.Carrier/F.Carrier)) • b =
      Units.map (algebraMap E.Carrier L.Carrier).toMonoidHom
        (Units.map (Algebra.norm E.Carrier) b) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := extensionAlgebra E L g
  let _ : IsScalarTower F.Carrier E.Carrier L.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := hL
  let := towerKernelFintype F E L f g hE
  have := extensionAlgebra_finiteDimensional F L (g.comp f)
  have := extensionAlgebra_finiteDimensional E L g
  have : IsGalois E.Carrier L.Carrier :=
    IsGalois.tower_top_of_isGalois F.Carrier E.Carrier L.Carrier
  apply Units.ext
  rw [Units.coe_prod]
  change ∏ h : (towerRestriction F E L f g hE).ker,
      (h : Gal(L.Carrier/F.Carrier)) (b : L.Carrier) =
    algebraMap E.Carrier L.Carrier (Algebra.norm E.Carrier (b : L.Carrier))
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv (towerKernelEquiv F E L f g hE) _ _ (fun _ => rfl)

include hF1 in
/-- The tower correction restricted to `L` fixes `E`, so it preserves the norm to `E`. -/
theorem norm_absoluteBaseConjugation_towerCorrection (a : L.Carrier) :
    letI := extensionAlgebra E L g
    Algebra.norm E.Carrier
        (absoluteBaseConjugation F L (g.comp f) hL (towerCorrection F E L f g) a) =
      Algebra.norm E.Carrier a := by
  let := extensionAlgebra E L g
  let σ : L.Carrier ≃ₐ[E.Carrier] L.Carrier :=
    { absoluteBaseConjugation F L (g.comp f) hL (towerCorrection F E L f g) with
      commutes' := absoluteBaseConjugation_towerCorrection F E L f g hL hF1 }
  exact Algebra.norm_eq_of_algEquiv σ a

variable (eE : ReciprocityCandidate E)
  (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
  (eL : ReciprocityCandidate L)
  (heL : GeometricWeilReciprocityRelation L L.canonicalTopologicalData eL)

include hF1 heE heL in
/-- The norm hypothesis of `cohomologyClass_inflate_norm` for the tower `F ⊂ E ⊂ L`: on the
kernel of the `L`-quotient, inverse reciprocity of `E` followed by `E → L` is the product of
the `Gal(L/E)`-conjugates of inverse reciprocity of `L`. -/
theorem towerNorm
    (x : letI := extensionAlgebra F L (g.comp f);
      (finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom.ker)
    (hx : letI := extensionAlgebra F E f;
      (x : localWeilGroup F) ∈ (finiteGaloisQuotient F E f hE).toMonoidHom.ker) :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F L (g.comp f)
    letI := extensionAlgebra E L g
    letI := towerKernelFintype F E L f g hE
    Units.map (algebraMap E.Carrier L.Carrier).toMonoidHom
        (finiteGaloisKernelReciprocity F E f hE eE ⟨x, hx⟩) =
      ∏ h : (towerRestriction F E L f g hE).ker,
        (h : Gal(L.Carrier/F.Carrier)) • finiteGaloisKernelReciprocity F L (g.comp f) hL eL x := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := extensionAlgebra E L g
  let := E.canonicalTopologicalData.topology
  let := L.canonicalTopologicalData.topology
  let := towerKernelFintype F E L f g hE
  obtain ⟨w, rfl⟩ := (finiteGaloisQuotientKernelEquiv F L (g.comp f) hL).surjective x
  obtain ⟨v, rfl⟩ :=
    (finiteGaloisAbsoluteConjugation F L (g.comp f) hL (towerCorrection F E L f g)).surjective w
  have hxy : (⟨_, hx⟩ : (finiteGaloisQuotient F E f hE).toMonoidHom.ker) =
      finiteGaloisQuotientKernelEquiv F E f hE (extensionWeilMap E L g v) := by
    apply Subtype.ext
    rw [finiteGaloisQuotientKernelEquiv_apply, finiteGaloisQuotientKernelEquiv_apply,
      extensionWeilMap_finiteGaloisAbsoluteConjugation, extensionWeilMap_comp]
  rw [hxy, finiteGaloisKernelReciprocity_apply, finiteGaloisKernelReciprocity_apply,
    reciprocityUnits_finiteGaloisAbsoluteConjugation F L (g.comp f) hL eL heL,
    reciprocityUnits_extensionWeilMap E L g eE heE eL heL, prod_towerKernel_smul F E L f g hE hL]
  congr 1
  rw [map_inv]
  congr 1
  apply Units.ext
  exact (norm_absoluteBaseConjugation_towerCorrection F E L f g hL hF1 _).symm

include hF1 heE heL in
/-- **Inflation of finite Galois Weil classes.** For a tower `F ⊂ E ⊂ L` of finite Galois
extensions, with `L → \bar F` extending `E → \bar F`, the inflation of the Weil class of `E/F`
is `[L : E]` times the Weil class of `L/F` (Tate 1979, (1.2.4)). -/
theorem relativeInflation_finiteGaloisClass_of_norm :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F L (g.comp f)
    letI := extensionAlgebra E L g
    letI : IsScalarTower F.Carrier E.Carrier L.Carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := hE
    relativeInflation F.Carrier E.Carrier L.Carrier 2 (finiteGaloisClass F E f hE eE heE) =
      Module.finrank E.Carrier L.Carrier • finiteGaloisClass F L (g.comp f) hL eL heL := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := extensionAlgebra E L g
  let _ : IsScalarTower F.Carrier E.Carrier L.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := hE
  let := hL
  let := extensionAlgebra_finiteDimensional F E f
  let := extensionAlgebra_finiteDimensional F L (g.comp f)
  let := extensionAlgebra_finiteDimensional E L g
  let := E.canonicalTopologicalData.topology
  let := L.canonicalTopologicalData.topology
  let := towerKernelFintype F E L f g hE
  have hπ : Function.Surjective (towerRestriction F E L f g hE) :=
    AlgEquiv.restrictNormalHom_surjective (F := F.Carrier) (K₁ := E.Carrier) (E := L.Carrier)
  have key := cohomologyClass_inflate_norm_of_comp (towerRestriction F E L f g hE) hπ
    (finiteGaloisSection F L (g.comp f) hL)
    (finiteGaloisKernelReciprocity F L (g.comp f) hL eL).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F L (g.comp f) hL eL heL)
    (Units.map (algebraMap E.Carrier L.Carrier).toMonoidHom)
    (unitsInflation_equivariant F.Carrier E.Carrier L.Carrier)
    (finiteGaloisQuotient F E f hE).toMonoidHom (towerRestriction_comp F E L f g hE hL hF1)
    (finiteGaloisSection F E f hE) (finiteGaloisKernelReciprocity F E f hE eE).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hE eE heE)
    (towerNorm F E L f g hE hL hF1 eE heE eL heL)
  have hcard : Fintype.card (towerRestriction F E L f g hE).ker =
      Module.finrank E.Carrier L.Carrier := by
    have h1 := Subgroup.card_mul_index (towerRestriction F E L f g hE).ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank F.Carrier E.Carrier L.Carrier, Nat.card_eq_fintype_card] at h1
    rw [mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := F.Carrier) (M := E.Carrier)) h1
  rw [← hcard]
  exact (relativeInflation_cohomologyClass F.Carrier E.Carrier L.Carrier _).trans key

end FiniteGaloisTower

end Langlands.Weil.Local
