import Langlands.Weil.Local.FiniteGaloisAbsoluteConjugation
import Langlands.Weil.Local.FiniteGaloisPushout
import Langlands.GroupTheory.ExtensionAkizukiWitt
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityStatement

/-! # Inflation of finite Galois Weil classes in a tower -/

noncomputable section

namespace Langlands.Weil.Local

universe u

open LocalClassField LocalFactor.RankOne GroupExtensionPushout
open ClassFieldTheory.Local

namespace FiniteGaloisTower

variable {p : ℕ} [Fact p.Prime] (F E L : PadicField.{u} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier) (g : E.Carrier →ₐ[Padic p] L.Carrier)

/-- The composite closure isomorphism `\bar F → \bar E → \bar L`. -/
def compositeClosureEquiv : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure L.Carrier :=
  (extensionClosureEquiv F E f).trans (extensionClosureEquiv E L g)

/-- The composite closure isomorphism lies over `g ∘ f`. -/
theorem compositeClosureEquiv_algebraMap (x : F.Carrier) :
    compositeClosureEquiv F E L f g (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x) =
      algebraMap L.Carrier (AlgebraicClosure L.Carrier) (g (f x)) := by
  change extensionClosureEquiv E L g (extensionClosureEquiv F E f
    (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)) = _
  rw [extensionClosureEquiv_apply F E f, extensionClosureLift_algebraMap,
    extensionClosureEquiv_apply E L g, extensionClosureLift_algebraMap]

/-- The correction element `κ = ε_comp⁻¹ ∘ ε_{FL}` of the absolute Galois group of `F`
comparing the direct and composite closure isomorphisms. -/
def towerCorrection : Field.absoluteGaloisGroup F.Carrier :=
  AlgEquiv.ofRingEquiv
    (f := (extensionClosureEquiv F L (g.comp f)).trans (compositeClosureEquiv F E L f g).symm)
    (fun x => by
      change (compositeClosureEquiv F E L f g).symm (extensionClosureEquiv F L (g.comp f)
        (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)) = _
      rw [extensionClosureEquiv_apply, extensionClosureLift_algebraMap,
        RingEquiv.symm_apply_eq, compositeClosureEquiv_algebraMap]
      rfl)

/-- The correction composed with the composite isomorphism is the direct isomorphism. -/
theorem compositeClosureEquiv_towerCorrection (x : AlgebraicClosure F.Carrier) :
    compositeClosureEquiv F E L f g (AlgEquiv.toAlgHom (towerCorrection F E L f g) x) =
      extensionClosureEquiv F L (g.comp f) x := by
  change compositeClosureEquiv F E L f g ((compositeClosureEquiv F E L f g).symm
    (extensionClosureEquiv F L (g.comp f) x)) = _
  rw [RingEquiv.apply_symm_apply]

/-- The composite Galois map is the direct one conjugated by the correction. -/
theorem extensionGaloisMap_comp (σ : Field.absoluteGaloisGroup L.Carrier) :
    extensionGaloisMap F E f (extensionGaloisMap E L g σ) =
      towerCorrection F E L f g * extensionGaloisMap F L (g.comp f) σ *
        (towerCorrection F E L f g)⁻¹ := by
  apply AlgEquiv.ext
  intro x
  apply (compositeClosureEquiv F E L f g).injective
  obtain ⟨y, rfl⟩ := (towerCorrection F E L f g).surjective x
  change compositeClosureEquiv F E L f g (AlgEquiv.toAlgHom (extensionGaloisMap F E f
      (extensionGaloisMap E L g σ)) (AlgEquiv.toAlgHom (towerCorrection F E L f g) y)) =
    compositeClosureEquiv F E L f g (AlgEquiv.toAlgHom (towerCorrection F E L f g)
      (AlgEquiv.toAlgHom (extensionGaloisMap F L (g.comp f) σ)
        (AlgEquiv.toAlgHom ((towerCorrection F E L f g)⁻¹ * towerCorrection F E L f g) y)))
  rw [inv_mul_cancel, compositeClosureEquiv_towerCorrection]
  change extensionClosureEquiv E L g (extensionClosureEquiv F E f
      (AlgEquiv.toAlgHom (extensionGaloisMap F E f (extensionGaloisMap E L g σ))
        (AlgEquiv.toAlgHom (towerCorrection F E L f g) y))) =
    extensionClosureEquiv F L (g.comp f) (AlgEquiv.toAlgHom (extensionGaloisMap F L (g.comp f) σ) y)
  rw [extensionClosureEquiv_apply F E f, extensionClosureLift_galoisMap,
    extensionClosureEquiv_apply E L g, extensionClosureLift_galoisMap,
    extensionClosureEquiv_apply F L (g.comp f), extensionClosureLift_galoisMap]
  congr 1
  rw [← extensionClosureEquiv_apply E L g, ← extensionClosureEquiv_apply F E f,
    ← extensionClosureEquiv_apply F L (g.comp f)]
  exact compositeClosureEquiv_towerCorrection F E L f g y

/-- The composite Weil map is the direct one conjugated by the correction. -/
theorem extensionWeilMap_comp (y : localWeilGroup L) :
    extensionWeilMap F E f (extensionWeilMap E L g y) =
      galoisConjugationWeil F (towerCorrection F E L f g) (extensionWeilMap F L (g.comp f) y) := by
  apply Subtype.ext
  apply Prod.ext
  · exact extensionGaloisMap_comp F E L f g (localProjection L y)
  · apply frobenius_injective
    have h1 := (extensionWeilMap F E f (extensionWeilMap E L g y)).property
    have h2 := (galoisConjugationWeil F (towerCorrection F E L f g)
      (extensionWeilMap F L (g.comp f) y)).property
    have he : (extensionWeilMap F E f (extensionWeilMap E L g y)).val.1 =
        (galoisConjugationWeil F (towerCorrection F E L f g)
          (extensionWeilMap F L (g.comp f) y)).val.1 :=
      extensionGaloisMap_comp F E L f g (localProjection L y)
    change localResidueDegree F (extensionWeilMap F E f (extensionWeilMap E L g y)).val.1 =
      frobenius (extensionWeilMap F E f (extensionWeilMap E L g y)).val.2 at h1
    change localResidueDegree F (galoisConjugationWeil F (towerCorrection F E L f g)
        (extensionWeilMap F L (g.comp f) y)).val.1 =
      frobenius (galoisConjugationWeil F (towerCorrection F E L f g)
        (extensionWeilMap F L (g.comp f) y)).val.2 at h2
    rw [← h1, ← h2, he]

section Inflation

variable (K Lf Mf : Type u) [Field K] [Field Lf] [Field Mf] [Algebra K Lf] [Algebra K Mf]
  [Algebra Lf Mf] [IsScalarTower K Lf Mf] [Normal K Lf]

/-- The unit inclusion is equivariant along normal restriction. -/
theorem unitsInflation_equivariant (σ : Gal(Mf/K)) (b : Lfˣ) :
    Units.map (algebraMap Lf Mf).toMonoidHom (AlgEquiv.restrictNormalHom Lf σ • b) =
      σ • Units.map (algebraMap Lf Mf).toMonoidHom b := by
  apply Units.ext
  exact AlgEquiv.restrictNormal_commutes σ Lf (b : Lf)

/-- Actual inflation of the class of a normalized unit cocycle is the class of the inflated
cocycle. -/
theorem relativeInflation_cohomologyClass (c : NormalizedTwoCocycle Gal(Lf/K) Lfˣ) :
    relativeInflation K Lf Mf 2 (NormalizedTwoCocycle.cohomologyClass c) =
      NormalizedTwoCocycle.cohomologyClass (NormalizedTwoCocycle.inflate
        (AlgEquiv.restrictNormalHom Lf) (Units.map (algebraMap Lf Mf).toMonoidHom)
        (unitsInflation_equivariant K Lf Mf) c) := by
  exact groupCohomology.H2π_comp_map_apply (AlgEquiv.restrictNormalHom Lf)
    (inflationCoefficients K Lf Mf)
    (show groupCohomology.cocycles₂ (unitsRepresentation K Lf) from
      NormalizedTwoCocycle.toCocycle₂ c)

end Inflation

section Galois

variable (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
  (hL : letI := extensionAlgebra F L (g.comp f); IsGalois F.Carrier L.Carrier)
  (hF1 : ∀ x : E.Carrier,
    extensionFieldEmbedding F L (g.comp f) (g x) = extensionFieldEmbedding F E f x)

include hF1 in
/-- The correction fixes the image of `E` in `\bar F`. -/
theorem towerCorrection_fieldEmbedding (x : E.Carrier) :
    AlgEquiv.toAlgHom (towerCorrection F E L f g) (extensionFieldEmbedding F E f x) =
      extensionFieldEmbedding F E f x := by
  apply (compositeClosureEquiv F E L f g).injective
  rw [compositeClosureEquiv_towerCorrection]
  calc extensionClosureEquiv F L (g.comp f) (extensionFieldEmbedding F E f x)
      = extensionClosureEquiv F L (g.comp f) (extensionFieldEmbedding F L (g.comp f) (g x)) := by
        rw [hF1]
    _ = algebraMap L.Carrier (AlgebraicClosure L.Carrier) (g x) := by
        rw [extensionClosureEquiv_apply, extensionClosureLift_fieldEmbedding]
    _ = compositeClosureEquiv F E L f g (extensionFieldEmbedding F E f x) := by
        change _ = extensionClosureEquiv E L g
          (extensionClosureEquiv F E f (extensionFieldEmbedding F E f x))
        rw [extensionClosureEquiv_apply F E f, extensionClosureLift_fieldEmbedding,
          extensionClosureEquiv_apply, extensionClosureLift_algebraMap]

/-- Restriction `Gal(L/F) → Gal(E/F)` along `g`. -/
def towerRestriction :
    (letI := extensionAlgebra F L (g.comp f); Gal(L.Carrier/F.Carrier)) →*
      (letI := extensionAlgebra F E f; Gal(E.Carrier/F.Carrier)) := by
  letI := extensionAlgebra F E f
  letI := extensionAlgebra F L (g.comp f)
  letI := extensionAlgebra E L g
  letI : IsScalarTower F.Carrier E.Carrier L.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := hE
  exact AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := L.Carrier) E.Carrier

/-- Restriction is compatible with `g`. -/
theorem towerRestriction_apply
    (σ : letI := extensionAlgebra F L (g.comp f); Gal(L.Carrier/F.Carrier)) (x : E.Carrier) :
    g (towerRestriction F E L f g hE σ x) = σ (g x) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := extensionAlgebra E L g
  let _ : IsScalarTower F.Carrier E.Carrier L.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := hE
  exact AlgEquiv.restrictNormal_commutes σ E.Carrier x

include hF1 in
/-- Restriction of the `L`-quotient is the `E`-quotient. -/
theorem towerRestriction_finiteGaloisQuotient (x : localWeilGroup F) :
    towerRestriction F E L f g hE (finiteGaloisQuotient F L (g.comp f) hL x) =
      finiteGaloisQuotient F E f hE x := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  apply AlgEquiv.ext
  intro z
  apply (extensionFieldEmbedding F E f).injective
  calc extensionFieldEmbedding F E f
        (towerRestriction F E L f g hE (finiteGaloisQuotient F L (g.comp f) hL x) z)
      = extensionFieldEmbedding F L (g.comp f)
          (g (towerRestriction F E L f g hE (finiteGaloisQuotient F L (g.comp f) hL x) z)) :=
        (hF1 _).symm
    _ = extensionFieldEmbedding F L (g.comp f) (finiteGaloisQuotient F L (g.comp f) hL x (g z)) := by
        rw [towerRestriction_apply]
    _ = AlgEquiv.toAlgHom (localProjection F x) (extensionFieldEmbedding F L (g.comp f) (g z)) :=
        finiteGaloisQuotient_apply F L (g.comp f) hL x (g z)
    _ = AlgEquiv.toAlgHom (localProjection F x) (extensionFieldEmbedding F E f z) := by
        rw [hF1]
    _ = extensionFieldEmbedding F E f (finiteGaloisQuotient F E f hE x z) :=
        (finiteGaloisQuotient_apply F E f hE x z).symm

include hF1 in
/-- The same identity as homomorphisms. -/
theorem towerRestriction_comp :
    (towerRestriction F E L f g hE).comp
        (letI := extensionAlgebra F L (g.comp f); (finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom) =
      (letI := extensionAlgebra F E f; (finiteGaloisQuotient F E f hE).toMonoidHom) :=
  MonoidHom.ext (towerRestriction_finiteGaloisQuotient F E L f g hE hL hF1)

include hF1 in
/-- The finite Galois element lies in the kernel of the tower restriction. -/
theorem finiteGaloisQuotient_extensionWeilMap_mem (y : localWeilGroup E) :
    finiteGaloisQuotient F L (g.comp f) hL (extensionWeilMap F E f y) ∈
      (towerRestriction F E L f g hE).ker := by
  let := extensionAlgebra F E f
  rw [MonoidHom.mem_ker, towerRestriction_finiteGaloisQuotient F E L f g hE hL hF1]
  exact (finiteGaloisQuotientKernelEquiv F E f hE y).property

/-- The quotient `W_E → Gal(L/E)` used to compute the transfer to `W_L`. -/
def towerKernelQuotient : localWeilGroup E →* (towerRestriction F E L f g hE).ker :=
  ((letI := extensionAlgebra F L (g.comp f);
      (finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom).comp
    (extensionWeilMap F E f).toMonoidHom).codRestrict _
    (finiteGaloisQuotient_extensionWeilMap_mem F E L f g hE hL hF1)

/-- The value of the transfer quotient. -/
@[simp] theorem towerKernelQuotient_coe (y : localWeilGroup E) :
    (towerKernelQuotient F E L f g hE hL hF1 y :
      (letI := extensionAlgebra F L (g.comp f); Gal(L.Carrier/F.Carrier))) =
      finiteGaloisQuotient F L (g.comp f) hL (extensionWeilMap F E f y) := rfl

/-- The kernel of the transfer quotient is the image of `W_L`. -/
theorem towerKernelQuotient_ker :
    (towerKernelQuotient F E L f g hE hL hF1).ker = (extensionWeilMap E L g).toMonoidHom.range := by
  let := extensionAlgebra F L (g.comp f)
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hy
    have h1 : extensionWeilMap F E f y ∈ (finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hy
    have h2 := galoisConjugationWeil_mem_ker F L (g.comp f) hL (towerCorrection F E L f g)⁻¹ _ h1
    rw [finiteGaloisQuotient_ker] at h2
    obtain ⟨z, hz⟩ := h2
    refine ⟨z, ?_⟩
    apply extensionWeilMap_injective F E f
    change extensionWeilMap F E f (extensionWeilMap E L g z) = _
    rw [extensionWeilMap_comp]
    rw [show extensionWeilMap F L (g.comp f) z = _ from hz]
    exact (galoisConjugationWeil F (towerCorrection F E L f g)).apply_symm_apply _
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    change finiteGaloisQuotient F L (g.comp f) hL
      (extensionWeilMap F E f (extensionWeilMap E L g z)) = 1
    rw [extensionWeilMap_comp]
    exact galoisConjugationWeil_mem_ker F L (g.comp f) hL (towerCorrection F E L f g) _
      (finiteGaloisQuotientKernelEquiv F L (g.comp f) hL z).property

include hF1 in
/-- A section value over the kernel of the tower restriction lies in the `E`-kernel. -/
theorem finiteGaloisSection_mem (h : (towerRestriction F E L f g hE).ker) :
    (letI := extensionAlgebra F L (g.comp f); finiteGaloisSection F L (g.comp f) hL (h : _)) ∈
      (letI := extensionAlgebra F E f; (finiteGaloisQuotient F E f hE).toMonoidHom.ker) := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  rw [MonoidHom.mem_ker]
  change finiteGaloisQuotient F E f hE (finiteGaloisSection F L (g.comp f) hL h) = 1
  rw [← towerRestriction_finiteGaloisQuotient F E L f g hE hL hF1]
  change towerRestriction F E L f g hE
    ((finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom (finiteGaloisSection F L (g.comp f) hL h)) = 1
  rw [Section.map_apply]
  exact h.property

/-- The section of the transfer quotient. -/
def towerKernelSection (h : (towerRestriction F E L f g hE).ker) : localWeilGroup E :=
  (letI := extensionAlgebra F E f; finiteGaloisQuotientKernelEquiv F E f hE).symm
    ⟨_, finiteGaloisSection_mem F E L f g hE hL hF1 h⟩

/-- The section values in `W_F` are the section values of the `L`-quotient. -/
theorem extensionWeilMap_towerKernelSection (h : (towerRestriction F E L f g hE).ker) :
    extensionWeilMap F E f (towerKernelSection F E L f g hE hL hF1 h) =
      (letI := extensionAlgebra F L (g.comp f); finiteGaloisSection F L (g.comp f) hL (h : _)) := by
  let := extensionAlgebra F E f
  exact extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm F E f hE _

/-- The section is a section of the transfer quotient. -/
theorem towerKernelQuotient_towerKernelSection (h : (towerRestriction F E L f g hE).ker) :
    towerKernelQuotient F E L f g hE hL hF1 (towerKernelSection F E L f g hE hL hF1 h) = h := by
  let := extensionAlgebra F L (g.comp f)
  apply Subtype.ext
  rw [towerKernelQuotient_coe, extensionWeilMap_towerKernelSection]
  exact Section.map_apply _ _

/-- The finite kernel of the tower restriction. -/
@[instance_reducible]
def towerKernelFintype : Fintype (towerRestriction F E L f g hE).ker := by
  letI := extensionAlgebra F L (g.comp f)
  letI := extensionAlgebra_finiteDimensional F L (g.comp f)
  exact Fintype.ofFinite _

include hF1 in
/-- The correction acts trivially on the image of `E` in `L`. -/
theorem absoluteBaseConjugation_towerCorrection (z : E.Carrier) :
    absoluteBaseConjugation F L (g.comp f) hL (towerCorrection F E L f g) (g z) = g z := by
  let := extensionAlgebra F L (g.comp f)
  apply (extensionFieldEmbedding F L (g.comp f)).injective
  change extensionFieldEmbedding F L (g.comp f)
    (finiteGaloisRestriction F L (g.comp f) hL (towerCorrection F E L f g) (g z)) = _
  rw [finiteGaloisRestriction_apply, hF1, towerCorrection_fieldEmbedding F E L f g hF1]

/-- The transfer factor `t(h) x t(h q(x))⁻¹` lies in the kernel. -/
theorem transferFactor_mem {W G : Type*} [Group W] [Group G] {q : W →* G}
    (t : Section q) (x : W) (h : G) : t h * x * (t (h * q x))⁻¹ ∈ q.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, Section.map_apply, Section.map_apply,
    mul_inv_cancel]

/-- `cohomologyClass_inflate_pushout` for a quotient map `q'` that equals `π ∘ q`. -/
theorem cohomologyClass_inflate_pushout_of_comp {W : Type*} {G A Q B : Type u} [Group W] [Group G]
    [CommGroup A] [MulDistribMulAction G A] [Group Q] [CommGroup B] [MulDistribMulAction Q B]
    {q : W →* G} (π : G →* Q) [Fintype π.ker] (hπ : Function.Surjective π) (t : Section q)
    (r : q.ker →* A) (hr : ∀ (x : W) (n : q.ker), r (conjugateKernel q x n) = q x • r n)
    (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b) (q' : W →* Q) (hq' : π.comp q = q')
    (s : Section q') (r' : q'.ker →* B)
    (hr' : ∀ (x : W) (n : q'.ker), r' (conjugateKernel q' x n) = q' x • r' n)
    (hV : ∀ x : q'.ker, ι (r' x) = ∏ h : π.ker, r ⟨_, transferFactor_mem t x h⟩) :
    NormalizedTwoCocycle.cohomologyClass
        (NormalizedTwoCocycle.inflate π ι hι (s.cocycle r' hr')) =
      Fintype.card π.ker • NormalizedTwoCocycle.cohomologyClass (t.cocycle r hr) := by
  subst hq'
  exact cohomologyClass_inflate_pushout π t r hr hπ ι hι s r' hr' hV

variable (eE : ReciprocityCandidate E)
  (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
  (eL : ReciprocityCandidate L)
  (heL : GeometricWeilReciprocityRelation L L.canonicalTopologicalData eL)

/-- The factors of the transfer quotient section lie in the image of `W_L`. -/
theorem towerTransferFactor_mem (x : localWeilGroup E) (h : (towerRestriction F E L f g hE).ker) :
    towerKernelSection F E L f g hE hL hF1 h * x *
        (towerKernelSection F E L f g hE hL hF1 (h * towerKernelQuotient F E L f g hE hL hF1 x))⁻¹ ∈
      (extensionWeilMap E L g).toMonoidHom.range := by
  rw [← towerKernelQuotient_ker F E L f g hE hL hF1, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
    towerKernelQuotient_towerKernelSection, towerKernelQuotient_towerKernelSection, mul_inv_cancel]

include hF1 heL in
/-- One factor of the transfer: the direct and composite identifications of `W_L`
differ by the correction, which acts trivially after reciprocity up to `κ|_L`. -/
theorem transferFactor_reciprocity (x : localWeilGroup E) (h : (towerRestriction F E L f g hE).ker)
    (hz : towerKernelSection F E L f g hE hL hF1 h * x *
        (towerKernelSection F E L f g hE hL hF1 (h * towerKernelQuotient F E L f g hE hL hF1 x))⁻¹ ∈
      (extensionWeilMap E L g).toMonoidHom.range) :
    letI := extensionAlgebra F L (g.comp f)
    letI := L.canonicalTopologicalData.topology
    finiteGaloisKernelReciprocity F L (g.comp f) hL eL
        ⟨_, transferFactor_mem (finiteGaloisSection F L (g.comp f) hL) (extensionWeilMap F E f x) h⟩ =
      (Units.mapEquiv (absoluteBaseConjugation F L (g.comp f) hL
          (towerCorrection F E L f g)).toMulEquiv
        (reciprocityUnits L eL (InductionAlong.rangeInverse (extensionWeilMap E L g).toMonoidHom
          (extensionWeilMap_injective E L g) ⟨_, hz⟩)))⁻¹ := by
  let := extensionAlgebra F L (g.comp f)
  let := L.canonicalTopologicalData.topology
  set w := InductionAlong.rangeInverse (extensionWeilMap E L g).toMonoidHom
    (extensionWeilMap_injective E L g) ⟨_, hz⟩ with hw
  have hwz : extensionWeilMap E L g w = _ :=
    InductionAlong.apply_rangeInverse (extensionWeilMap E L g).toMonoidHom
      (extensionWeilMap_injective E L g) ⟨_, hz⟩
  have hkey : (⟨_, transferFactor_mem (finiteGaloisSection F L (g.comp f) hL)
      (extensionWeilMap F E f x) h⟩ : (finiteGaloisQuotient F L (g.comp f) hL).toMonoidHom.ker) =
      finiteGaloisQuotientKernelEquiv F L (g.comp f) hL
        (finiteGaloisAbsoluteConjugation F L (g.comp f) hL (towerCorrection F E L f g) w) := by
    apply Subtype.ext
    rw [finiteGaloisQuotientKernelEquiv_apply, extensionWeilMap_finiteGaloisAbsoluteConjugation,
      ← extensionWeilMap_comp, hwz, map_mul, map_mul, map_inv,
      extensionWeilMap_towerKernelSection, extensionWeilMap_towerKernelSection]
    rfl
  rw [hkey, finiteGaloisKernelReciprocity_apply,
    reciprocityUnits_finiteGaloisAbsoluteConjugation F L (g.comp f) hL eL heL]

variable (hT : ExtensionWeilTransferReciprocityStatement.{u, u})

include hF1 heE heL hT in
/-- The transfer–inclusion square of `E ⊂ L` in kernel coordinates: the inverse reciprocity
of `E` followed by `E → L` is the coset product of the inverse reciprocity of `L`. -/
theorem towerTransfer (y : localWeilGroup E) :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F L (g.comp f)
    letI := E.canonicalTopologicalData.topology
    letI := L.canonicalTopologicalData.topology
    letI := towerKernelFintype F E L f g hE
    Units.map g.toRingHom.toMonoidHom
        (finiteGaloisKernelReciprocity F E f hE eE (finiteGaloisQuotientKernelEquiv F E f hE y)) =
      ∏ h : (towerRestriction F E L f g hE).ker,
        finiteGaloisKernelReciprocity F L (g.comp f) hL eL
          ⟨_, transferFactor_mem (finiteGaloisSection F L (g.comp f) hL)
            (extensionWeilMap F E f y) h⟩ := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := E.canonicalTopologicalData.topology
  let := L.canonicalTopologicalData.topology
  let := towerKernelFintype F E L f g hE
  have hW := hT p E L g eE eL heE heL y
  rw [transfer_eq_prod_section _ (towerKernelQuotient F E L f g hE hL hF1)
    (towerKernelQuotient_ker F E L f g hE hL hF1) (towerKernelSection F E L f g hE hL hF1)
    (towerKernelQuotient_towerKernelSection F E L f g hE hL hF1) y] at hW
  rw [finiteGaloisKernelReciprocity_apply,
    Finset.prod_congr rfl (fun h _ => transferFactor_reciprocity F E L f g hE hL hF1 eL heL y h
      (towerTransferFactor_mem F E L f g hE hL hF1 y h)),
    Finset.prod_inv_distrib, ← map_prod]
  change _ = ((Units.mapEquiv _) (∏ h : (towerRestriction F E L f g hE).ker,
    ((reciprocityUnits L eL).toMonoidHom.comp (InductionAlong.rangeInverse
      (extensionWeilMap E L g).toMonoidHom (extensionWeilMap_injective E L g))) _))⁻¹
  rw [hW, map_inv]
  congr 1
  apply Units.ext
  exact (absoluteBaseConjugation_towerCorrection F E L f g hL hF1 _).symm

include hF1 heE heL hT in
/-- **Inflation of finite Galois Weil classes.** For a tower `F ⊂ E ⊂ L` of finite Galois
extensions, with `L → \bar F` extending `E → \bar F`, and the transfer–inclusion square
of geometric reciprocity for `E ⊂ L`, the inflation of the Weil class of `E/F` is
`[L : E]` times the Weil class of `L/F` (Tate 1979, (1.2.4)). -/
theorem relativeInflation_finiteGaloisClass :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F L (g.comp f)
    letI := extensionAlgebra E L g
    letI : IsScalarTower F.Carrier E.Carrier L.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := hE
    relativeInflation F.Carrier E.Carrier L.Carrier 2 (finiteGaloisClass F E f hE eE heE) =
      Module.finrank E.Carrier L.Carrier • finiteGaloisClass F L (g.comp f) hL eL heL := by
  let := extensionAlgebra F E f
  let := extensionAlgebra F L (g.comp f)
  let := extensionAlgebra E L g
  let _ : IsScalarTower F.Carrier E.Carrier L.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
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
  have hV : ∀ x : (finiteGaloisQuotient F E f hE).toMonoidHom.ker,
      Units.map (algebraMap E.Carrier L.Carrier).toMonoidHom
          ((finiteGaloisKernelReciprocity F E f hE eE).toMonoidHom x) =
        ∏ h : (towerRestriction F E L f g hE).ker,
          (finiteGaloisKernelReciprocity F L (g.comp f) hL eL).toMonoidHom
            ⟨_, transferFactor_mem (finiteGaloisSection F L (g.comp f) hL) x h⟩ := by
    intro x
    obtain ⟨y, rfl⟩ := (finiteGaloisQuotientKernelEquiv F E f hE).surjective x
    exact towerTransfer F E L f g hE hL hF1 eE heE eL heL hT y
  have key := cohomologyClass_inflate_pushout_of_comp (towerRestriction F E L f g hE) hπ
    (finiteGaloisSection F L (g.comp f) hL)
    (finiteGaloisKernelReciprocity F L (g.comp f) hL eL).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F L (g.comp f) hL eL heL)
    (Units.map (algebraMap E.Carrier L.Carrier).toMonoidHom)
    (unitsInflation_equivariant F.Carrier E.Carrier L.Carrier)
    (finiteGaloisQuotient F E f hE).toMonoidHom (towerRestriction_comp F E L f g hE hL hF1)
    (finiteGaloisSection F E f hE) (finiteGaloisKernelReciprocity F E f hE eE).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hE eE heE) hV
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

end Galois


end FiniteGaloisTower

end Langlands.Weil.Local
