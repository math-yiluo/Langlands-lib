import Langlands.GroupScheme.Dynamic.RingWeightLift
import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange
import Langlands.CommutativeAlgebra.GradedLineGlobal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # The actual Lie line of a dynamic root group over a ring -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CommutativeAlgebra

/-- Maximal residue tensor fibres detect zero finite modules. -/
theorem subsingleton_of_all_maximal_tensor
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ (p : Ideal R), p.IsMaximal → Subsingleton ((R ⧸ p) ⊗[R] M)) :
    Subsingleton M := by
  apply subsingleton_of_all_maximal_smul_top (R := R)
  intro p hp
  let := h p hp
  let e := TensorProduct.quotTensorEquivQuotSMul M p
  let : Subsingleton (M ⧸ (p • (⊤ : Submodule R M))) :=
    e.symm.injective.subsingleton
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)

/-- Surjectivity onto a finite module is detected on all maximal residue tensor fibres. -/
theorem surjective_of_all_maximal_lTensor
    {R N M : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : N →ₗ[R] M)
    (h : ∀ (p : Ideal R), p.IsMaximal → Function.Surjective (f.lTensor (R ⧸ p))) :
    Function.Surjective f := by
  let Q := M ⧸ LinearMap.range f
  let q : M →ₗ[R] Q := (LinearMap.range f).mkQ
  have hQ : Subsingleton Q := by
    apply subsingleton_of_all_maximal_tensor (R := R)
    intro p hp
    have hzero : ∀ z, q.lTensor (R ⧸ p) z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := h p hp z
      have hc : (q.lTensor (R ⧸ p)).comp (f.lTensor (R ⧸ p)) = 0 := by
        apply TensorProduct.ext'
        intro r n
        change r ⊗ₜ (LinearMap.range f).mkQ (f n) = 0
        have hn : f n ∈ LinearMap.range f := ⟨n, rfl⟩
        rw [show (LinearMap.range f).mkQ (f n) = 0 from
          (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr hn,
          TensorProduct.tmul_zero]
      exact LinearMap.congr_fun hc w
    exact ⟨fun x y => by
      obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (R ⧸ p) (LinearMap.range f).mkQ_surjective x
      obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (R ⧸ p) (LinearMap.range f).mkQ_surjective y
      rw [hzero x, hzero y]⟩
  intro m
  exact (Submodule.Quotient.mk_eq_zero _).mp (hQ.elim (q m) 0)

/-- A split injection between finite modules is an equivalence if its maximal
residue tensor fibres have equal dimensions. -/
theorem bijective_of_split_of_maximal_finrank
    {R N M : Type*} [CommRing R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : N →ₗ[R] M) (g : M →ₗ[R] N) (hgf : g.comp f = LinearMap.id)
    (hdim : ∀ (p : Ideal R), p.IsMaximal →
      Module.finrank (R ⧸ p) ((R ⧸ p) ⊗[R] N) =
        Module.finrank (R ⧸ p) ((R ⧸ p) ⊗[R] M)) :
    Function.Bijective f := by
  refine ⟨Function.LeftInverse.injective (fun x => LinearMap.congr_fun hgf x), ?_⟩
  apply surjective_of_all_maximal_lTensor f
  intro p hp
  let : p.IsMaximal := hp
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have he : (g.baseChange (R ⧸ p)).comp (f.baseChange (R ⧸ p)) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_id]
  have hi : Function.Injective (f.baseChange (R ⧸ p)) :=
    Function.LeftInverse.injective fun x => LinearMap.congr_fun he x
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim p hp)).mp hi

end Langlands.CommutativeAlgebra

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu a : I → ℤ)
  [Smooth G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance affineCentralizer : IsAffineHom (Zc i mu).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

local instance affineRootGroup : IsAffineHom (Uc i mu nu).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

local instance smoothCentralizer : Smooth (Zc i mu).X.hom := by
  have := smooth_coordG (G := G)
  exact DynamicSmoothRing.smooth_centralizerScheme (centCochar i mu)

local instance smoothRootGroup : Smooth (Uc i mu nu).X.hom := smooth_Uc i mu nu

/-- The centralizer inclusion in the original group, rather than its coordinate model. -/
abbrev centralizerIncl : Zc i mu ⟶ G :=
  jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom

omit [DecidableEq I] [Smooth G.X.hom] in
theorem torusZ_centralizerIncl : torusZ i mu ≫ centralizerIncl i mu = i := by
  rw [centralizerIncl, ← Category.assoc, torusZ_comp, modelTorus,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [DecidableEq I] [Smooth G.X.hom] in
theorem centralizerIncl_represents :
    (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I mu) ≫ i)).IsRepresentedBy (centralizerIncl i mu) := by
  exact Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i)

omit [DecidableEq I] [Smooth G.X.hom] in
theorem jU_represents : (Dynamic.unipotent (unipCochar i mu nu)).IsRepresentedBy (jU i mu nu) :=
  Corepresented.isRepresentedBy_unipotentHom
    (F := cutFunctor (isCutOutBy_affineSubgroups
      (isAffineCutOutBy_centralizer (centCochar i mu))))
    (e := cutCorepresentableBy (isCutOutBy_affineSubgroups
      (isAffineCutOutBy_centralizer (centCochar i mu))))
    (unipCochar i mu nu)

/-- The root character's actual weight space is unchanged in the centralizer. -/
def centralizerRootWeightEquiv (hmu : ∑ j, a j * mu j = 0) :
    weightSpace (torusZ i mu) (splitTorus.exponentCharacter _ I a) ≃ₗ[CommRingCat.of R]
      splitTorus.exponentWeightSpace I G i a :=
  (Dynamic.centralizerWeightSpaceEquivOfCompEq (R := R) (G := G)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) (H := Zc i mu)
    (j := centralizerIncl i mu) i
    (splitTorus.exponentCocharacter _ I mu) (splitTorus.exponentCharacter _ I a)
    (centralizerIncl_represents i mu)
    (by rw [splitTorus.exponentCocharacter_comp_exponentCharacter, hmu])
    (torusZ i mu) (torusZ_centralizerIncl i mu)).trans
      (LinearEquiv.ofEq _ _
        (splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter I G i a).symm)

omit [DecidableEq I] in
theorem centralizerRootWeightEquiv_comp (hmu : ∑ j, a j * mu j = 0) :
    (splitTorus.exponentWeightSpace I G i a).subtype.comp
      (centralizerRootWeightEquiv i mu a hmu).toLinearMap =
    (Lie.targetMapLinear (centralizerIncl i mu) (CommRingCat.of R)).comp
      (weightSpace (torusZ i mu) (splitTorus.exponentCharacter _ I a)).subtype := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_coe, centralizerRootWeightEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]
  exact Dynamic.centralizerWeightSpaceEquivOfCompEq_coe
    (R := R) (G := G) (H := Zc i mu) (j := centralizerIncl i mu)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i
    (splitTorus.exponentCocharacter _ I mu) (splitTorus.exponentCharacter _ I a)
    (centralizerIncl_represents i mu)
    (by rw [splitTorus.exponentCocharacter_comp_exponentCharacter, hmu])
    (torusZ i mu) (torusZ_centralizerIncl i mu) X

/-- Lift the actual ambient root weight line into the dynamic root group's actual Lie module. -/
def rootWeightLieLift (hmu : ∑ j, a j * mu j = 0)
    (n : ℕ) (hnu : ∑ j, a j * nu j = n + 1) :
    splitTorus.exponentWeightSpace I G i a →ₗ[CommRingCat.of R]
      Additive (lieKernel (Uc i mu nu) (CommRingCat.of R)) :=
  (Dynamic.unipotentWeightLiftOfCompEq (R := R) (G := Zc i mu)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)
    (H := Uc i mu nu) (j := jU i mu nu) (torusZ i mu)
    (splitTorus.exponentCocharacter _ I nu) (splitTorus.exponentCharacter _ I a)
    (jU_represents i mu nu) n
    (by rw [splitTorus.exponentCocharacter_comp_exponentCharacter, hnu])).comp
      (centralizerRootWeightEquiv i mu a hmu).symm.toLinearMap

omit [DecidableEq I] in
theorem rootWeightLieLift_comp (hmu : ∑ j, a j * mu j = 0)
    (n : ℕ) (hnu : ∑ j, a j * nu j = n + 1)
    (X : splitTorus.exponentWeightSpace I G i a) :
    Lie.targetMapLinear (incl i mu nu) (CommRingCat.of R)
      (rootWeightLieLift i mu nu a hmu n hnu X) = X := by
  rw [show incl i mu nu = jU i mu nu ≫ centralizerIncl i mu from rfl,
    Lie.targetMapLinear_comp, LinearMap.comp_apply]
  rw [rootWeightLieLift, LinearMap.comp_apply,
    Dynamic.targetMapLinear_unipotentWeightLiftOfCompEq]
  have he := LinearMap.congr_fun (centralizerRootWeightEquiv_comp i mu a hmu)
    ((centralizerRootWeightEquiv i mu a hmu).symm X)
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using he.symm

/-- Projection of the ambient Lie algebra onto the root weight retracts its lift. -/
theorem rootWeightLieLift_split (hmu : ∑ j, a j * mu j = 0)
    (n : ℕ) (hnu : ∑ j, a j * nu j = n + 1) :
    ((splitTorus.exponentProjection I G i a).comp
      (Lie.targetMapLinear (incl i mu nu) (CommRingCat.of R))).comp
        (rootWeightLieLift i mu nu a hmu n hnu) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [rootWeightLieLift_comp i mu nu a hmu n hnu X,
    splitTorus.exponentProjection_subtype]

omit [DecidableEq I] in
/-- A field-line root-group fibre makes the corresponding scalar-extended
actual Lie module one-dimensional. -/
theorem finrank_tensor_rootLie_eq_one (K : Type u) [Field K] [Algebra R K]
    (Φ : Ga K ≅ UK i mu nu K) :
    Module.finrank K (K ⊗[R] Additive (lieKernel (Uc i mu nu) R)) = 1 := by
  let : IsAffineHom (UK i mu nu K).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
      (Uc i mu nu).X.hom (algebraBaseMap R K)))
  let : IsAffineHom (Ga K).X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  let e := (Lie.smoothSchemeScalarExtension (K := K) (Uc i mu nu)).trans
    ((Lie.targetEquiv Φ.symm K).trans (gaLieEquiv K).symm)
  rw [e.finrank_eq]
  exact Module.finrank_self K

/-- A trivial ambient root weight and field-line fibres identify the actual
root-group Lie module with that ambient root weight over the original ring. -/
theorem rootWeightLieLift_bijective (hmu : ∑ j, a j * mu j = 0)
    (n : ℕ) (hnu : ∑ j, a j * nu j = n + 1)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K], Nonempty (Ga K ≅ UK i mu nu K)) :
    Function.Bijective (rootWeightLieLift i mu nu a hmu n hnu) := by
  let : Module.Finite (CommRingCat.of R) (splitTorus.exponentWeightSpace I G i a) :=
    Module.Finite.equiv eW.symm
  let : Module.Finite (CommRingCat.of R)
      (Additive (lieKernel (Uc i mu nu) (CommRingCat.of R))) :=
    Lie.finite_lieKernel_of_smooth (Uc i mu nu)
  apply CommutativeAlgebra.bijective_of_split_of_maximal_finrank
    (rootWeightLieLift i mu nu a hmu n hnu)
    ((splitTorus.exponentProjection I G i a).comp
      (Lie.targetMapLinear (incl i mu nu) (CommRingCat.of R)))
    (rootWeightLieLift_split i mu nu a hmu n hnu)
  intro p hp
  let : p.IsMaximal := hp
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  obtain ⟨Φ⟩ := hfib (R ⧸ p)
  calc
    Module.finrank (R ⧸ p) ((R ⧸ p) ⊗[R] splitTorus.exponentWeightSpace I G i a) =
        Module.finrank (R ⧸ p) ((R ⧸ p) ⊗[R] R) :=
      (eW.baseChange (CommRingCat.of R) (R ⧸ p) _ _).finrank_eq
    _ = 1 := by
      let e : ((R ⧸ p) ⊗[R] R) ≃ₗ[R ⧸ p] (R ⧸ p) :=
        TensorProduct.AlgebraTensorModule.rid R (R ⧸ p) (R ⧸ p)
      exact e.finrank_eq.trans (Module.finrank_self _)
    _ = Module.finrank (R ⧸ p)
        ((R ⧸ p) ⊗[R] Additive (lieKernel (Uc i mu nu) R)) :=
      (finrank_tensor_rootLie_eq_one i mu nu (R ⧸ p) Φ).symm

/-- The actual ambient root weight is the actual dynamic root group's Lie line. -/
def rootWeightLieEquiv (hmu : ∑ j, a j * mu j = 0)
    (n : ℕ) (hnu : ∑ j, a j * nu j = n + 1)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K], Nonempty (Ga K ≅ UK i mu nu K)) :
    splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R]
      Additive (lieKernel (Uc i mu nu) (CommRingCat.of R)) :=
  LinearEquiv.ofBijective (rootWeightLieLift i mu nu a hmu n hnu)
    (rootWeightLieLift_bijective i mu nu a hmu n hnu eW hfib)

end Langlands.GroupScheme.LocalRootGroup
