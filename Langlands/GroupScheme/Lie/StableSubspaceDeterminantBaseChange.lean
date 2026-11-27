import Langlands.GroupScheme.Lie.StableSubspaceDeterminant
import Langlands.GroupScheme.Lie.ActionBaseChange
import Langlands.GroupScheme.Torus.WeightBaseChange

/-! # Determinant characters on stable subspaces under field extension

Let `V` be a stable subspace of `Lie(G)(k)` for `l : M ⟶ G` and `K/k` a field extension. Let
`V_K` be a subspace of `Lie(G_K)(K)` with a basis that is the image of a basis of `V` under the
scalar extension `K ⊗ Lie(G)(k) ≅ Lie(G_K)(K)`. Then `V_K` is stable for `l_K`, and the base
change of the determinant character of `M` on `V` is the determinant character of `M_K` on
`V_K`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie

set_option maxHeartbeats 800000
set_option maxRecDepth 8192

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {M : GroupScheme (Spec (CommRingCat.of k))} {l : M ⟶ G}

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "M_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) M
local notation "l_K" => CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) l

local instance stableBaseChangeAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance stableBaseChangeLocallyOfFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {V : Submodule k (Additive (lieKernel G k))}
  {VK : Submodule K (Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K))}
  {J : Type*} (bV : Module.Basis J k V) (bK : Module.Basis J K VK)

/-- The comparison of the two scalar extensions matching the two bases. -/
def extensionComparison (B : Type u) [CommRing B] [Algebra k B] [Algebra K B] :
    B ⊗[K] VK ≃ₗ[B] B ⊗[k] V :=
  (bK.baseChange B).equiv (bV.baseChange B) (Equiv.refl J)

variable {bV bK}
  (hb : ∀ j, (bK j : Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K)) =
    schemeScalarExtension (K := K) G (1 ⊗ₜ[k] (bV j : Additive (lieKernel G k))))

include hb in
/-- The comparison intertwines the two embeddings into the actual Lie kernels. -/
theorem subspaceExtension_extensionComparison (B : Type u) [CommRing B] [Algebra k B]
    [Algebra K B] [IsScalarTower k K B] (x : B ⊗[K] VK) :
    subspaceExtension G V B (extensionComparison bV bK B x) =
      kernelBaseChangeLinearEquiv k K G B (subspaceExtension G_K VK B x) := by
  have h : (subspaceExtension G V B) ∘ₗ (extensionComparison bV bK B).toLinearMap =
      (kernelBaseChangeLinearEquiv k K G B).toLinearMap ∘ₗ subspaceExtension G_K VK B := by
    apply (bK.baseChange B).ext
    intro j
    have h1 : extensionComparison bV bK B ((bK.baseChange B) j) = (bV.baseChange B) j :=
      Module.Basis.equiv_apply _ _ _ _
    have h2 : subspaceExtension G V B ((bV.baseChange B) j) =
        lieKernelMapLinear G (Algebra.ofId k B) (bV j : Additive (lieKernel G k)) := by
      rw [Module.Basis.baseChange_apply, subspaceExtension_tmul, one_smul]
    have h3 : subspaceExtension G_K VK B ((bK.baseChange B) j) =
        lieKernelMapLinear G_K (Algebra.ofId K B)
          (schemeScalarExtension (K := K) G (1 ⊗ₜ[k] (bV j : Additive (lieKernel G k)))) := by
      rw [Module.Basis.baseChange_apply, subspaceExtension_tmul, one_smul, hb]
    have h4 := schemeScalarExtension_base_naturality (K := K) (A := B) G
      (bV j : Additive (lieKernel G k))
    change subspaceExtension G V B (extensionComparison bV bK B ((bK.baseChange B) j)) =
      kernelBaseChangeLinearEquiv k K G B (subspaceExtension G_K VK B ((bK.baseChange B) j))
    rw [h1, h2, h3]
    exact h4.symm
  exact LinearMap.congr_fun h x

include hb in
/-- Stability descends to the matched subspace after base change. -/
theorem isAdjointStable_baseChange (hV : IsAdjointStable G V l) :
    IsAdjointStable G_K VK l_K := by
  intro B _ _ m x
  let : Algebra k B := Algebra.compHom B (algebraMap k K)
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨y, hy⟩ := hV B (affineBaseChangeEquiv k K M B m) (extensionComparison bV bK B x)
  refine ⟨(extensionComparison bV bK B).symm y, ?_⟩
  apply (kernelBaseChangeLinearEquiv k K G B).injective
  rw [← subspaceExtension_extensionComparison hb B, LinearEquiv.apply_symm_apply, hy,
    kernelBaseChangeLinearEquiv_adjoint, affineBaseChangeEquiv_target,
    subspaceExtension_extensionComparison hb B]

variable (hV : IsAdjointStable G V l)
  (hVK : IsAdjointStable ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) VK
    ((GroupScheme.baseChange (algebraBaseMap k K)).map l))

include hb in
/-- The comparison intertwines the induced operators. -/
theorem extensionComparison_stableOperator (B : Type u) [CommRing B] [Algebra k B]
    [Algebra K B] [IsScalarTower k K B] (m : AffinePoints M_K B) (x : B ⊗[K] VK) :
    extensionComparison bV bK B (stableOperator hVK B m x) =
      stableOperator hV B (affineBaseChangeEquiv k K M B m) (extensionComparison bV bK B x) := by
  apply subspaceExtension_injective G V B
  rw [subspaceExtension_stableOperator hV B, subspaceExtension_extensionComparison hb B,
    subspaceExtension_extensionComparison hb B, subspaceExtension_stableOperator hVK B,
    kernelBaseChangeLinearEquiv_adjoint, affineBaseChangeEquiv_target]

include hb in
/-- The induced operators have the same determinant. -/
theorem det_stableOperator_baseChange (B : Type u) [CommRing B] [Algebra k B]
    [Algebra K B] [IsScalarTower k K B] (m : AffinePoints M_K B) :
    LinearMap.det (stableOperator hVK B m) =
      LinearMap.det (stableOperator hV B (affineBaseChangeEquiv k K M B m)) := by
  rw [← LinearMap.det_conj (stableOperator hVK B m) (extensionComparison bV bK B)]
  congr 1
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [extensionComparison_stableOperator hb hV hVK B, LinearEquiv.apply_symm_apply]

variable [IsAffine M.X.left]

local instance stableBaseChangeAffineSource : IsAffine (M_K).X.left := by
  change IsAffine (pullback M.X.hom (algebraBaseMap k K))
  infer_instance

include hb in
/-- **Base change.** The base change of the determinant character on `V` is the determinant
character on the matched subspace `V_K`. -/
theorem baseChange_stableDeterminantCharacter :
    rationalCharacters.baseChange b (stableDeterminantCharacter hV) =
      stableDeterminantCharacter hVK := by
  apply rationalCharacters.ext_characterEval
  intro T x
  obtain ⟨⟨B⟩, ⟨i⟩⟩ := (essImage_algSpec (G := (M_K).X)).mpr inferInstance
  let : Algebra k B := Algebra.compHom B (algebraMap k K)
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  have hx : x = (x ≫ i.inv) ≫ i.hom := by simp
  rw [hx, characterEval_naturality, characterEval_naturality]
  congr 1
  rw [rationalCharacters.characterEval_baseChange_affine k K,
    stableDeterminantCharacter_eval_affine hV (CommAlgCat.of k B),
    stableDeterminantCharacter_eval_affine hVK]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom
      (Matrix.GeneralLinearGroup.det
        (stableMatrix hV (CommAlgCat.of k B) (affineBaseChangeEquiv k K M B i.hom))) =
    Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom
      (Matrix.GeneralLinearGroup.det (stableMatrix hVK B i.hom))
  congr 1
  apply Units.ext
  refine (stableMatrix_det hV (CommAlgCat.of k B) _).trans ?_
  refine Eq.trans ?_ (stableMatrix_det hVK B i.hom).symm
  exact (det_stableOperator_baseChange hb hV hVK B i.hom).symm

end Langlands.GroupScheme.Lie
