import Langlands.AlgebraicGeometry.LocalFreeChartPullback
import Langlands.AlgebraicGeometry.LocalSectionDeterminant
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- Evaluate a local morphism from the structure module at the unit section. -/
def localUnitSection (M : Y.Modules) (U : Y.Opens) :
    LocalHom (SheafOfModules.unit Y.ringCatSheaf) M U →ₗ[Γ(Y, U)] Γ(M, U) where
  toFun t := LocalHom.app t (𝟙 U) (1 : Γ(Y, U))
  map_add' _ _ := rfl
  map_smul' r t := by
    change Y.presheaf.map (𝟙 U).op r • LocalHom.app t (𝟙 U) (1 : Γ(Y, U)) =
      r • LocalHom.app t (𝟙 U) (1 : Γ(Y, U))
    simp

/-- A local map from the structure module is multiplication by its unit section. -/
lemma localUnitSection_app {M : Y.Modules} {U : Y.Opens}
    (t : LocalHom (SheafOfModules.unit Y.ringCatSheaf) M U)
    (V : Over U) (r : Γ(Y, V.left)) :
    t.val.app (op V) r = r • M.presheaf.map V.hom.op (localUnitSection M U t) := by
  have hn := PresheafOfModules.naturality_apply t.val
    (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (1 : Γ(Y, U))
  change t.val.app (op V) (Y.presheaf.map V.hom.op 1) =
    M.presheaf.map V.hom.op (localUnitSection M U t) at hn
  rw [map_one] at hn
  rw [← hn]
  simpa only [smul_eq_mul, mul_one] using
    (t.val.app (op V)).hom.map_smul r (1 : Γ(Y, V.left))

/-- The value on the unit section over the chart determines a local map from the unit. -/
lemma localUnitSection_injective (M : Y.Modules) (U : Y.Opens) :
    Function.Injective (localUnitSection M U) := by
  intro t s h
  apply LocalHom.ext
  intro V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change t.val.app (op (Over.mk i)) r = s.val.app (op (Over.mk i)) r
  rw [localUnitSection_app, localUnitSection_app, h]

/-- Postcomposition acts on the value of a local morphism at the unit section. -/
lemma localUnitSection_comp {M N : Y.Modules} {U : Y.Opens}
    (t : LocalHom (SheafOfModules.unit Y.ringCatSheaf) M U) (h : LocalHom M N U) :
    localUnitSection N U (t ≫ h) = LocalHom.app h (𝟙 U) (localUnitSection M U t) := rfl

/-- Pullback preserves composition of arbitrary local module morphisms. -/
lemma localHomPullback_comp (f : X ⟶ Y) (U : Y.Opens) {M N P : Y.Modules}
    (h : LocalHom M N U) (k : LocalHom N P U) :
    localHomPullback f U (h ≫ k) = localHomPullback f U h ≫ localHomPullback f U k := by
  rw [← cancel_epi (chartPullbackIso f U M).hom]
  rw [← chartPullbackIso_naturality, Functor.map_comp, Category.assoc,
    chartPullbackIso_naturality, ← Category.assoc, chartPullbackIso_naturality,
    Category.assoc]

/-- Pullback of local morphisms preserves finite sums. -/
lemma localHomPullback_sum (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules}
    {J : Type*} (s : Finset J) (h : J → LocalHom M N U) :
    localHomPullback f U (∑ j ∈ s, h j) = ∑ j ∈ s, localHomPullback f U (h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp only [Finset.sum_insert hj, localHomPullback_add, ih]

variable {I : Type u} [Fintype I] {M : Y.Modules} {U : Y.Opens}

local instance localChartDeterminantDecidableEq : DecidableEq I := Classical.decEq I

/-- The chart generators, evaluated on the unit, are exactly its section basis. -/
lemma localUnitSection_generator
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U) (i : I) :
    localUnitSection M U (SheafOfModules.ιFree i ≫ e.hom) =
      localSectionBasis e (Over.mk (𝟙 U)) i := by
  rw [localSectionBasis_apply]
  rfl

/-- Evaluating a chart generator followed by an endomorphism gives its action on the basis. -/
lemma localUnitSection_generator_comp
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : End (M.over U)) (j : I) :
    localUnitSection M U (SheafOfModules.ιFree j ≫ e.hom ≫ a) =
      localSectionEndomorphism M (Over.mk (𝟙 U)) a
        (localSectionBasis e (Over.mk (𝟙 U)) j) := by
  change LocalHom.app a (𝟙 U)
    (localUnitSection M U (SheafOfModules.ιFree j ≫ e.hom)) = _
  rw [localUnitSection_generator]
  rfl

/-- Expansion of an endomorphism on each generator as an equality of local sheaf maps. -/
lemma localSectionBasis_generator_matrix
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : End (M.over U)) (j : I) :
    SheafOfModules.ιFree j ≫ e.hom ≫ a =
      ∑ i, (show Γ(Y, U) from LinearMap.toMatrix (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionEndomorphism M (Over.mk (𝟙 U)) a) i j) •
          (show LocalHom (SheafOfModules.unit Y.ringCatSheaf) M U from
            SheafOfModules.ιFree i ≫ e.hom) := by
  apply localUnitSection_injective M U
  rw [map_sum]
  simp only [map_smul, localUnitSection_generator, LinearMap.toMatrix_apply]
  change LocalHom.app a (𝟙 U)
      (localUnitSection M U (SheafOfModules.ιFree j ≫ e.hom)) = _
  rw [localUnitSection_generator]
  exact ((localSectionBasis e (Over.mk (𝟙 U))).sum_repr _).symm

/-- Precomposition preserves the scalar action on local morphisms. -/
lemma localHom_comp_smul {L N : Y.Modules} (g : LocalHom L M U)
    (r : Γ(Y, U)) (h : LocalHom M N U) :
    g ≫ (r • h) = r • (g ≫ h) := by
  apply LocalHom.ext
  intro V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The source generator expansion transports through the actual pullback chart. -/
lemma chartFreePullbackIso_generator_matrix (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : End (M.over U)) (j : I) :
    SheafOfModules.ιFree j ≫ (chartFreePullbackIso f U e).hom ≫
        localHomPullback f U a =
      ∑ i, (f.app U (LinearMap.toMatrix (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionEndomorphism M (Over.mk (𝟙 U)) a) i j)) •
          (show LocalHom (SheafOfModules.unit X.ringCatSheaf)
            ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) from
              SheafOfModules.ιFree i ≫ (chartFreePullbackIso f U e).hom) := by
  rw [chartFreePullbackIso_generator_assoc, ← localHomPullback_comp,
    Category.assoc, localSectionBasis_generator_matrix, localHomPullback_sum,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let c : Γ(Y, U) := LinearMap.toMatrix (localSectionBasis e (Over.mk (𝟙 U)))
    (localSectionBasis e (Over.mk (𝟙 U)))
    (localSectionEndomorphism M (Over.mk (𝟙 U)) a) i j
  let α : LocalHom (SheafOfModules.unit Y.ringCatSheaf) M U :=
    SheafOfModules.ιFree i ≫ e.hom
  let β : LocalHom (SheafOfModules.unit X.ringCatSheaf)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) :=
    SheafOfModules.ιFree i ≫ (chartFreePullbackIso f U e).hom
  change (pullbackUnitIso f).inv.over (f ⁻¹ᵁ U) ≫ localHomPullback f U (c • α) =
    f.app U c • β
  rw [localHomPullback_smul f (SheafOfModules.unit Y.ringCatSheaf) M U c α,
    localHom_comp_smul]
  exact congrArg (fun t : LocalHom (SheafOfModules.unit X.ringCatSheaf)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) => f.app U c • t)
    (chartFreePullbackIso_generator f U e i).symm

/-- The matrix in the constructed pullback chart is the image of the actual source matrix. -/
theorem localSectionEndomorphism_toMatrix_pullback_top (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : End (M.over U)) :
    LinearMap.toMatrix
        (localSectionBasis (chartFreePullbackIso f U e) (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (localSectionBasis (chartFreePullbackIso f U e) (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (localSectionEndomorphism ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          (Over.mk (𝟙 (f ⁻¹ᵁ U))) (localHomPullback f U a)) =
      (LinearMap.toMatrix (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionBasis e (Over.mk (𝟙 U)))
        (localSectionEndomorphism M (Over.mk (𝟙 U)) a)).map (f.app U) := by
  apply Matrix.ext
  intro i j
  have h := congrArg
    (localUnitSection ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U))
    (chartFreePullbackIso_generator_matrix f e a j)
  rw [map_sum] at h
  simp only [map_smul, localUnitSection_generator, localUnitSection_generator_comp] at h
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
  rw [h]
  rw [Module.Basis.repr_sum_self]
  rfl

/-- The constructed chart transports endomorphism matrices on every inverse-image open. -/
theorem localSectionEndomorphism_toMatrix_pullback (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : End (M.over U)) (V : Over U) :
    LinearMap.toMatrix
        (localSectionBasis (chartFreePullbackIso f U e)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)))
        (localSectionBasis (chartFreePullbackIso f U e)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)))
        (localSectionEndomorphism ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom))
          (localHomPullback f U a)) =
      (LinearMap.toMatrix (localSectionBasis e V) (localSectionBasis e V)
        (localSectionEndomorphism M V a)).map (f.app V.left) := by
  apply Matrix.ext
  intro i j
  let js : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom
  let jt : Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom) ⟶
      Over.mk (𝟙 (f ⁻¹ᵁ U)) :=
    Over.homMk ((TopologicalSpace.Opens.map f.base).map V.hom)
  have h := congrArg (fun A => A i j) (localSectionEndomorphism_toMatrix_pullback_top f e a)
  simp only [Matrix.map_apply] at h ⊢
  rw [localSectionEndomorphism_toMatrix_restrict (chartFreePullbackIso f U e) jt,
    localSectionEndomorphism_toMatrix_restrict e js, h]
  exact (ConcreteCategory.congr_hom (f.naturality V.hom.op) _).symm

variable {ι : Type v} [Fintype ι]

/-- The universal matrix of a finite local family commutes with actual coefficient pullback. -/
theorem localSectionDeterminant_matrix_pullback (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : ι → End (M.over U)) (V : Over U) :
    (Langlands.Shimura.HodgeDeterminant.matrix (localSectionBasis e V)
        (fun i => localSectionEndomorphism M V (a i))).map
          (MvPolynomial.map (f.app V.left).hom) =
      Langlands.Shimura.HodgeDeterminant.matrix
        (localSectionBasis (chartFreePullbackIso f U e)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)))
        (fun i => localSectionEndomorphism ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom))
          (localHomPullback f U (a i))) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Langlands.Shimura.HodgeDeterminant.matrix,
    map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    localSectionEndomorphism_toMatrix_pullback f e, Matrix.map_apply]
  rfl

/-- The actual local determinant polynomial commutes with arbitrary scheme pullback. -/
theorem localSectionDeterminant_pullback (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : ι → End (M.over U)) (V : Over U) :
    MvPolynomial.map (f.app V.left).hom (localSectionDeterminant e a V) =
      localSectionDeterminant (chartFreePullbackIso f U e)
        (fun i => localHomPullback f U (a i))
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) := by
  unfold localSectionDeterminant Langlands.Shimura.HodgeDeterminant.polynomial
  rw [RingHom.map_det]
  exact congrArg Matrix.det (localSectionDeterminant_matrix_pullback f e a V)

/-- Each determinant coefficient pulls back as an actual structure-sheaf section. -/
theorem coeff_localSectionDeterminant_pullback (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (a : ι → End (M.over U)) (V : Over U) (d : ι →₀ ℕ) :
    f.app V.left ((localSectionDeterminant e a V).coeff d) =
      (localSectionDeterminant (chartFreePullbackIso f U e)
        (fun i => localHomPullback f U (a i))
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom))).coeff d := by
  rw [← localSectionDeterminant_pullback f e a V]
  exact (MvPolynomial.coeff_map (f.app V.left).hom (localSectionDeterminant e a V) d).symm

end Langlands.Scheme.Modules
